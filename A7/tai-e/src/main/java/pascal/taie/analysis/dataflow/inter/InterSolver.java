/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */
package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.util.collection.Pair;
import pascal.taie.util.collection.SetQueue;

import java.util.Queue;
import java.util.Set;

import static pascal.taie.analysis.dataflow.inter.InterConstantPropagation.*;

/**
 * Solver for inter-procedural data-flow analysis. The workload of
 * inter-procedural analysis is heavy, thus we always adopt work-list algorithm
 * for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;
    private final ICFG<Method, Node> icfg;
    private DataflowResult<Node, Fact> result;
    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
            ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private Value meet(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        if (v1.isUndef()) {
            return v2;
        }
        if (v2.isUndef()) {
            return v1;
        }
        return v1.equals(v2) ? v1 : Value.getNAC();
    }

    private void initialize() {
        // TODO - finish me 
        for (Node node : icfg) {
            result.setInFact(node, analysis.newInitialFact());
            result.setOutFact(node, analysis.newInitialFact());
        }
        icfg.entryMethods().forEach(method -> {
            Node entry = icfg.getEntryOf(method);
            result.setInFact(entry, analysis.newBoundaryFact(entry));
        });
    }

    private void doSolve() {
        // TODO - finish me
        workList = new SetQueue<>();
        workList.addAll(icfg.getNodes());

        while (!workList.isEmpty()) {
            Node node = workList.poll();
            CPFact in = (CPFact) result.getInFact(node);
            CPFact out = (CPFact) result.getOutFact(node);

            for (ICFGEdge<Node> edge : icfg.getInEdgesOf(node)) {
                Fact edgeFact = analysis.transferEdge(edge, result.getOutFact(edge.getSource()));
                analysis.meetInto(edgeFact, (Fact) in);
            }

            handleSideEffects(node, in);

            if (analysis.transferNode(node, (Fact) in, (Fact) out)) {
                icfg.getOutEdgesOf(node).forEach(edge -> workList.offer(edge.getTarget()));
            }

            result.setInFact(node, (Fact) in);
            result.setOutFact(node, (Fact) out);
        }
    }

    private void handleSideEffects(Node node, CPFact inFact) {
        if (node instanceof StoreField storeField) {
            if (ConstantPropagation.canHoldInt(storeField.getRValue())) {
                handleStoreField(storeField, inFact);
            }
        } else if (node instanceof StoreArray storeArray) {
            if (ConstantPropagation.canHoldInt(storeArray.getRValue())) {
                handleStoreArray(storeArray, inFact);
            }
        }
    }

    private void handleStoreField(StoreField store, CPFact inFact) {
        Value val = ConstantPropagation.evaluate(store.getRValue(), inFact);
        if (store.getFieldAccess() instanceof InstanceFieldAccess access) {
            for (var obj : pta.getPointsToSet(access.getBase())) {
                updateGlobalValue(new Pair<>(obj, access.getFieldRef()), val, obj);
            }
        } else if (store.getFieldAccess() instanceof StaticFieldAccess access) {
            updateGlobalValue(new Pair<>(access.getFieldRef().getDeclaringClass(), access.getFieldRef()), val, null);
        }
    }

    private void handleStoreArray(StoreArray store, CPFact inFact) {
        Value val = ConstantPropagation.evaluate(store.getRValue(), inFact);
        Value index = ConstantPropagation.evaluate(store.getArrayAccess().getIndex(), inFact);

        if (!index.isUndef()) {
            for (var obj : pta.getPointsToSet(store.getArrayAccess().getBase())) {
                updateGlobalValue(new Pair<>(obj, index), val, obj);
            }
        }
    }

    private void updateGlobalValue(Pair<?, ?> key, Value newValue, Object contextObj) {
        Value oldValue = valueMap.getOrDefault(key, Value.getUndef());
        Value metValue = meet(oldValue, newValue);

        if (!metValue.equals(oldValue)) {
            valueMap.put(key, metValue);
            addDependentsToWorkList(key, contextObj);
        }
    }

    private void addDependentsToWorkList(Pair<?, ?> key, Object contextObj) {
        if (contextObj instanceof Obj obj) {
            Set<Var> aliases = aliasMap.get(obj);
            if (aliases != null) {
                for (Var var : aliases) {
                    if (key.second() instanceof FieldRef fieldRef) {
                        var.getLoadFields().stream()
                                .filter(load -> load.getFieldAccess().getFieldRef().equals(fieldRef))
                                .forEach(load -> workList.offer((Node) load));
                    } else {
                        var.getLoadArrays().forEach(load -> workList.offer((Node) load));
                    }
                }
            }
        } else {
            Set<LoadField> loads = staticloadFieldMap.get(key);
            if (loads != null) {
                loads.forEach(load -> workList.offer((Node) load));
            }
        }
    }
}
