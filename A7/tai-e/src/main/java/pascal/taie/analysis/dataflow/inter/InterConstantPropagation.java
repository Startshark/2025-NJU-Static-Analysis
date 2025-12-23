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

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Pair;

import java.util.*;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    // TODO - you can add more fields if necessary
    public static final Map<Obj, Set<Var>> aliasMap = new HashMap<>(); // Obj -> set of Vars
    public static final Map<Pair<?, ?>, Value> valueMap = new HashMap<>(); // (Obj, FieldRef)/(Obj, Value) -> Value
    public static final Map<Pair<JClass, FieldRef>, Set<LoadField>> staticloadFieldMap = new HashMap<>(); // (Class, FieldRef) -> set of LoadField
    public static PointerAnalysisResult pta;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);

        // TODO - You can do initialization work here
        pta.getVars().forEach(var
                -> pta.getPointsToSet(var).forEach(obj
                        -> aliasMap.computeIfAbsent(obj, k -> new HashSet<>()).add(var)
                )
        ); // This part is optimized by GPT

        icfg.getNodes().stream()
                .filter(stmt -> stmt instanceof LoadField)
                .map(stmt -> (LoadField) stmt)
                .filter(load -> load.getFieldAccess() instanceof StaticFieldAccess)
                .forEach(load -> {
                    StaticFieldAccess access = (StaticFieldAccess) load.getFieldAccess();
                    FieldRef ref = access.getFieldRef();
                    staticloadFieldMap.computeIfAbsent(
                            new Pair<>(ref.getDeclaringClass(), ref),
                            k -> new HashSet<>()
                    ).add(load);
                });
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        boolean changed = false;

        // Remove keys not in in
        List<Var> toRemove = new ArrayList<>();
        for (Var var : out.keySet()) {
            if (in.get(var) == null) {
                toRemove.add(var);
            }
        }
        for (Var var : toRemove) {
            out.remove(var);
            changed = true;
        }

        for (Var var : in.keySet()) {
            if (out.update(var, in.get(var))) {
                changed = true;
            }
        }
        return changed;
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        boolean changed = cp.transferNode(stmt, in, out);

        if (stmt instanceof LoadField || stmt instanceof LoadArray) {
            LValue lVal = ((DefinitionStmt) stmt).getLValue();
            if (lVal instanceof Var && ConstantPropagation.canHoldInt((Var) lVal)) {
                Var lValue = (Var) lVal;
                Value resultValue = Value.getUndef();

                if (stmt instanceof LoadField) {
                    resultValue = handleLoadField((LoadField) stmt);
                } else {
                    resultValue = handleLoadArray((LoadArray) stmt, in);
                }

                if (out.update(lValue, resultValue)) {
                    changed = true;
                }
            }
        }
        return changed;
    }

    private Value handleLoadField(LoadField load) {
        Value res = Value.getUndef();
        if (load.getFieldAccess() instanceof InstanceFieldAccess access) {
            for (Obj obj : pta.getPointsToSet(access.getBase())) {
                Value val = valueMap.get(new Pair<>(obj, access.getFieldRef()));
                if (val == null) {
                    val = Value.getUndef();
                }
                res = cp.meetValue(res, val);
            }
        } else if (load.getFieldAccess() instanceof StaticFieldAccess access) {
            Value val = valueMap.get(new Pair<>(access.getFieldRef().getDeclaringClass(), access.getFieldRef()));
            if (val == null) {
                val = Value.getUndef();
            }
            res = cp.meetValue(res, val);
        }
        return res;
    }

    private Value handleLoadArray(LoadArray load, CPFact in) {
        Value res = Value.getUndef();
        ArrayAccess access = load.getArrayAccess();
        Value indexVal = ConstantPropagation.evaluate(access.getIndex(), in);

        if (!indexVal.isUndef()) {
            if (indexVal.isNAC()) {
                return Value.getNAC();
            }
            for (Obj obj : pta.getPointsToSet(access.getBase())) {
                Value val = valueMap.get(new Pair<>(obj, indexVal));
                if (val == null) {
                    val = Value.getUndef();
                }
                res = cp.meetValue(res, val);

                Value nacValue = valueMap.get(new Pair<>(obj, Value.getNAC()));
                if (nacValue != null) {
                    res = cp.meetValue(res, nacValue);
                }
            }
        }
        return res;
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        CPFact result = out.copy();
        Invoke invoke = (Invoke) edge.getSource();
        if (invoke.getLValue() != null) {
            result.remove(invoke.getLValue());
        }
        return result;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        CPFact entryFact = new CPFact();
        Invoke invoke = (Invoke) edge.getSource();
        List<Var> args = invoke.getRValue().getArgs();
        List<Var> params = edge.getCallee().getIR().getParams();

        for (int i = 0; i < args.size(); i++) {
            entryFact.update(params.get(i), callSiteOut.get(args.get(i)));
        }
        return entryFact;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact returnFact = new CPFact();
        Invoke invoke = (Invoke) edge.getCallSite();
        Var lValue = invoke.getLValue();

        if (lValue != null) {
            Value mergedValue = Value.getUndef();
            for (Var retVar : edge.getReturnVars()) {
                mergedValue = cp.meetValue(mergedValue, returnOut.get(retVar));
            }
            returnFact.update(lValue, mergedValue);
        }
        return returnFact;
    }
}
