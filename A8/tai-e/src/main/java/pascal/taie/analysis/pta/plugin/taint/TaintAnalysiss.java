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
package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

// TODO - finish me
public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    private final TaintConfigProcessor configProc;
    private final TaintAnalysisSolver taintSolver;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);

        // TODO - finish me
        configProc = new TaintConfigProcessor(config);
        taintSolver = new TaintAnalysisSolver();
    }

    public void taintProcessCall(Context callerContext, Invoke callSite, JMethod callee) {
        taintSolver.processSource(callerContext, callSite, callee);
        taintSolver.buildTaintFlowGraph(callerContext, callSite, callee);
    }

    public boolean isTaintObj(CSObj obj) {
        return manager.isTaint(obj.getObject()) && obj.getContext().equals(emptyContext);
    }

    public void taintPropagate(Pointer pointer, PointsToSet delta) {
        taintSolver.taintPropagateToTaintSuccs(pointer, delta);
    }

    // TODO - finish me
    public void onFinish() {
        Set<TaintFlow> flows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), flows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> flows = new TreeSet<>();
        PointerAnalysisResult ptaResult = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        analyzeResult(flows, ptaResult);

        return flows;
    }

    /**
     * Analyze the pointer analysis result and find the taint flows.
     */
    private void analyzeResult(Set<TaintFlow> flows, PointerAnalysisResult ptaResult) {
        ptaResult.getCallGraph().edges().forEach(
                e -> analyzeInvoke(e.getCallSite(), e.getCallee(), flows, ptaResult)
        );
    }

    /**
     * Analyze one invoke → callee and find the taint flows.
     */
    private void analyzeInvoke(
            Invoke callSite, JMethod callee, Set<TaintFlow> flows, PointerAnalysisResult ptaResult
    ) {
        configProc.getSinks(callee).forEach(sink -> {
            Var arg = callSite.getInvokeExp().getArgs().get(sink.index());
            ptaResult.getPointsToSet(arg).forEach(obj -> {
                if (manager.isTaint(obj)) {
                    flows.add(new TaintFlow(manager.getSourceCall(obj), callSite, sink.index()));
                }
            });
        });
    }

    /**
     * Cache the map of TaintConfig
     */
    private static class TaintConfigProcessor {

        private final Map<JMethod, Set<Source>> sources;
        private final Map<JMethod, Set<Sink>> sinks;
        private final Map<JMethod, Set<TaintTransfer>> transfers;

        TaintConfigProcessor(TaintConfig config) {
            sources = groupItems(config.getSources(), Source::method);
            sinks = groupItems(config.getSinks(), Sink::method);
            transfers = groupItems(config.getTransfers(), TaintTransfer::method);
        }

        private <K, V> Map<K, Set<V>> groupItems(Set<V> items, Function<V, K> classifier) {
            return items.stream().collect(Collectors.groupingBy(classifier, Collectors.toSet()));
        }

        Set<Source> getSources(JMethod method) {
            return sources.getOrDefault(method, Set.of());
        }

        Set<Sink> getSinks(JMethod method) {
            return sinks.getOrDefault(method, Set.of());
        }

        Set<TaintTransfer> getTaintTransfers(JMethod method) {
            return transfers.getOrDefault(method, Set.of());
        }
    }

    /**
     * Represents taint flow graph in context-sensitive pointer analysis.
     */
    private static class TaintFlowGraph {

        private final MultiMap<Pointer, TaintTargetPointer> adj = Maps.newMultiMap();

        boolean addEdge(Pointer src, Pointer dest, Type type) {
            return adj.put(src, new TaintTargetPointer(dest, type));
        }

        Set<TaintTargetPointer> getSuccsOf(Pointer p) {
            return adj.get(p);
        }
    }

    private record TaintTargetPointer(Pointer pointer, Type typeOfTaintObj) {
    }

    private class TaintAnalysisSolver {

        private final TaintFlowGraph tfg;

        TaintAnalysisSolver() {
            tfg = new TaintFlowGraph();
        }

        void processSource(Context callerCtx, Invoke callSite, JMethod callee) {
            Var lhs = callSite.getLValue();
            if (lhs != null) {
                PointsToSet taints = PointsToSetFactory.make();
                configProc.getSources(callee).forEach(src -> {
                    Obj taintObj = manager.makeTaint(callSite, src.type());
                    taints.addObject(csManager.getCSObj(emptyContext, taintObj));
                });
                if (!taints.isEmpty()) {
                    solver.addPtsToWL(csManager.getCSVar(callerCtx, lhs), taints);
                }
            }
        }

        void buildTaintFlowGraph(Context callerCtx, Invoke callSite, JMethod callee) {
            configProc.getTaintTransfers(callee).forEach(transfer -> {
                Var fromVar = getSpecificVar(transfer.from(), callSite);
                Var toVar = getSpecificVar(transfer.to(), callSite);
                if (fromVar != null && toVar != null) {
                    addTFGEdge(csManager.getCSVar(callerCtx, fromVar),
                            csManager.getCSVar(callerCtx, toVar),
                            transfer.type());
                }
            });
        }

        private Var getSpecificVar(int loc, Invoke call) {
            InvokeExp invokeExp = call.getInvokeExp();
            if (loc == TaintTransfer.BASE) {
                return getBaseVarOf(invokeExp);
            }
            if (loc == TaintTransfer.RESULT) {
                return call.getResult();
            }
            return invokeExp.getArg(loc);
        }

        private Var getBaseVarOf(InvokeExp invokeExp) {
            return invokeExp instanceof InvokeInstanceExp instanceExp ? instanceExp.getBase() : null;
        }

        private void addTFGEdge(Pointer source, Pointer target, Type type) {
            if (tfg.addEdge(source, target, type)) {
                PointsToSet taints = getTaintObjOf(source.getPointsToSet());
                if (!taints.isEmpty()) {
                    solver.addPtsToWL(target, changeTaintType(taints, type));
                }
            }
        }

        void taintPropagateToTaintSuccs(Pointer pointer, PointsToSet pts) {
            PointsToSet taints = getTaintObjOf(pts);
            if (!taints.isEmpty()) {
                tfg.getSuccsOf(pointer).forEach(target -> {
                    solver.addPtsToWL(target.pointer(), changeTaintType(taints, target.typeOfTaintObj()));
                });
            }
        }

        private PointsToSet changeTaintType(PointsToSet pts, Type type) {
            PointsToSet result = PointsToSetFactory.make();
            pts.forEach(obj -> {
                Obj newTaint = manager.makeTaint(manager.getSourceCall(obj.getObject()), type);
                result.addObject(csManager.getCSObj(emptyContext, newTaint));
            });
            return result;
        }

        private PointsToSet getTaintObjOf(PointsToSet pts) {
            PointsToSet result = PointsToSetFactory.make();
            pts.forEach(obj -> {
                if (isTaintObj(obj)) {
                    result.addObject(obj);
                }
            });
            return result;
        }
    }
}
