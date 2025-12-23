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
package pascal.taie.analysis.pta.cs;

import java.util.Set;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
            ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if (!callGraph.contains(csMethod)) {
            callGraph.addReachableMethod(csMethod);
            StmtProcessor processor = new StmtProcessor(csMethod);
            for (pascal.taie.ir.stmt.Stmt stmt : csMethod.getMethod().getIR()) {
                stmt.accept(processor);
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) { // static invocation
                JMethod callee = resolveCallee(null, stmt);
                CSCallSite callSite = csManager.getCSCallSite(context, stmt);
                Context calleeContext = contextSelector.selectContext(callSite, callee);
                CSMethod calleeMethod = csManager.getCSMethod(calleeContext, callee);

                Edge<CSCallSite, CSMethod> newEdge = new Edge<>(CallKind.STATIC, callSite, calleeMethod);
                if (callGraph.addEdge(newEdge)) {
                    addReachable(calleeMethod);

                    int paramCount = callee.getParamCount();
                    for (int i = 0; i < paramCount; i++) {
                        CSVar argument = csManager.getCSVar(context, stmt.getRValue().getArg(i));
                        CSVar parameter = csManager.getCSVar(calleeContext, callee.getIR().getParam(i));
                        addPFGEdge(argument, parameter);
                    }

                    Var lhs = stmt.getLValue();
                    if (lhs != null) {
                        CSVar targetVar = csManager.getCSVar(context, lhs);
                        for (Var retVar : callee.getIR().getReturnVars()) {
                            CSVar sourceRet = csManager.getCSVar(calleeContext, retVar);
                            addPFGEdge(sourceRet, targetVar);
                        }
                    }
                }
            }
            return null;
        }

        public Void visit(New stmt) {
            Var lhs = stmt.getLValue();
            CSVar target = csManager.getCSVar(context, lhs);
            Obj obj = heapModel.getObj(stmt);
            Context heapContext = contextSelector.selectHeapContext(csMethod, obj);
            CSObj csObj = csManager.getCSObj(heapContext, obj);
            workList.addEntry(target, PointsToSetFactory.make(csObj));
            return null;
        }

        public Void visit(Copy stmt) {
            CSVar source = csManager.getCSVar(context, stmt.getRValue());
            CSVar target = csManager.getCSVar(context, stmt.getLValue());
            addPFGEdge(source, target);
            return null;
        }

        public Void visit(StoreField stmt) {
            JField field = stmt.getFieldRef().resolve();
            if (field.isStatic()) {
                CSVar source = csManager.getCSVar(context, stmt.getRValue());
                StaticField target = csManager.getStaticField(field);
                addPFGEdge(source, target);
            }
            return null;
        }

        public Void visit(LoadField stmt) {
            JField field = stmt.getFieldRef().resolve();
            if (field.isStatic()) {
                StaticField source = csManager.getStaticField(field);
                CSVar target = csManager.getCSVar(context, stmt.getLValue());
                addPFGEdge(source, target);
            }
            return null;
        }

        public Void visit(StoreArray stmt) {
            return StmtVisitor.super.visit(stmt);
        }

        public Void visit(LoadArray stmt) {
            return StmtVisitor.super.visit(stmt);
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        boolean added = pointerFlowGraph.addEdge(source, target);
        if (added) {
            PointsToSet pts = source.getPointsToSet();
            if (!pts.isEmpty()) {
                workList.addEntry(target, pts);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer ptr = entry.pointer();
            PointsToSet pts = entry.pointsToSet();

            PointsToSet diff = propagate(ptr, pts);

            if (ptr instanceof CSVar) {
                CSVar csVar = (CSVar) ptr;
                Var var = csVar.getVar();
                Context ctx = csVar.getContext();

                for (CSObj obj : diff) {
                    for (StoreField stmt : var.getStoreFields()) {
                        CSVar rhs = csManager.getCSVar(ctx, stmt.getRValue());
                        JField field = stmt.getFieldRef().resolve();
                        InstanceField fieldObj = csManager.getInstanceField(obj, field);
                        addPFGEdge(rhs, fieldObj);
                    }

                    for (LoadField stmt : var.getLoadFields()) {
                        CSVar lhs = csManager.getCSVar(ctx, stmt.getLValue());
                        JField field = stmt.getFieldRef().resolve();
                        InstanceField fieldObj = csManager.getInstanceField(obj, field);
                        addPFGEdge(fieldObj, lhs);
                    }

                    for (StoreArray stmt : var.getStoreArrays()) {
                        CSVar rhs = csManager.getCSVar(ctx, stmt.getRValue());
                        ArrayIndex arrayIdx = csManager.getArrayIndex(obj);
                        addPFGEdge(rhs, arrayIdx);
                    }

                    for (LoadArray stmt : var.getLoadArrays()) {
                        CSVar lhs = csManager.getCSVar(ctx, stmt.getLValue());
                        ArrayIndex arrayIdx = csManager.getArrayIndex(obj);
                        addPFGEdge(arrayIdx, lhs);
                    }

                    processCall(csVar, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors, returns the
     * difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet diff = PointsToSetFactory.make();
        PointsToSet currentPts = pointer.getPointsToSet();

        for (CSObj obj : pointsToSet) {
            if (currentPts.addObject(obj)) {
                diff.addObject(obj);
            }
        }

        if (!diff.isEmpty()) {
            Set<Pointer> successors = pointerFlowGraph.getSuccsOf(pointer);
            for (Pointer succ : successors) {
                workList.addEntry(succ, diff);
            }
        }

        return diff;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable
     * changes.
     *
     * @param recv the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        for (Invoke invoke : recv.getVar().getInvokes()) {
            JMethod callee = resolveCallee(recvObj, invoke);
            if (callee == null) {
                continue;
            }

            CSCallSite callSite = csManager.getCSCallSite(recv.getContext(), invoke);
            Context calleeContext = contextSelector.selectContext(callSite, recvObj, callee);
            CSMethod calleeMethod = csManager.getCSMethod(calleeContext, callee);

            CSVar thisVar = csManager.getCSVar(calleeContext, callee.getIR().getThis());
            workList.addEntry(thisVar, PointsToSetFactory.make(recvObj));

            CallKind kind;
            if (invoke.isInterface()) {
                kind = CallKind.INTERFACE;
            } else if (invoke.isVirtual()) {
                kind = CallKind.VIRTUAL;
            } else if (invoke.isSpecial()) {
                kind = CallKind.SPECIAL;
            } else {
                kind = CallKind.DYNAMIC;
            }

            Edge<CSCallSite, CSMethod> newEdge = new Edge<>(kind, callSite, calleeMethod);

            if (callGraph.addEdge(newEdge)) {
                addReachable(calleeMethod);

                int paramCount = callee.getParamCount();
                for (int i = 0; i < paramCount; i++) {
                    CSVar argument = csManager.getCSVar(recv.getContext(), invoke.getRValue().getArg(i));
                    CSVar parameter = csManager.getCSVar(calleeContext, callee.getIR().getParam(i));
                    addPFGEdge(argument, parameter);
                }

                Var lhs = invoke.getLValue();
                if (lhs != null) {
                    CSVar targetVar = csManager.getCSVar(recv.getContext(), lhs);
                    for (Var retVar : callee.getIR().getReturnVars()) {
                        CSVar sourceRet = csManager.getCSVar(calleeContext, retVar);
                        addPFGEdge(sourceRet, targetVar);
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite is
     * static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
