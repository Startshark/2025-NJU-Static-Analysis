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
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import java.util.*;
import pascal.taie.language.type.Type;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
            ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    /**
     * Append the pointer-pts(csObj) to workList to process.
     */
    public void addPtsToWL(Pointer p, PointsToSet pointsToSet) {
        workList.addEntry(p, pointsToSet);
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
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
        if (callGraph.addReachableMethod(csMethod)) {
            StmtProcessor processor = new StmtProcessor(csMethod);
            // Process New, Assign, static (LoadField, storeField, invoke) statements.
            csMethod.getMethod().getIR().getStmts().forEach(s -> s.accept(processor));
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
        @Override
        public Void visit(New stmt) {
            // the context of variables are always the context of the methods.
            CSVar lVar = csManager.getCSVar(context, stmt.getLValue());
            Obj heapObj = heapModel.getObj(stmt);
            // the context of the object need to be selected.
            Context heapContext = contextSelector.selectHeapContext(csMethod, heapObj);
            CSObj csHeapObj = csManager.getCSObj(heapContext, heapObj);
            workList.addEntry(lVar, PointsToSetFactory.make(csHeapObj));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            CSVar rhs = csManager.getCSVar(context, stmt.getRValue());
            CSVar lhs = csManager.getCSVar(context, stmt.getLValue());
            addPFGEdge(rhs, lhs);
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                StaticField field = csManager.getStaticField(stmt.getFieldRef().resolve());
                CSVar lhs = csManager.getCSVar(context, stmt.getLValue());
                addPFGEdge(field, lhs);
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                CSVar rhs = csManager.getCSVar(context, stmt.getRValue());
                StaticField field = csManager.getStaticField(stmt.getFieldRef().resolve());
                addPFGEdge(rhs, field);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod callee = resolveCallee(null, stmt);
                // select callee context
                Context calleeCtx = contextSelector.selectContext(
                        csManager.getCSCallSite(context, stmt), callee);
                addPFGInvokeEdgesAndCGEdge(CallKind.STATIC, context, stmt, calleeCtx, callee);
            }
            return null;
        }
    }

    private void addPFGInvokeEdgesAndCGEdge(CallKind kind, Context callerCtx, Invoke callSite,
            Context calleeCtx, JMethod callee
    ) {
        CSCallSite csSite = csManager.getCSCallSite(callerCtx, callSite);
        CSMethod csCallee = csManager.getCSMethod(calleeCtx, callee);

        Edge edge = new Edge(kind, csSite, csCallee);
        if (callGraph.addEdge(edge)) {
            addReachable(csCallee);
            linkArgsToParams(callerCtx, callSite, calleeCtx, callee);
            linkRetToAssignee(callerCtx, callSite, calleeCtx, callee);

            taintAnalysis.taintProcessCall(callerCtx, callSite, callee);
        }
    }

    private void linkArgsToParams(Context callerCtx, Invoke callSite,
            Context calleeCtx, JMethod callee
    ) {
        List<Var> arguments = callSite.getInvokeExp().getArgs();
        List<Var> parameters = callee.getIR().getParams();

        if (arguments.size() != parameters.size()) {
            throw new AnalysisException("the numbers of args and params do not match!");
        }

        java.util.stream.IntStream.range(0, arguments.size()).forEach(i -> {
            CSVar argVar = csManager.getCSVar(callerCtx, arguments.get(i));
            CSVar paramVar = csManager.getCSVar(calleeCtx, parameters.get(i));
            addPFGEdge(argVar, paramVar);
        });
    }

    private void linkRetToAssignee(Context callerCtx, Invoke callSite,
            Context calleeCtx, JMethod callee
    ) {
        Var lhs = callSite.getLValue();
        if (lhs != null) {
            callee.getIR().getReturnVars().forEach(retVar -> {
                CSVar src = csManager.getCSVar(calleeCtx, retVar);
                CSVar dest = csManager.getCSVar(callerCtx, lhs);
                addPFGEdge(src, dest);
            });
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)) {
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

            PointsToSet delta = propagate(ptr, pts);

            // taint analysis
            taintAnalysis.taintPropagate(ptr, delta);

            if (ptr instanceof CSVar csVar) {
                delta.forEach(obj -> {
                    if (isRegularObj(obj)) {
                        updateFieldEdges(csVar, obj);
                        processCall(csVar, obj);
                    }
                });
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors, returns the
     * difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet pts = pointer.getPointsToSet();
        PointsToSet delta = PointsToSetFactory.make();
        pointsToSet.forEach(obj -> {
            if (pts.addObject(obj)) {
                delta.addObject(obj);
            }
        });

        if (!delta.isEmpty()) {
            pointerFlowGraph.getSuccsOf(pointer).forEach(succ -> workList.addEntry(succ, delta));
        }

        return delta;
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
        Context callerCtx = recv.getContext();
        for (Invoke callSite : recv.getVar().getInvokes()) {
            JMethod callee = resolveCallee(recvObj, callSite);
            Context calleeCtx = contextSelector.selectContext(
                    csManager.getCSCallSite(callerCtx, callSite), recvObj, callee);
            // add (callee:this, recvObj) to WL
            CSVar thisVar = csManager.getCSVar(calleeCtx, callee.getIR().getThis());
            workList.addEntry(thisVar, PointsToSetFactory.make(recvObj));
            addPFGInvokeEdgesAndCGEdge(selectCallKind(callSite), callerCtx, callSite, calleeCtx,
                    callee);
        }
    }

    private CallKind selectCallKind(Invoke call) {
        if (call.isVirtual()) {
            return CallKind.VIRTUAL;
        }
        if (call.isInterface()) {
            return CallKind.INTERFACE;
        }
        if (call.isSpecial()) {
            return CallKind.SPECIAL;
        }
        if (call.isDynamic()) {
            return CallKind.DYNAMIC;
        }
        return CallKind.STATIC;
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param receiver the receiver object of the method call. If the callSite
     * is static, this parameter is ignored (i.e., can be null).
     * @param call the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj receiver, Invoke call) {
        Type t = receiver != null ? receiver.getObject().getType() : null;
        return CallGraphs.resolveCallee(t, call);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }

    private boolean isRegularObj(CSObj obj) {
        return !taintAnalysis.isTaintObj(obj);
    }

    private void updateFieldEdges(CSVar var, CSObj obj) {
        updateLoadFieldEdges(var, obj);
        updateStoreFieldEdges(var, obj);
        updateLoadArrayEdges(var, obj);
        updateStoreArrayEdges(var, obj);
    }

    private void updateLoadFieldEdges(CSVar var, CSObj obj) {
        Context ctx = var.getContext();
        var.getVar().getLoadFields().forEach(lf -> {
            InstanceField srcField = csManager.getInstanceField(obj, lf.getFieldRef().resolve());
            CSVar targetVar = csManager.getCSVar(ctx, lf.getLValue());
            addPFGEdge(srcField, targetVar);
        });
    }

    private void updateStoreFieldEdges(CSVar var, CSObj obj) {
        Context ctx = var.getContext();
        var.getVar().getStoreFields().forEach(sf -> {
            CSVar srcVar = csManager.getCSVar(ctx, sf.getRValue());
            InstanceField targetField = csManager.getInstanceField(obj, sf.getFieldRef().resolve());
            addPFGEdge(srcVar, targetField);
        });
    }

    private void updateLoadArrayEdges(CSVar var, CSObj obj) {
        List<LoadArray> laList = var.getVar().getLoadArrays();
        if (!laList.isEmpty()) {
            Context ctx = var.getContext();
            ArrayIndex arrayIdx = csManager.getArrayIndex(obj);
            laList.forEach(la -> {
                CSVar target = csManager.getCSVar(ctx, la.getLValue());
                addPFGEdge(arrayIdx, target);
            });
        }
    }

    private void updateStoreArrayEdges(CSVar var, CSObj obj) {
        List<StoreArray> saList = var.getVar().getStoreArrays();
        if (!saList.isEmpty()) {
            Context ctx = var.getContext();
            ArrayIndex arrayIdx = csManager.getArrayIndex(obj);
            saList.forEach(sa -> {
                CSVar source = csManager.getCSVar(ctx, sa.getRValue());
                addPFGEdge(source, arrayIdx);
            });
        }
    }

}
