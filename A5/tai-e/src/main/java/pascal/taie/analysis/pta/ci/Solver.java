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
package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;
import pascal.taie.language.classes.JField;

import java.util.List;
import java.util.Set;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        if (!callGraph.contains(method)) {
            callGraph.addReachableMethod(method);
            for (pascal.taie.ir.stmt.Stmt s : method.getIR()) {
                s.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod callee = resolveCallee(null, stmt);
                Edge<Invoke, JMethod> staticEdge = new Edge<>(CallKind.STATIC, stmt, callee);
                if (callGraph.addEdge(staticEdge)) {
                    addReachable(callee);
                    passArguments(stmt, callee);
                    passReturnValues(stmt, callee);
                }
            }
            return null;
        }

        public Void visit(New stmt) {
            Obj newObj = heapModel.getObj(stmt);
            VarPtr lhs = pointerFlowGraph.getVarPtr(stmt.getLValue());
            workList.addEntry(lhs, new PointsToSet(newObj));
            return null;
        }

        public Void visit(Copy stmt) {
            Pointer from = pointerFlowGraph.getVarPtr(stmt.getRValue());
            Pointer to = pointerFlowGraph.getVarPtr(stmt.getLValue());
            addPFGEdge(from, to);
            return null;
        }

        public Void visit(StoreField stmt) {
            JField f = stmt.getFieldRef().resolve();
            if (f.isStatic()) {
                Pointer from = pointerFlowGraph.getVarPtr(stmt.getRValue());
                Pointer to = pointerFlowGraph.getStaticField(f);
                addPFGEdge(from, to);
            }
            return null;
        }

        public Void visit(LoadField stmt) {
            JField f = stmt.getFieldRef().resolve();
            if (f.isStatic()) {
                Pointer from = pointerFlowGraph.getStaticField(f);
                Pointer to = pointerFlowGraph.getVarPtr(stmt.getLValue());
                addPFGEdge(from, to);
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

    private void passArguments(Invoke stmt, JMethod callee) {
        int paramCount = callee.getParamCount();
        for (int i = 0; i < paramCount; i++) {
            Var arg = stmt.getRValue().getArg(i);
            Var param = callee.getIR().getParam(i);
            addPFGEdge(pointerFlowGraph.getVarPtr(arg), pointerFlowGraph.getVarPtr(param));
        }
    }

    private void passReturnValues(Invoke stmt, JMethod callee) {
        Var lhs = stmt.getLValue();
        if (lhs != null) {
            callee.getIR().getReturnVars().forEach(ret
                    -> addPFGEdge(pointerFlowGraph.getVarPtr(ret), pointerFlowGraph.getVarPtr(lhs))
            );
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        boolean isAdded = pointerFlowGraph.addEdge(source, target);
        if (isAdded && !source.getPointsToSet().isEmpty()) {
            workList.addEntry(target, source.getPointsToSet());
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer ptr = entry.pointer();
            PointsToSet pts = entry.pointsToSet();

            PointsToSet diff = propagate(ptr, pts);

            if (ptr instanceof VarPtr) {
                VarPtr vPtr = (VarPtr) ptr;
                processInstanceOperations(vPtr.getVar(), diff);
            }
        }
    }

    private void processInstanceOperations(Var var, PointsToSet diff) {
        diff.forEach(obj -> {
            for (StoreField s : var.getStoreFields()) {
                VarPtr r = pointerFlowGraph.getVarPtr(s.getRValue());
                JField f = s.getFieldRef().resolve();
                addPFGEdge(r, pointerFlowGraph.getInstanceField(obj, f));
            }
            for (LoadField l : var.getLoadFields()) {
                VarPtr lVal = pointerFlowGraph.getVarPtr(l.getLValue());
                JField f = l.getFieldRef().resolve();
                addPFGEdge(pointerFlowGraph.getInstanceField(obj, f), lVal);
            }
            for (StoreArray sa : var.getStoreArrays()) {
                VarPtr r = pointerFlowGraph.getVarPtr(sa.getRValue());
                ArrayIndex ai = pointerFlowGraph.getArrayIndex(obj);
                addPFGEdge(r, ai);
            }
            for (LoadArray la : var.getLoadArrays()) {
                VarPtr lVal = pointerFlowGraph.getVarPtr(la.getLValue());
                ArrayIndex ai = pointerFlowGraph.getArrayIndex(obj);
                addPFGEdge(ai, lVal);
            }
            processCall(var, obj);
        });
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors, returns the
     * difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet diff = new PointsToSet();
        pointsToSet.forEach(obj -> {   // compute difference set
            if (!pointer.getPointsToSet().contains(obj)) {
                diff.addObject(obj);
            }
        });

        if (!diff.isEmpty()) {  // propagate the difference set
            diff.forEach(obj -> pointer.getPointsToSet().addObject(obj));
            for (Pointer succ : pointerFlowGraph.getSuccsOf(pointer)) { // propagate to successors
                workList.addEntry(succ, diff);  // add to work-list
            }
        }
        return diff;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable
     * changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        for (Invoke invoke : var.getInvokes()) {
            JMethod callee = resolveCallee(recv, invoke);
            VarPtr thisPtr = pointerFlowGraph.getVarPtr(callee.getIR().getThis());
            workList.addEntry(thisPtr, new PointsToSet(recv));

            CallKind kind = null;
            if (invoke.isDynamic()) {
                kind = CallKind.DYNAMIC;
            } else if (invoke.isInterface()) {
                kind = CallKind.INTERFACE;
            } else if (invoke.isSpecial()) {
                kind = CallKind.SPECIAL;
            } else if (invoke.isVirtual()) {
                kind = CallKind.VIRTUAL;
            }

            if (kind != null) { // instance call
                Edge<Invoke, JMethod> edge = new Edge<>(kind, invoke, callee);
                if (callGraph.addEdge(edge)) {
                    addReachable(callee);
                    passArguments(invoke, callee);
                    passReturnValues(invoke, callee);
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
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
