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
package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.Set;
import java.util.TreeSet;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants
                = ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars
                = ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode

        // for (Stmt stmt : ir) {
        //     if (stmt instanceof AssignStmt) {
        //         AssignStmt assignStmt = (AssignStmt) stmt;
        //         RValue rvalue = assignStmt.getRValue();
        //         SetFact<Var> liveOutFact = liveVars.getOutFact(stmt);
        //         if (assignStmt.getLValue() instanceof Var lvar) {
        //             if (!liveOutFact.contains(lvar) && hasNoSideEffect(rvalue)) {
        //                 deadCode.add(stmt);
        //             }
        //         }
        //     } else if (stmt instanceof If) {
        //         CPFact cpFact = constants.getOutFact(stmt);
        //         If ifStmt = (If) stmt;
        //         // Use constant propagation to evaluate the condition to a Value (1/0 when constant)
        //         Value condValue = ConstantPropagation.evaluate(ifStmt.getCondition(), cpFact);
        //         if (condValue.isConstant()) {
        //             deadCode.add(stmt);
        //             int cond = condValue.getConstant();
        //             for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
        //                 Stmt target = edge.getTarget();
        //                 // If condition is true (non-zero), the IF_FALSE edge is dead; if false (zero), the IF_TRUE edge is dead
        //                 if ((cond != 0 && edge.getKind() == Edge.Kind.IF_FALSE)
        //                         || (cond == 0 && edge.getKind() == Edge.Kind.IF_TRUE)) {
        //                     deadCode.add(target);
        //                 }
        //             }
        //         }
        //     } else if (stmt instanceof SwitchStmt) {
        //         CPFact cpFact = constants.getOutFact(stmt);
        //         SwitchStmt switchStmt = (SwitchStmt) stmt;
        //         // Evaluate the switch key (variable) to a Value
        //         Value keyValue = ConstantPropagation.evaluate(switchStmt.getVar(), cpFact);
        //         if (keyValue.isConstant()) {
        //             deadCode.add(stmt);
        //             int keyConst = keyValue.getConstant();
        //             for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
        //                 Stmt target = edge.getTarget();
        //                 // Mark non-matching case targets as dead; keep default as is (following original logic)
        //                 if (edge.getKind() == Edge.Kind.SWITCH_CASE && edge.getCaseValue() != keyConst) {
        //                     deadCode.add(target);
        //                 }
        //             }
        //         }
        //     }
        // }
        // return deadCode;
        // First, find all reachable nodes to handle control-flow based dead code
        Set<Stmt> reachableStmts = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        java.util.Queue<Stmt> worklist = new java.util.LinkedList<>();
        worklist.add(cfg.getEntry());
        reachableStmts.add(cfg.getEntry());

        while (!worklist.isEmpty()) {
            Stmt curr = worklist.poll(); // current statement being processed

            if (curr instanceof If) {
                If ifStmt = (If) curr;
                CPFact inFact = constants.getInFact(curr);
                Value condValue = ConstantPropagation.evaluate(ifStmt.getCondition(), inFact);

                if (condValue.isConstant()) {
                    boolean conditionTrue = condValue.getConstant() != 0;
                    Stmt trueTarget = ifStmt.getTarget();
                    for (Stmt succ : cfg.getSuccsOf(curr)) {
                        if ((conditionTrue && succ.equals(trueTarget)) || (!conditionTrue && !succ.equals(trueTarget))) {
                            if (reachableStmts.add(succ)) {
                                worklist.add(succ);
                            }
                        }
                    }
                    continue;
                }
            }

            if (curr instanceof SwitchStmt) {
                SwitchStmt switchStmt = (SwitchStmt) curr;
                CPFact inFact = constants.getInFact(curr);
                Value keyValue = ConstantPropagation.evaluate(switchStmt.getVar(), inFact);

                if (keyValue.isConstant()) {
                    int constKey = keyValue.getConstant();
                    Stmt target = null;
                    for (int i = 0; i < switchStmt.getCaseValues().size(); i++) {
                        if (switchStmt.getCaseValues().get(i) == constKey) {
                            target = switchStmt.getTarget(i);
                            break;
                        }
                    }
                    if (target == null) {
                        target = switchStmt.getDefaultTarget();
                    }
                    if (target != null && reachableStmts.add(target)) {
                        worklist.add(target);
                    }
                    continue;
                }
            }

            for (Stmt succ : cfg.getSuccsOf(curr)) {
                if (reachableStmts.add(succ)) {
                    worklist.add(succ);
                }
            }
        }

        for (Stmt stmt : ir) {
            if (!reachableStmts.contains(stmt)) {
                deadCode.add(stmt);
            }
        }

        for (Stmt stmt : reachableStmts) { // detect dead assignments among the reachable statements
            if (stmt instanceof AssignStmt) {
                AssignStmt<?, ?> assignStmt = (AssignStmt<?, ?>) stmt;
                if (assignStmt.getLValue() instanceof Var) {
                    Var lVar = (Var) assignStmt.getLValue();
                    if (!liveVars.getOutFact(stmt).contains(lVar) && hasNoSideEffect(assignStmt.getRValue())) {
                        deadCode.add(stmt);
                    }
                }
            }
        }

        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp
                || // cast may trigger ClassCastException
                rvalue instanceof CastExp
                || // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess
                || // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
