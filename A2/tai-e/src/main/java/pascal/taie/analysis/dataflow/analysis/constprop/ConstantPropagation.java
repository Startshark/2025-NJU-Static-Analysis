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
package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        CPFact fact = new CPFact();
//        Stmt entry = cfg.getEntry();
        IR ir = cfg.getIR();
        for (Var v : ir.getParams()) {
            if (canHoldInt(v)) {
                fact.update(v, Value.getNAC());
            }
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (Var v : fact.keySet()) {
            Value v1 = fact.get(v);
            Value v2 = target.get(v);
            Value result = meetValue(v1, v2);
            // if (!result.equals(v2)) {
            target.update(v, result);
            // }
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }

        if (v1.isUndef()) {
            return v2;
        } else if (v2.isUndef()) {
            return v1;
        }

        if (v1.isConstant() && v2.isConstant()) {
            if (v1.equals(v2)) {
                return v1;
            } else {
                return Value.getNAC();
            }
        }

        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // out.copyFrom(in);
        // if (stmt instanceof DefinitionStmt) {
        //     DefinitionStmt def = (DefinitionStmt) stmt;
        //     LValue left = def.getLValue();
        //     Exp right = def.getRValue();
        //     if (left instanceof Var) {
        //         Var left_temp = (Var) left;
        //         if (canHoldInt(left_temp)) {
        //             Value value = evaluate(right, in);
        //             out.update(left_temp, value);
        //             return true;
        //         } else {
        //             out.remove(left_temp);
        //             return true;
        //         }
        //     }
        // }
        // return false;
        CPFact tempFact = in.copy();
        if (stmt instanceof DefinitionStmt def) {
            LValue left = def.getLValue();
            Exp right = def.getRValue();
            if (left instanceof Var leftVar) {
                if (canHoldInt(leftVar)) {
                    Value value = evaluate(right, in);
                    tempFact.update(leftVar, value);
                } else {
                    tempFact.remove(leftVar);
                }
            }
        }
        return out.copyFrom(tempFact);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise
     * false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof Var) {
            return in.get((Var) exp);
        }

        if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }

        if (exp instanceof BinaryExp biExp) {
            Var lVar = biExp.getOperand1();
            Var rVar = biExp.getOperand2();

            Value l = in.get(lVar);
            Value r = in.get(rVar);

//            if (!l.isConstant() || !r.isConstant()) {
//                return  Value.getNAC();
//            }
            if (l.isNAC() || r.isNAC()) {
                if (exp instanceof ArithmeticExp arExp) {
                    ArithmeticExp.Op op = arExp.getOperator();
                    if (l.isNAC() && r.isConstant()) {
                        if (r.getConstant() == 0 && (op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM)) {
                            return Value.getUndef();
                        }
                    }
                }
                return Value.getNAC();
            }

//            if (l.isNAC() || r.isNAC()) {
//                这里NAC / 0, NAC % 0 都应该为UNDEF！！!
//                if (exp instanceof ArithmeticExp arExp) {
//                    ArithmeticExp.Op op = arExp.getOperator();
//                    if (l.isNAC() && r.isConstant()) {
//                        if (r.getConstant() == 0 && (op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM)) {
//                            return Value.getUndef();
//                        }
//                    }
//                }
//                return Value.getNAC();
//            }
            if (!l.isConstant() || !r.isConstant()) {
                return Value.getUndef();
            }
            int a = l.getConstant();
            int b = r.getConstant();
            int res = -1; // 希望没有bug

            if (exp instanceof ArithmeticExp arExp) {
                ArithmeticExp.Op op = arExp.getOperator();
                switch (op) {
                    case ADD:
                        res = a + b;
                        break;
                    case SUB:
                        res = a - b;
                        break;
                    case MUL:
                        res = a * b;
                        break;
                    case DIV:
                        if (b == 0) {
                            return Value.getUndef();

                        }
                        res = a / b;
                        break;
                    case REM:
                        if (b == 0) {
                            return Value.getUndef();

                        }
                        res = a % b;
                        break;
                }
            } else if (exp instanceof ConditionExp conditionExp) {
                ConditionExp.Op op = conditionExp.getOperator();
                res = switch (op) {
                    case EQ ->
                        (a == b) ? 1 : 0;
                    case NE ->
                        (a != b) ? 1 : 0;
                    case LT ->
                        (a < b) ? 1 : 0;
                    case GT ->
                        (a > b) ? 1 : 0;
                    case LE ->
                        (a <= b) ? 1 : 0;
                    case GE ->
                        (a >= b) ? 1 : 0;
                };
            } else if (exp instanceof BitwiseExp bitwiseExp) {
                BitwiseExp.Op op = bitwiseExp.getOperator();
                res = switch (op) {
                    case AND ->
                        a & b;
                    case OR ->
                        a | b;
                    case XOR ->
                        a ^ b;
                };
            } else if (exp instanceof ShiftExp shiftExp) {
                ShiftExp.Op op = shiftExp.getOperator();
                res = switch (op) {
                    case SHL ->
                        a << b;
                    case SHR ->
                        a >> b;
                    case USHR ->
                        a >>> b;
                };
            } else {
                // I shouldn't be here.
                throw new RuntimeException("Unknown exp type: " + exp.getClass());
            }
            return Value.makeConstant(res);
        }

        return Value.getNAC();
    }
}
