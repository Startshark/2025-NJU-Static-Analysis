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

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.util.collection.SetQueue;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.ir.exp.LValue;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;

import java.util.ArrayDeque;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

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

    private void initialize() {
        for (Node n : icfg) {
            result.setInFact(n, analysis.newInitialFact());
            result.setOutFact(n, analysis.newInitialFact());
        }

        // set boundary facts
        for (Method m : icfg.entryMethods().toList()) {
            setBoundaryFacts(icfg.getEntryOf(m));
        }
    }

    private void setBoundaryFacts(Node n) {
        // 保持行为一致：分别构造 in/out 的边界 fact（避免共用同一实例）
        result.setInFact(n, analysis.newBoundaryFact(n));
        result.setOutFact(n, analysis.newBoundaryFact(n));
    }

    private void doSolve() {
        // 初始化工作列表，将所有节点加入
        workList = new LinkedList<>();
        workList.addAll(icfg.getNodes());

        while (!workList.isEmpty()) {
            Node current = workList.poll();

            Fact inFactOfCurrent = result.getInFact(current);
            Fact outFactOfCurrent = result.getOutFact(current);

            // 处理所有入边，合并前驱节点的 out fact 到当前节点的 in fact
            for (ICFGEdge<Node> inEdge : icfg.getInEdgesOf(current)) {
                Fact edgeFact = analysis.transferEdge(inEdge, result.getOutFact(inEdge.getSource()));
                analysis.meetInto(edgeFact, inFactOfCurrent);
            }

            boolean hasChanged = analysis.transferNode(current, inFactOfCurrent, outFactOfCurrent);

            if (hasChanged) {
                for (ICFGEdge<Node> outEdge : icfg.getOutEdgesOf(current)) {
                    workList.add(outEdge.getTarget());
                }
            }

            result.setInFact(current, inFactOfCurrent);
            result.setOutFact(current, outFactOfCurrent);
        }
    }
}
