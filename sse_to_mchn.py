import typing
import types

kind = types.SimpleNamespace(
    loops=0,
    ifs=1,
    breaks=2,
)

Code = list[typing.Union[int, "Code"]]
Graph = list[list[int]]

code: list[Code] = [
    [kind.loops,
        [kind.ifs, [kind.breaks], []],
        [kind.ifs, [], []],
    ]
]

def codegen(code) -> Graph:
    graph: Graph = []
    loops: list[tuple[int, list[int]]] = []

    def make_block() -> int:
        graph.append([])
        return len(graph) - 1

    def visit(code) -> None:
        match code:
            case [kind.loops, *body]:
                loops.append((make_block(), []))
                for c in body: visit(c)
                base, braks = loops.pop()
                graph[-1].append(base)
                make_block()
                for b in braks: graph[b][0] = len(graph) - 1
            case [kind.ifs, then, else_]:
                frm = graph[-1]
                frm.append(make_block())
                visit(then)
                last_then = len(graph) - 1
                frm.append(make_block())
                visit(else_)
                last_else = len(graph) - 1
                join = make_block()
                graph[last_then].append(join)
                graph[last_else].append(join)
            case [kind.breaks]:
                loops[-1][1].append(len(graph) - 1)
            case []: return
            case val: raise Exception(f"wat {val}")
    for c in code: visit(c)
    return graph

def lgraph(graph) -> None:
    for n in graph: print(n)
    print()

graph = codegen(code)

lgraph(graph)

def make_ref_counts(graph: Graph) -> list[int]:
    ref_counts = [0] * len(graph)
    ref_counts[0] = 1
    for n in graph:
        for e in n:
            ref_counts[e] += 1
    return ref_counts


def build_dominators(graph: Graph) -> Graph:
    ref_counts = make_ref_counts(graph)
    brefs = [-1] * len(graph)
    brefs[0] = 0
    def dfs(node: int) -> None:
        for child in graph[node]:
            if brefs[child] != -1: return
            if ref_counts[child] > 1:
                cursor = node
                while len(graph[brefs[cursor]]) == 1:
                    cursor = brefs[cursor]
                brefs[child] = brefs[cursor]
            else: brefs[child] = node
            dfs(child)
    dfs(0)
    return typing.cast(Graph, brefs)

tgraph = [
    [2, 1],
    [5],
    [3],
    [4],
    [5],
    [],
]
lgraph(build_dominators(tgraph))

dominators = build_dominators(graph)

def make_block_order(graph: Graph) -> list[int]:
    order = []
    seen = [False] * len(graph)
    ref_counts = make_ref_counts(graph)

    def dfs(node: int) -> None:
        if seen[node]: return
        seen[node] = True
        order.append(node)

        for child in graph[node]:
            if dominators[child] != node and ref_counts[child] != 1:
                ref_counts[child] -= 1
                return
            dfs(child)
    dfs(0)

    return order

lgraph(make_block_order(graph))

def simplify(graph: Graph) -> Graph:
    ref_counts = make_ref_counts(graph)
    for n in graph:
        if not n: continue
        for i, e in enumerate(n):
            if ref_counts[e] == 1 and len(graph[e]) == 1:
                n[i] = graph[e][0]
                graph[e] = []
    return graph

graph = simplify(graph)
lgraph(graph)

lgraph(make_block_order(graph))
