#lang forge

abstract sig Color {}
sig Red extends Color {}
sig Green extends Color {}
sig Blue extends Color {}
sig Yellow extends Color {}

// A node is a representation of a two dimensional region
// where its edges are the nodes which the node "touches"
// in its representation in 2D space.
sig Node {
    coloring: one Color
    // edges: set Edge
}

// 
sig Edge {
    // Must be a set of two -- using a set to define bidirectionality
    nodePair: set Node
}

// A graph is a set of Nodes and a set of Edges
sig Graph {
    nodes: set Node,
    edges: set Edge
}

// Kuratowki's theorem:
// A graph is planar if and only if it does not contain a subgraph
// with a subdivision of K5 or K3,3.
// By extension -- we can generate planar graphs by ensuring that
// our graph does not contain K5 or K3,3
// Then, given a random planar graph, show that there is some configuration
// such that each node -> node pair is such that the nodes are not the
// same color.

pred wellformed[g: Graph] {
    // A node not having an edge to itself is implicitly implies when we contrain
    // nodes field to be length 2
    // All edges contain exactly two nodes
    all e: Edge | {
        #{n : Node | n in e.nodePair} = 2
    }

    // All edges in the graph must be reachable
    all e1, e2: g.edges | {
        reachable[e1, e2, nodePair, ~nodePair]
    }
}

// Helper predicate to see if there is an edge between two nodes in the graph
pred hasEdge[n1,n2: Node, g: Graph] {
    some e: g.edges | {
        n1 in e.nodePair
        n2 in e.nodePair
    }
}

pred mainGraph[g: Graph] {
    all n: Node | {
        n in g.nodes
    }
    all e: Edge | {
        e in g.edges
    }
}

// Predicate which takes in a graph and checks if
// the graph has a K33 subgraph
pred containsK33[g: Graph] {
    some disj v1, v2, v3, v4, v5, v6: g.nodes | {
        // Establishes that each of the graphs
        // halves (bipartite) are interconnected (3,3)
        hasEdge[v1,v4,g]
        hasEdge[v1,v5,g]
        hasEdge[v1,v6,g]
        hasEdge[v2,v4,g]
        hasEdge[v2,v5,g]
        hasEdge[v2,v6,g]
        hasEdge[v3,v4,g]
        hasEdge[v3,v5,g]
        hasEdge[v3,v6,g]     
    }
}

// Predicate which takes in a graph containing exactly 5 nodes and
// checks whether the graph is a K5 graph.
// pred isK5[g: Graph] {
//     all disj a, b: g.nodes | {
//         b in edges[a]
//         a in edges[b]
//     }
// }

// Predicate for ensuring that a graph is planar through Kuratowski's
// theorem.
// pred kuratowski[g: Graph] {
//     all subG: Graph | {
//         isSubgraph[subG, g] implies
//             not isK5[subG] and not containsK33[subG]
//     }
// }

// Checks if g1 is a subgraph of g2
// pred isSubgraph[g1: Graph, g2: Graph] {
//     // g1's nodes are a subset of g2's
//     g1.nodes in g2.nodes
//     // The graph must be wellformed
//     wellformed[g1]
// }

// run {
//     some g: Graph | {
//         wellformed[g]
//         isK5[g]
//     }
// } for exactly 1 Graph, 4 Int, exactly 5 Node

run {
    some g: Graph | {
        wellformed[g]
        mainGraph[g]
        containsK33[g]
    }
} for exactly 1 Graph, 6 Int, exactly 6 Node, 9 Edge
