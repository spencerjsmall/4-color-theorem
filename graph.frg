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

--------------------------------
// * Testing for wellformed * //
--------------------------------

// Test checking a basic K3 graph
example isWellformed is {some g: Graph | wellformed[g]} for {
    Graph = `Graph0
    nodes = `Graph0 -> `Node0 +
            `Graph0 -> `Node1 +
            `Graph0 -> `Node2
    edges = `Graph0 -> `Edge0 +
            `Graph0 -> `Edge1 +
            `Graph0 -> `Edge2
    nodePair = `Edge0 -> `Node0 +
               `Edge0 -> `Node1 +
               `Edge1 -> `Node1 +
               `Edge1 -> `Node2 +
               `Edge2 -> `Node2 +
               `Edge2 -> `Node0
}

// A wellformed K5 graph is sat
test expect {
    isWellFormedK5: {some g: Graph | wellformed[g] and mainGraph[g] and isK5[g]} 
    for exactly 1 Graph, 5 Int, exactly 5 Node, 10 Edge is sat

    isWellFormedK33: {some g: Graph | wellformed[g] and mainGraph[g] and containsK33[g]}
    for exactly 1 Graph, 5 Int, exactly 6 Node, 9 Edge is sat
}

// Case where a graph is not wellformed -- edge connects to three nodes
example isnotWellformed is not {some g: Graph | wellformed[g]} for {
    Graph = `Graph0
    nodes = `Graph0 -> `Node0 +
            `Graph0 -> `Node1 +
            `Graph0 -> `Node2
    edges = `Graph0 -> `Edge0 +
            `Graph0 -> `Edge1 +
            `Graph0 -> `Edge2
    nodePair = `Edge0 -> `Node0 +
               `Edge0 -> `Node1 +
               `Edge0 -> `Node2 +
               `Edge1 -> `Node1 +
               `Edge1 -> `Node2 +
               `Edge2 -> `Node2 +
               `Edge2 -> `Node0
}

// Case where a graph is not wellformed -- graph isn't fully connected
example isnotWellformed2 is not {some g: Graph | wellformed[g]} for {
    Graph = `Graph0
    nodes = `Graph0 -> `Node0 +
            `Graph0 -> `Node1 +
            `Graph0 -> `Node2 +
            `Graph0 -> `Node3
    edges = `Graph0 -> `Edge0 +
            `Graph0 -> `Edge1
    nodePair = `Edge0 -> `Node0 +
               `Edge0 -> `Node1 +
               `Edge1 -> `Node2 +
               `Edge1 -> `Node3
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
    all n: Node | {
        some e: Edge | {
            n in e.nodePair
        }
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

---------------------------------
// * Testing for containsK33 * //
---------------------------------

// example containsK33Test is {some g: Graph | containsK33[g]} for {
//     #Int = 5
//     #Edge = 10
//     Graph = `Graph0
//     nodes = `Graph0 -> `Node0 +
//             `Graph0 -> `Node1 +
//             `Graph0 -> `Node2 +
//             `Graph0 -> `Node3 +
//             `Graph0 -> `Node4 +
//             `Graph0 -> `Node5
//     edges = `Graph0 -> `Edge0 +
//             `Graph0 -> `Edge1 +
//             `Graph0 -> `Edge2 +
//             `Graph0 -> `Edge3 +
//             `Graph0 -> `Edge4 +
//             `Graph0 -> `Edge5 +
//             `Graph0 -> `Edge6 +
//             `Graph0 -> `Edge7 +
//             `Graph0 -> `Edge8
//     nodePair = `Edge0 -> `Node0 +
//                `Edge0 -> `Node3 +
//                `Edge1 -> `Node1 +
//                `Edge1 -> `Node3 +
//                `Edge2 -> `Node2 +
//                `Edge2 -> `Node3 +
//                `Edge3 -> `Node0 +
//                `Edge3 -> `Node4 +
//                `Edge4 -> `Node1 +
//                `Edge4 -> `Node4 +
//                `Edge5 -> `Node2 +
//                `Edge5 -> `Node4 +
//                `Edge6 -> `Node0 +
//                `Edge6 -> `Node5 +
//                `Edge7 -> `Node1 +
//                `Edge7 -> `Node5 +
//                `Edge8 -> `Node2 +
//                `Edge8 -> `Node5
// }

// Predicate which takes in a graph containing exactly 5 nodes and
// checks whether the graph is a K5 graph.
pred isK5[g: Graph] {
    all disj a, b: g.nodes | {
        hasEdge[a, b, g]
    }
}

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

pred canFourColor[g: Graph] {
    all e: Edge, n1,n2: Node | {
        n1 in e.nodePair and n2 in e.nodePair implies {
            n1.coloring != n2.coloring
        }
    }
}

test expect {
    cannotFourColorK5: {some g: Graph | wellformed[g] and mainGraph[g] and isK5[g] and canFourColor[g]} 
    for exactly 1 Graph, 5 Int, exactly 5 Node, 10 Edge is unsat

    cannotFourColorK33: {some g: Graph | wellformed[g] and mainGraph[g] and containsK33[g] and canFourColor[g]}
    for exactly 1 Graph, 5 Int, exactly 6 Node, 9 Edge is unsat
}

// run {
//     some g: Graph | {
//         wellformed[g]
//         mainGraph[g]
//         isK5[g]
//     }
// } for exactly 1 Graph, 5 Int, exactly 5 Node, 10 Edge

run {
    some g: Graph | {
        wellformed[g]
        mainGraph[g]
        // canFourColor[g]
        containsK33[g]
    }
} for exactly 1 Graph, 6 Int, exactly 6 Node, 9 Edge
