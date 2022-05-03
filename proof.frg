#lang forge
// A node is a representation of a two dimensional region
// where its edges are the nodes which the node "touches"
// in its representation in 2D space.
sig Node {}

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

sig Coloring {
    nodeSet: set Node
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
    all e: g.edges | {
        #{n : Node | n in e.nodePair} = 2
    }
    // All edges in the graph must be reachable
    all e1, e2: g.edges | {
        reachable[e1, e2, nodePair, ~nodePair]
    }
    // No two edges have same nodePair
    all disj e1, e2: g.edges | {
        e1.nodePair != e2.nodePair
    }
    // All graph nodes are in its edges
    g.nodes in g.edges.nodePair         
}

pred wellformedMain[g: Graph] {
    wellformed[g]
    // All nodes and edges must be in the graph
    Node in g.nodes
    Edge in g.edges
}

// Predicate for checking all Coloring
// fields are valid. Since we are interested in
// generating coloring combinations for a graph,
// we want to make sure no two Colorings are the same.
pred wellformedColors {
    // No two colorings are the same   
    all disj c1, c2: Coloring | {
        c1.nodeSet != c2.nodeSet
    }
}

// Helper predicate to see if there is an edge 
// between two nodes in the graph
pred hasEdge[n1,n2: Node, g: Graph] {
    some e: g.edges | {
        n1 in e.nodePair
        n2 in e.nodePair
    }
}

// Predicate which takes in a graph and checks if
// the graph has a K33 subgraph
pred containsK33[g: Graph] {
    some disj v1, v2, v3, v4, v5, v6: g.nodes | {
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
pred isK5[g: Graph] {
    // all disj a, b: g.nodes | {
    //     hasEdge[a, b, g]
    // }
    some disj v1, v2, v3, v4, v5: g.nodes | {
        hasEdge[v1,v2,g]   
        hasEdge[v1,v3,g]
        hasEdge[v1,v4,g]
        hasEdge[v1,v5,g]
        hasEdge[v2,v3,g]
        hasEdge[v2,v4,g]
        hasEdge[v2,v5,g]
        hasEdge[v3,v4,g]
        hasEdge[v3,v5,g]
        hasEdge[v4,v5,g]  
    }
}

// Checks if subG is a subgraph of main.
pred isSubgraph[subG: Graph, main: Graph] {
    // g1's nodes are a subset of g2's
    subG.edges in main.edges    
    // The graph must be wellformed
    wellformed[subG]
}

// Checks if subD is a subdivision of main.
pred isSubdivision[subD: Graph, main: Graph] {
    wellformed[subD]
    // All nodes are present in main
    subD.nodes in main.nodes
    // All subdivision edges are either in the main,
    // or can be formed by joining two adjacent main edges
    all e: subD.edges | {
        e not in main.edges => {
            some disj e1, e2: main.edges | {
                e.nodePair = e1.nodePair - e2.nodePair
            }
        }
    }
}

// Predicate for ensuring that a graph is planar through Kuratowski's
// theorem.
pred isPlanar[g: Graph] {
    all subG: Graph | {
        (isSubgraph[subG, g] or isSubdivision[subG, g]) implies {
            not isK5[subG] and not containsK33[subG]         
        }
    }
}

pred canFourColor[g: Graph] {
    (some disj red, green, blue, yellow: Coloring | {
        g.nodes = ((red.nodeSet + green.nodeSet) + (yellow.nodeSet + blue.nodeSet))
        all e: g.edges | {        
            e.nodePair not in red.nodeSet
            e.nodePair not in green.nodeSet
            e.nodePair not in yellow.nodeSet
            e.nodePair not in blue.nodeSet
        }
    })
    // Added additional cases for graphs with <= 3 nodes
    or (some disj green, blue, yellow: Coloring | {
        g.nodes = ((green.nodeSet) + (yellow.nodeSet + blue.nodeSet))
        all e: g.edges | {        
            e.nodePair not in green.nodeSet
            e.nodePair not in yellow.nodeSet
            e.nodePair not in blue.nodeSet
        }
    })
    or (some disj blue, yellow: Coloring | {
        g.nodes = (yellow.nodeSet + blue.nodeSet)
        all e: g.edges | {        
            e.nodePair not in yellow.nodeSet
            e.nodePair not in blue.nodeSet
        }
    })
    or (one blue: Coloring | {
        g.nodes = (blue.nodeSet)
        all e: g.edges | {        
            e.nodePair not in blue.nodeSet
        }
    })
    or (
        no g.nodes
    )
}


// A graph containing only three nodes is four colorable
// example isFourColorable is {some g: Graph | wellformed[g] and canFourColor[g]} for {
//     Graph = `Graph0
//     nodes = `Graph0 -> `Node0 +
//             `Graph0 -> `Node1 +
//             `Graph0 -> `Node2
//     edges = `Graph0 -> `Edge0 +
//             `Graph0 -> `Edge1 +
//             `Graph0 -> `Edge2
//     nodePair = `Edge0 -> `Node0 +
//                `Edge0 -> `Node1 +
//                `Edge1 -> `Node1 +
//                `Edge1 -> `Node2 +
//                `Edge2 -> `Node2 +
//                `Edge2 -> `Node0
// }

// // Graph with four nodes which is four colorable
// example isFourColorable2 is {some g: Graph | wellformed[g] and canFourColor[g]} for {
//     nodes = `Graph0 -> `Node0 +
//             `Graph0 -> `Node1 +
//             `Graph0 -> `Node2 +
//             `Graph0 -> `Node3 
//     edges = `Graph0 -> `Edge0 +
//             `Graph0 -> `Edge1 +
//             `Graph0 -> `Edge2
//     nodePair = `Edge0 -> `Node0 +
//                `Edge0 -> `Node1 +
//                `Edge1 -> `Node1 +
//                `Edge1 -> `Node2 +
//                `Edge2 -> `Node2 +
//                `Edge2 -> `Node3
// }

// example isFourColorable3 is {some g: Graph | wellformed[g]} for {
//     #Int = 5
//     Edge = `Edge0 + `Edge1 +`Edge2 + `Edge3 + `Edge4
//     Node = `Node0 + `Node1 + `Node2 + `Node3 + `Node4 + `Node5
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
//             `Graph0 -> `Edge4
//     nodePair = `Edge0 -> `Node0 +
//                `Edge0 -> `Node1 +
//                `Edge1 -> `Node1 +
//                `Edge1 -> `Node2 +
//                `Edge2 -> `Node2 +
//                `Edge2 -> `Node3 +
//                `Edge3 -> `Node3 +
//                `Edge3 -> `Node4 +
//                `Edge4 -> `Node4 +
//                `Edge4 -> `Node5
// }

pred sanity { 
    wellformedColors
    some g: Graph {
        wellformedMain[g]    
        canFourColor[g]          
    }
}

pred planar {
    wellformedColors
    some g: Graph {
        wellformedMain[g]
        isPlanar[g]
        // not canFourColor[g] => produce unsat :)
        // canFourColor[g]
    }
}

// Run statement should work -- works with wellformed alone,
// is unsat otherwise

// run planar for exactly 1 Graph, 4 Node, exactly 16 Coloring

test expect {
    // A K5 graph cannot be 4 colored
    cannotFourColorK5: {some g: Graph | wellformed[g] and isK5[g] and canFourColor[g]} 
    for exactly 1 Graph, 5 Int, exactly 5 Node, 10 Edge is unsat

    // A K3,3 graph can be 4 colored (color one side one color and the other side another color)
    canFourColorK33: {some g: Graph | wellformed[g] and containsK33[g] and canFourColor[g]}
    for exactly 1 Graph, 5 Int, exactly 6 Node, 9 Edge is sat

    // fourColor4Node: {some g: Graph | planar => canFourColor[g]} for exactly 1 Graph, 4 Node, 
    // exactly 16 Coloring is theorem

    // fourColor5Node: {some g: Graph | planar => canFourColor[g]} for exactly 1 Graph, 5 Node, 
    // exactly 32 Coloring is theorem

    fourColor6Node: {some g: Graph | planar => canFourColor[g]} for exactly 1 Graph, 6 Node, 
    exactly 64 Coloring is theorem
}