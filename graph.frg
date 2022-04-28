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

// pred mainGraph[g: Graph] {
//     Node in g.nodes
//     Edge in g.edges
//     Node in g.edges.nodePair
// }

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

// Test on the base definition of a K33 Graph:  
example containsK33Test is {some g: Graph | containsK33[g]} for {
    #Int = 5
    Edge = `Edge0 + `Edge1 +`Edge2 + `Edge3 + `Edge4 + `Edge5 + `Edge6 +
           `Edge7 + `Edge8
    Node = `Node0 + `Node1 + `Node2 + `Node3 + `Node4 + `Node5
    Graph = `Graph0
    nodes = `Graph0 -> `Node0 +
            `Graph0 -> `Node1 +
            `Graph0 -> `Node2 +
            `Graph0 -> `Node3 +
            `Graph0 -> `Node4 +
            `Graph0 -> `Node5
    edges = `Graph0 -> `Edge0 +
            `Graph0 -> `Edge1 +
            `Graph0 -> `Edge2 +
            `Graph0 -> `Edge3 +
            `Graph0 -> `Edge4 +
            `Graph0 -> `Edge5 +
            `Graph0 -> `Edge6 +
            `Graph0 -> `Edge7 +
            `Graph0 -> `Edge8
    nodePair = `Edge0 -> `Node0 +
               `Edge0 -> `Node3 +
               `Edge1 -> `Node1 +
               `Edge1 -> `Node3 +
               `Edge2 -> `Node2 +
               `Edge2 -> `Node3 +
               `Edge3 -> `Node0 +
               `Edge3 -> `Node4 +
               `Edge4 -> `Node1 +
               `Edge4 -> `Node4 +
               `Edge5 -> `Node2 +
               `Edge5 -> `Node4 +
               `Edge6 -> `Node0 +
               `Edge6 -> `Node5 +
               `Edge7 -> `Node1 +
               `Edge7 -> `Node5 +
               `Edge8 -> `Node2 +
               `Edge8 -> `Node5
}

// Test on a Graph containing a K33 subgraph
example containsK33Test2 is {some g: Graph | containsK33[g]} for {
    #Int = 5
    Edge = `Edge0 + `Edge1 +`Edge2 + `Edge3 + `Edge4 + `Edge5 + `Edge6 +
           `Edge7 + `Edge8 + `Edge9
    Node = `Node0 + `Node1 + `Node2 + `Node3 + `Node4 + `Node5 + `Node6
    Graph = `Graph0
    nodes = `Graph0 -> `Node0 +
            `Graph0 -> `Node1 +
            `Graph0 -> `Node2 +
            `Graph0 -> `Node3 +
            `Graph0 -> `Node4 +
            `Graph0 -> `Node5 +
            `Graph0 -> `Node6
    edges = `Graph0 -> `Edge0 +
            `Graph0 -> `Edge1 +
            `Graph0 -> `Edge2 +
            `Graph0 -> `Edge3 +
            `Graph0 -> `Edge4 +
            `Graph0 -> `Edge5 +
            `Graph0 -> `Edge6 +
            `Graph0 -> `Edge7 +
            `Graph0 -> `Edge8 +
            `Graph0 -> `Edge9
    nodePair = `Edge0 -> `Node0 +
               `Edge0 -> `Node3 +
               `Edge1 -> `Node1 +
               `Edge1 -> `Node3 +
               `Edge2 -> `Node2 +
               `Edge2 -> `Node3 +
               `Edge3 -> `Node0 +
               `Edge3 -> `Node4 +
               `Edge4 -> `Node1 +
               `Edge4 -> `Node4 +
               `Edge5 -> `Node2 +
               `Edge5 -> `Node4 +
               `Edge6 -> `Node0 +
               `Edge6 -> `Node5 +
               `Edge7 -> `Node1 +
               `Edge7 -> `Node5 +
               `Edge8 -> `Node2 +
               `Edge8 -> `Node5 +
               `Edge9 -> `Node0 +
               `Edge9 -> `Node6
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

---------------------------------
// * Testing for isK5 * //
---------------------------------

// Test on the base definition of a K5 Graph:  
example isK5Test is {some g: Graph | isK5[g]} for {
    #Int = 5
    Edge = `Edge0 + `Edge1 +`Edge2 + `Edge3 + `Edge4 + `Edge5 + `Edge6 +
           `Edge7 + `Edge8 + `Edge9
    Node = `Node0 + `Node1 + `Node2 + `Node3 + `Node4
    Graph = `Graph0
    nodes = `Graph0 -> `Node0 +
            `Graph0 -> `Node1 +
            `Graph0 -> `Node2 +
            `Graph0 -> `Node3 +
            `Graph0 -> `Node4
    edges = `Graph0 -> `Edge0 +
            `Graph0 -> `Edge1 +
            `Graph0 -> `Edge2 +
            `Graph0 -> `Edge3 +
            `Graph0 -> `Edge4 +
            `Graph0 -> `Edge5 +
            `Graph0 -> `Edge6 +
            `Graph0 -> `Edge7 +
            `Graph0 -> `Edge8 +
            `Graph0 -> `Edge9
    nodePair = `Edge0 -> `Node0 +
               `Edge0 -> `Node1 +
               `Edge1 -> `Node0 +
               `Edge1 -> `Node2 +
               `Edge2 -> `Node0 +
               `Edge2 -> `Node3 +
               `Edge3 -> `Node0 +
               `Edge3 -> `Node4 +
               `Edge4 -> `Node1 +
               `Edge4 -> `Node2 +
               `Edge5 -> `Node1 +
               `Edge5 -> `Node3 +
               `Edge6 -> `Node1 +
               `Edge6 -> `Node4 +
               `Edge7 -> `Node2 +
               `Edge7 -> `Node3 +
               `Edge8 -> `Node2 +
               `Edge8 -> `Node4 +
               `Edge9 -> `Node3 +
               `Edge9 -> `Node4
}

// Test on a graph that doesn't contain a K5 subgraph 
example notK5Test is {some g: Graph | not isK5[g]} for {
    #Int = 5
    Edge = `Edge0 + `Edge1 +`Edge2 + `Edge3 + `Edge4 + `Edge5 + `Edge6 +
           `Edge7
    Node = `Node0 + `Node1 + `Node2 + `Node3 + `Node4
    Graph = `Graph0
    nodes = `Graph0 -> `Node0 +
            `Graph0 -> `Node1 +
            `Graph0 -> `Node2 +
            `Graph0 -> `Node3 +
            `Graph0 -> `Node4
    edges = `Graph0 -> `Edge0 +
            `Graph0 -> `Edge1 +
            `Graph0 -> `Edge2 +
            `Graph0 -> `Edge3 +
            `Graph0 -> `Edge4 +
            `Graph0 -> `Edge5 +
            `Graph0 -> `Edge6 +
            `Graph0 -> `Edge7
    nodePair = `Edge0 -> `Node0 +
               `Edge0 -> `Node1 +
               `Edge1 -> `Node0 +
               `Edge1 -> `Node2 +
               `Edge2 -> `Node0 +
               `Edge2 -> `Node3 +
               `Edge3 -> `Node0 +
               `Edge3 -> `Node4 +
               `Edge4 -> `Node1 +
               `Edge4 -> `Node2 +
               `Edge5 -> `Node1 +
               `Edge5 -> `Node3 +
               `Edge6 -> `Node1 +
               `Edge6 -> `Node4 +
               `Edge7 -> `Node2 +
               `Edge7 -> `Node3
}

test expect {
    // A graph containing less than five nodes cannot have a K5 subgraph
    fourNodeNotK5: {some g: Graph | (#{g.nodes} < 5) and isK5[g]} 
    for exactly 1 Graph, 5 Int, 4 Node, 10 Edge is unsat
    // A graph containing 6 nodes and at least 14 edges is always K5
    // Why? -- A graph with 6 nodes can have up to (5 + 4 + 3 + 2 + 1) = 15
    // edges. A K6 graph always contains a K5 subgraph. If we remove 1 edges at random,
    // the other 5 nodes are still interconnected.
    mustBeK5: {all g: Graph | (#{g.nodes} = 6) and (#{g.edges} >= 14) and wellformed[g] => isK5[g]}
    for exactly 1 Graph, 6 Int, 6 Node, 15 Edge is theorem
    // Same as previous test with larger bounds, works but takes 1 or 2 minutes to run
    // mustBeK5Test2: {all g: Graph | (#{g.nodes} = 7) and (#{g.edges} >= 19) and wellformed[g] => isK5[g]}
    // for exactly 1 Graph, 6 Int, 7 Node, 21 Edge is theorem
}

// Predicate for ensuring that a graph is planar through Kuratowski's
// theorem.
// pred kuratowski[g: Graph] {
//     all subG: Graph | {
//         isSubgraph[subG, g] implies {
//             not isK5[subG] and not containsK33[subG]
//         }
//     }
// }

// Checks if g1 is a subgraph of g2
// pred isSubgraph[g1: Graph, g2: Graph] {
//     // g1's nodes are a subset of g2's
//     g1.nodes in g2.nodes
//     // The graph must be wellformed
//     wellformed[g1]
// }

// Predicate which takes in a graph and evaluates if it is four colorable
// pred canFourColor[g: Graph] {  
//     // No edge has nodes in the same color
//     all e: g.edges | {
//         all c: Color | {
//             e.nodePair not in c.nodes
//         }
//     }
// }

pred canFourColor[g: Graph] {
    some disj red, green, blue, yellow: set g.nodes | {
        g.nodes in ((red + green) + (yellow + blue))
        all e: g.edges | {        
            e.nodePair not in red
            e.nodePair not in green
            e.nodePair not in yellow
            e.nodePair not in blue
        }
    }
}


// A graph containing only three nodes is four colorable
example isFourColorable is {some g: Graph | wellformed[g] and mainGraph[g] and canFourColor[g]} for {
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

// Graph with four nodes which is four colorable
example isFourColorable2 is {some g: Graph | wellformed[g] and mainGraph[g] and canFourColor[g]} for {
    nodes = `Graph0 -> `Node0 +
            `Graph0 -> `Node1 +
            `Graph0 -> `Node2 +
            `Graph0 -> `Node3 
    edges = `Graph0 -> `Edge0 +
            `Graph0 -> `Edge1 +
            `Graph0 -> `Edge2
    nodePair = `Edge0 -> `Node0 +
               `Edge0 -> `Node1 +
               `Edge1 -> `Node1 +
               `Edge1 -> `Node2 +
               `Edge2 -> `Node2 +
               `Edge2 -> `Node3
}

test expect {
    // A K5 graph cannot be 4 colored
    cannotFourColorK5: {some g: Graph | wellformed[g] and isK5[g] and canFourColor[g]} 
    for exactly 1 Graph, 5 Int, exactly 5 Node, 10 Edge is unsat

    // A K3,3 graph can be 4 colored (color one side one color and the other side another color)
    canFourColorK33: {some g: Graph | wellformed[g] and containsK33[g] and canFourColor[g]}
    for exactly 1 Graph, 5 Int, exactly 6 Node, 9 Edge is sat

    // Want to show this!
    // isFourColorable: {all g: Graph | wellformed[g] and mainGraph[g] implies canFourColor[g]}
}

// Counterexample case to current definitions
// run {
//     one g: Graph | {wellformed[g] and mainGraph[g] implies not canFourColor[g]}
// }

// Run statement for producing a K5 graph.
// run {
//     some g: Graph | {
//         wellformed[g]
//         mainGraph[g]
//         isK5[g]
//     }
// } for exactly 1 Graph, 5 Int, exactly 5 Node, 10 Edge

test expect {
    all g: Graph | {
        (wellformed[g]
        mainGraph[g]        
        containsK33[g]) => {
            some disj red, green, blue, yellow: Color | {
                canFourColor[red,green,blue,yellow,g]
            }
        }
    } for exactly 6 Int, exactly 6 Node, 9 Edge is theorem
}


// Run statement for producing a K3,3 graph.
run {
    some g: Graph | {
        wellformed[g]
        mainGraph[g]
        // canFourColor[g]
        containsK33[g]
    }
} for exactly 1 Graph, 6 Int, exactly 6 Node, 9 Edge
