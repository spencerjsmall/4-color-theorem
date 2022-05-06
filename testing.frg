#lang forge
open "proof.frg"

--------------------------------
// * Testing for wellformed * //
--------------------------------

// Test checking a basic K3 graph
example isWellformed is wellformed for {
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
    // Test case where the graph must be K5
    isWellFormedK5: {some g: Graph | wellformed implies containsK5} 
    for exactly 1 Graph, 5 Int, exactly 5 Node, exactly 10 Edge is theorem
    
    // Test case checking that a K33 graph is sound
    isWellFormedK33: {some g: Graph | wellformed implies containsK33}
    for exactly 1 Graph, 5 Int, exactly 6 Node, exactly 9 Edge is sat
}

// Case where a graph is not wellformed -- edge connects to three nodes
example isnotWellformed is not wellformed for {
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
example isnotWellformed2 is not wellformed for {
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

---------------------------------
// * Testing for containsK33 * //
---------------------------------

// Test on the base definition of a K33 Graph:  
example containsK33Test is containsK33 for {
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
example containsK33Test2 is {some g: Graph | containsK33} for {
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

---------------------------------
// * Testing for isK5 * //
---------------------------------

// Test on the base definition of a K5 Graph:  
example isK5Test is containsK5 for {
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
example notK5Test is not containsK5 for {
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
    fourNodeNotK5: {some g: Graph | (#{g.nodes} < 5) and containsK5} 
    for exactly 1 Graph, 5 Int, 4 Node, 10 Edge is unsat
    // A graph containing 6 nodes and at least 14 edges is always K5
    // Why? -- A graph with 6 nodes can have up to (5 + 4 + 3 + 2 + 1) = 15
    // edges. A K6 graph always contains a K5 subgraph. If we remove 1 edges at random,
    // the other 5 nodes are still interconnected.
    mustBeK5: {all g: Graph | (#{g.nodes} = 6) and (#{g.edges} >= 14) and wellformed => containsK5}
    for exactly 1 Graph, 6 Int, 6 Node, 15 Edge is theorem
    // Same as previous test with larger bounds, works but takes 1 or 2 minutes to run
    // mustBeK5Test2: {all g: Graph | (#{g.nodes} = 7) and (#{g.edges} >= 19) and wellformed => containsK5}
    // for exactly 1 Graph, 6 Int, 7 Node, 21 Edge is theorem
}

---------------------------------
// * Testing for canFourColor * //
---------------------------------

// A graph containing only three nodes is four colorable
example isFourColorable is {some g: Graph | wellformed and canFourColor} for {
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
example isFourColorable2 is {some g: Graph | wellformed and canFourColor} for {
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

// Check on a graph with 5 nodes which is four colorable
example isFourColorable3 is {some g: Graph | wellformed and canFourColor} for {
    #Int = 5
    Edge = `Edge0 + `Edge1 +`Edge2 + `Edge3 + `Edge4
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
            `Graph0 -> `Edge4
    nodePair = `Edge0 -> `Node0 +
               `Edge0 -> `Node1 +
               `Edge1 -> `Node1 +
               `Edge1 -> `Node2 +
               `Edge2 -> `Node2 +
               `Edge2 -> `Node3 +
               `Edge3 -> `Node3 +
               `Edge3 -> `Node4 +
               `Edge4 -> `Node4 +
               `Edge4 -> `Node5
}

// Check that a K4 graph is 4 colorable
example K4is4Colorable is {some g: Graph | wellformed and canFourColor} for {
    #Int = 5
    Edge = `Edge0 + `Edge1 +`Edge2 + `Edge3 + `Edge4 + `Edge5
    Node = `Node0 + `Node1 + `Node2 + `Node3
    Graph = `Graph0
    nodes = `Graph0 -> `Node0 +
            `Graph0 -> `Node1 +
            `Graph0 -> `Node2 +
            `Graph0 -> `Node3
    edges = `Graph0 -> `Edge0 +
            `Graph0 -> `Edge1 +
            `Graph0 -> `Edge2 +
            `Graph0 -> `Edge3 +
            `Graph0 -> `Edge4 +
            `Graph0 -> `Edge5
    nodePair = `Edge0 -> `Node0 +
               `Edge0 -> `Node1 +
               `Edge1 -> `Node0 +
               `Edge1 -> `Node2 +
               `Edge2 -> `Node0 +
               `Edge2 -> `Node3 +
               `Edge3 -> `Node1 +
               `Edge3 -> `Node2 +
               `Edge4 -> `Node1 +
               `Edge4 -> `Node3 +
               `Edge5 -> `Node2 +
               `Edge5 -> `Node3        
    }

--------------------------------------------
// * Tests verifying Four Color Theorem * //
--------------------------------------------

test expect {
    // A K5 graph cannot be 4 colored
    cannotFourColorK5: {some g: Graph | wellformed and containsK5 and canFourColor} 
    for exactly 1 Graph, 5 Int, exactly 5 Node, 10 Edge is unsat

    // A K3,3 graph can be 4 colored (color one side one color and the other side another color)
    canFourColorK33: {some g: Graph | wellformed and containsK33 and canFourColor}
    for exactly 1 Graph, 5 Int, exactly 6 Node, 9 Edge is sat

    // fourColor4Node: {some g: Graph | planar => canFourColor[g]} for exactly 1 Graph, 4 Node, 
    // exactly 16 Coloring is theorem

//     fourColor5Node: {some g: Graph | isPlanar => canFourColor} for exactly 1 Graph, 5 Node, 10 Edge,
//     exactly 32 Color is theorem

    // fourColor6Node: {some g: Graph | planar => canFourColor[g]} for exactly 1 Graph, 6 Node, 
    // exactly 64 Coloring is theorem
}

run isPlanar