#lang forge
// A node is a representation of a two dimensional region
// where its edges are the nodes which the node "touches"
// in its representation in 2D space.
sig Node {}
 
sig Edge {
    // Must be a set of two -- using a set to define bidirectionality
    nodePair: set Node
}

one sig Graph {
    nodes: set Node,
    edges: set Edge
}

sig Color {
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

pred wellformed {
    // A node not having an edge to itself is implicitly implies when we contrain
    // nodes field to be length 2
    // All edges contain exactly two nodes
    all e: Graph.edges | {
        #{n : Node | n in e.nodePair} = 2
    }
    // All edges in the graph must be reachable
    all e1, e2: Graph.edges | {
        reachable[e1, e2, nodePair, ~nodePair]
    }
    // No two edges have same nodePair
    all disj e1, e2: Graph.edges | {
        e1.nodePair != e2.nodePair
    }
    // All graph nodes are in its edges
    nodes in edges.nodePair      
    // All nodes and edges must be in the graph
    Node in Graph.nodes
    Edge in Graph.edges   
    // No two Colors are the same   
    all disj c1, c2: Color | {
        c1.nodeSet != c2.nodeSet
    }
}

// Helper predicate to see if there is an edge between two nodes in the graph
pred hasEdge[n1,n2: Node] {
    // Edge is in graph
    some e: Graph.edges | {
        n1 + n2 = e.nodePair
    } or (
    some e1, e2: Graph.edges | {
        n1 + n2 in (e1.nodePair + e2.nodePair)
        #{n: Node | n in (e1.nodePair & e2.nodePair)} = 1
    })
}

// Predicate which takes in a graph and checks if
// the graph has a K33 subgraph
pred containsK33 {
    some disj v1, v2, v3, v4, v5, v6: Graph.nodes | {
        // Establishes that each of the graphs
        // halves (bipartite) are interconnected (3,3)
        hasEdge[v1,v4]
        hasEdge[v1,v5]
        hasEdge[v1,v6]
        hasEdge[v2,v4]
        hasEdge[v2,v5]
        hasEdge[v2,v6]
        hasEdge[v3,v4]
        hasEdge[v3,v5]
        hasEdge[v3,v6]     
    }
}

// Predicate which takes in a graph containing exactly 5 nodes and
// checks whether the graph is a K5 graph.
pred containsK5 {
    some disj v1, v2, v3, v4, v5: Graph.nodes | {
        hasEdge[v1,v2]   
        hasEdge[v1,v3]
        hasEdge[v1,v4]
        hasEdge[v1,v5]
        hasEdge[v2,v3]
        hasEdge[v2,v4]
        hasEdge[v2,v5]
        hasEdge[v3,v4]
        hasEdge[v3,v5]
        hasEdge[v4,v5]  
    }
}

// Predicate for ensuring that a graph is planar through Kuratowski's
// theorem.
pred isPlanar {
    not containsK5
    not containsK33    
}

pred canFourColor {
    (some disj red, green, blue, yellow: Color | {
        Graph.nodes = ((red.nodeSet + green.nodeSet) + (yellow.nodeSet + blue.nodeSet))
        all e: Graph.edges | {        
            e.nodePair not in red.nodeSet
            e.nodePair not in green.nodeSet
            e.nodePair not in yellow.nodeSet
            e.nodePair not in blue.nodeSet
        }
    })
    // Added additional cases for graphs with <= 3 nodes
    or (some disj green, blue, yellow: Color | {
        Graph.nodes = ((green.nodeSet) + (yellow.nodeSet + blue.nodeSet))
        all e: Graph.edges | {        
            e.nodePair not in green.nodeSet
            e.nodePair not in yellow.nodeSet
            e.nodePair not in blue.nodeSet
        }
    })
    or (some disj blue, yellow: Color | {
        Graph.nodes = (yellow.nodeSet + blue.nodeSet)
        all e: Graph.edges | {        
            e.nodePair not in yellow.nodeSet
            e.nodePair not in blue.nodeSet
        }
    })
    or (one blue: Color | {
        Graph.nodes = (blue.nodeSet)
        all e: Graph.edges | {        
            e.nodePair not in blue.nodeSet
        }
    })
    or (
        no Graph.nodes
    )
}

test expect {
    proof: {(wellformed and isPlanar) implies canFourColor} for exactly 5 Node, exactly 32 Color is theorem
}

run {wellformed and isPlanar and canFourColor} for exactly 4 Node, exactly 16 Color