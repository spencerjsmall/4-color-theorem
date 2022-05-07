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
        no (c1.nodeSet & c2.nodeSet)
    }
}

// Predicate that checks whether the graph contains a homomorphic k## subgraph
pred containsK33 {
    // Checks if there are two collections of nodes c1,c2 such that
    some disj c1, c2: Color | {
        // They both have three nodes and
        #{n: Node | n in c1.nodeSet} = 3
        #{n: Node | n in c2.nodeSet} = 3
        no (c1.nodeSet & c2.nodeSet)
        // Each node in one set is connected to each node in the other
        all n1: c1.nodeSet | {
            all n2: c2.nodeSet | {
                // By an edge in the Graph
                some e: Graph.edges | {
                    n1+n2 = e.nodePair
                } or (
                    // or by a subdivided edge whose removed node is in neither c1,c2
                    some n3: Graph.nodes | {
                        n1+n3 in Graph.edges
                        n2+n3 in Graph.edges
                        n3 not in (c1.nodeSet + c2.nodeSet)                        
                    }
                )
            }
         }
    }
}

// Predicate that checks whether the graph contains a homomorphic K5 subgraph
pred containsK5 {
    // Checks if there is a collection of nodes c such that
    some c: Color | {    
        // it contains 5 nodes    
        #{n: Node | n in c.nodeSet} = 5
        // and all nodes are connected to each other
        all disj n1, n2: c.nodeSet | {
            // by either a graph edge
            some e: Graph.edges | {
                n1 + n2 = e.nodePair
            } 
            or (
                // or a subdivided edge whose removed node is not in the subset
                some n3: Graph.nodes | {
                    n1 + n3 in Graph.edges
                    n2 + n3 in Graph.edges       
                    n3 not in c.nodeSet
                }
            )
        }
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
    // or (
    //     no Graph.nodes
    // )
}

run {wellformed and isPlanar and canFourColor} for 7 Int, 10 Node, 15 Edge
