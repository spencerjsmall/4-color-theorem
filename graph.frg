#lang forge

abstract sig Color {}
sig Red extends Color {}
sig Green extends Color {}
sig Blue extends Color {}
sig Yellow extends Color {}

sig Node {
    edges: set Node
}

// A region is a set of nodes which are the same color.
sig Region {
    boundary: set Node,
    coloring: one Color
}

// This could be a set of nodes instead?
// Not sure what the benefit of a set of Regions is
sig Graph {
    regions: set Region,
    nodes: set Node
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
    // I don't think we'll have to cover this case by definition
    // of a set (each elem is unique), but I'll leave it here just in
    // case.    
    // all n, m: g.nodes | lone edges[n][m] -- no double-edges
    // Covered symmetric case below    
    // all n, m: g.nodes | n.edges[m] = m.edges[n] -- symmetric
    // Covered self-loop case below
    // no iden -- no self-loops
    

    // All nodes must be interconnected in some way
    all n, m: g.nodes | n in m.^edges
    // Edges must work both ways
    all n,m : Node | {
        m in n.edges implies n in m.edges
    }
    // A node cannot have an edge to itself
    all n: Node | {
        n not in n.edges
    }
    // All nodes in the graph should be in a region
    g.regions.boundary = g.nodes
    // No node can occupy two regions
    all n: Node | {
        no disj r1,r2: Region | {
            n in r1.boundary
            n in r2.boundary
        }
    }
    // No two regions can have the same color
    no disj r1,r2: Region | {
        r1.coloring = r2.coloring
    }
}

// Assuming this takes in a graph for the case of
// making subgraphs
pred containsK3[g: Graph] {
    some disj v1, v2, v3, v4, v5, v6: Node | {
        v1 in g.nodes
        v2 in g.nodes
        v3 in g.nodes
        v4 in g.nodes
        v5 in g.nodes
        v6 in g.nodes
        // Establishes that each of the graphs
        // halves (bipartite) are interconnected (3,3)
        v1 in v4.edges
        v1 in v5.edges
        v1 in v6.edges
        v2 in v4.edges
        v2 in v5.edges
        v2 in v6.edges
        v3 in v4.edges
        v3 in v5.edges
        v3 in v6.edges
        // Holds definition for a bipartite graph
        v1 not in v2.edges
        v1 not in v3.edges
        v2 not in v3.edges
        v4 not in v5.edges
        v4 not in v6.edges
        v5 not in v6.edges        
    }
}

// The graph must have 
pred isK5[g: Graph] {
    some disj a, b: g.nodes | {
        some edges[a][b]
    }
}

// pred kuratowski[g: Graph] {
//     all subG: Graph | {        
//         subG.edges in g.edges implies
//         not isK5[subG] and not containsK33[subG]
//     }
// }

run {
    one g: Graph | {
        wellformed[g]
        containsK3[g]
    }
} for exactly 1 Graph, 4 Int, 6 Node
