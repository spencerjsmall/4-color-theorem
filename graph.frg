#lang forge

abstract sig Color {}
sig Red extends Color {}
sig Green extends Color {}
sig Blue extends Color {}
sig Yellow extends Color {}

sig Node {
    edges: set Node
}

sig Region {
    boundary: set Node
    coloring: one Color
}

sig Graph {
    regions: set Region
}

pred wellformed[g: Graph] {    
    all n, m: g.nodes | lone edges[n][m] -- no double-edges    
    all n, m: g.nodes | n.edges[m] = m.edges[n] -- symmetric
    no iden -- no self-loops
    all n, m: g.nodes | n in m.^edges
    g.regions.boundary = g.nodes
    ...
}

pred containsK3[g: Graph] {
    some disj v1, v2, v3, v4, v5, v6 | g.nodes {
        v1 in v4.edges
        v1 in v5.edges
        v1 in v6.edges
        v2 in v4.edges
        v2 in v5.edges
        v2 in v6.edges
        v3 in v4.edges
        v3 in v5.edges
        v3 in v6.edges
        v1 not in v2.edges
        v1 not in v3.edges
        v2 not in v3.edges
        v4 not in v5.edges
        v4 not in v6.edges
        v5 not in v6.edges        
    }
}

pred isK5[g: Graph] {
    all disj a, b: g.nodes | {
        some edges[a][b]
    }
}

pred kuratowski[g: Graph] {
    all subG: Graph | {        
        subG.edges in g.edges implies
        not isK5[subG] and not containsK33[subG]
    }
}