sig Node {
    edges: some Node
}

fact ConnectedGraph{
all n1, n2: Node | n1 in n2.edges iff n2 in n1.edges and !(n1 = n2) and n1.*edges =Node}

sig Message {
    var loc: Node 
}

fact {
all disj m1,m2: Message | always !(m1.loc = m2.loc)}

pred send[m: Message, n: Node] {
n in m.loc.edges
no m2: Message | m2.loc = n
m.loc' = n
}

pred sent[m: Message] {
some n: Node | send[m, n]
}

pred unsent[m: Message] {
m.loc = m.loc'
}

fact SendingOrNot {
all m: Message | always (sent [m] or unsent [m]) }


run{#Message = 3} for 6
