// CISC/CMPE 422/835
module Lists 

sig List {
   head : Node
}

sig Node {
   nextN : lone  Node   // 'next' is already used (in 'ordering' library)
}

fact NoCycle {
   // nextN is acyclic
   // for all n : Node, n is not inside a 'nextN' cycle
   all n : Node |  !(n in n.^nextN)
}

fact AllReachable {
   all n:Node | some l:List | n in (l.head.*nextN)
}

fun reachable[l : List] : set Node {
   l.head.*nextN
}

fact NoSharing {
   // for any two lists l1 and l2, the nodes contained in l1 and l2 is disjoint
   // all l1, l2 : List | nodes in l1 disjoint from nodes in l2
   // all l1, l2 : List | (l1 = l2) or  (no n : Node | (n in (l1.head.*nextN) && (n in (l2.head.*nextN))))
   // all l1, l2 : List | (l1 != l2) implies  (no n : Node | (n in (l1.head.*nextN) && (n in (l2.head.*nextN))))
   // all disj l1, l2 : List | no n : Node | (n in (l1.head.*nextN) && (n in (l2.head.*nextN)))
   // all disj l1, l2 : List | no n : Node | (n in reachable[l1]) && (n in reachable[l2])
   all disj l1, l2 : List | no (reachable[l1] & reachable[l2])
}

assert OneTail {
   // every list contains exactly one node with no successor
   // all l : List | l contains exactly one node with no successor
   // all l : List | reachable[l] contains exactly one node with no success
   // all l : List | {n : reachable[l] | n has no successor} has cardinality 1
   // all l : List | one {n : reachable[l] | n has no successor} 
   // all l : List | one {n : reachable[l] | no m: Node | m=n.nextN} 
   // all l : List | one {n : reachable[l] | no n.nextN}
   all l : List | one n : reachable[l] | no n.nextN
   // all l : List | all n1,n2 : reachable[l] | (no n1.nextN && no n2.nextN) implies n1=n2
} 
check OneTail for exactly 2 List, exactly 3 Node

assert HeadHasNoPred {
//	all l:List | "head of l does not have a predecessor"
//	all l:List | no n:Node | "head of l is successor of n"
//	all l:List | no n:Node | (l.head) in n.nextN
//	all l:List | no n:Node | n in (l.head).~nextN
	all l:List | no n:Node | n in nextN.(l.head)
}
check HeadHasNoPred for 4

// every node either has a predecessor or a successor
assert A1 {all n:Node | (some nextN.n) or (some n.nextN)}
// assert A1 {all n:Node | (some n.~nextN) or (some n.nextN)}
check A1 for 8

// every node inside a list w/ at least two nodes either has a pre- or a succ-cessor
assert A2 {(#List=1 && #Node>1) => all n:Node | (some nextN.n) or (some n.nextN)}
check A2 for 8

// pred Show[] {
//    some List 
// }

run {some List} for 3
// run {} for exactly 2 List, exactly 3 Node
run {} for  2 List, exactly 3 Node
