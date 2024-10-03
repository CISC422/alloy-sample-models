module Graphs 
	
sig Node {}

sig Name {}

sig Graph {
	name : Name,		// every Graph has exactly one Name
	initial : set Node,	// every Graph has 0 or more initial Nodes
	curr : lone Node,	// every Graph has 0 or 1 current Nodes	
	nextNode : Node -> Node	// every Graph has a successor relation
}{
 // all n : Node | n in initial.*nextNode
  	all g : Graph | all n : Node | n in (g.@initial).*(g.@nextNode)
}

fact Facts {
	// all nodes belong to at least one graph
	all n : Node | some g : Graph | n in (g.initial).*(g.nextNode)
	// current nodes belong to a graph	
	all g : Graph | g.curr in (g.initial).*(g.nextNode)
}

sig AcyclicGraph extends Graph {
}{
	no n : Node | n in n.^nextNode
}

sig Tree extends AcyclicGraph {
	root : initial
}{
	all n : Node | lone n.~nextNode
}

sig TreeNoSharing extends Tree {}

fun reachableNodes (g : Graph) : set Node {
	(g.initial).*(g.nextNode)
}

fact TreeNoSharingFacts {
	all t1, t2 : TreeNoSharing | t1 != t2 => 
			no (reachableNodes[t1] & reachableNodes[t2])
}

assert CurrAtMostSingleton {
	all g : Graph | lone g.curr
}

assert NextIsTotal {
	all g : Graph | all n : Node | some n.(g.nextNode)
}

assert AllNodesAreReachable {
	all n : Node | some g : Graph | n in (g.initial).*(g.nextNode)
}

assert Acyclic {
	all d : AcyclicGraph, n : Node | n !in n.^(d.nextNode)
}
					
pred P() {
//	no Graph
	some AcyclicGraph
//	some n1,  n2, n3 : Node | n1 != n2 && n2 != n3 && n1 != n3
	#Node > 2
}

run P for 4
check CurrAtMostSingleton for 4
check NextIsTotal for 4
check AllNodesAreReachable for 4
check Acyclic for 4
