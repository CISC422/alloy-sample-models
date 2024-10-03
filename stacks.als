// CISC/CMPE 422/835
module Stacks

sig Data {}

sig Node {
   succ : lone Node,
   val : Data
}

sig Stack {
   head : lone Node
}

pred empty[s : Stack] {
   no s.head
}

pred push[s1 : Stack, d : Data, s2 : Stack] {
   s2.head.val = d
   s2.head.succ= s1.head
}

pred pop[s1 : Stack, s2 : Stack, d : Data] {
   !empty[s1]
   d = s1.head.val
   s2.head = s1.head.succ  
}

fun nodes[s : Stack] : set Node {
   (s.head).*succ
}

fun values[s : Stack] : set Data {
   nodes[s].val
}

fact NoReachableNodes {
   all n:Node | some s:Stack | n in nodes[s]
}

fact NoCycles {
   no n:Node | n in n.^succ
}

// assertions formalizing expected properties 
assert PushProps {
   all s1,s2:Stack | all d:Data | push[s1,d,s2] => !empty[s2]    // stack not empty after push
   all s1,s2:Stack | all d:Data | push[s1,d,s2] => values[s1]+d = values[s2]           // push adds pushed value
}

assert PopProps {
   all s1,s2:Stack | all d:Data | pop[s1,s2,d] => values[s1]=values[s2]+d                // pop removes top value only
}

assert PushPopProps {
   all s1,s2:Stack | all d:Data | push[s1,d,s2] => pop[s2,s1,d]                // after pushing d onto s1, a pop returns s1 and d
   all s1,s2:Stack | all d:Data | pop[s1,s2,d] => push[s2,d,s1]                // after popping d off s1, a push of d returns s1
   all s1,s2,s3:Stack | all d1,d2:Data |         
                (push[s1, d1, s2] && pop[s2, s3, d2]) => (d1=d2 && s1.head=s3.head && values[s1]=values[s3])
   all s1,s2,s3:Stack | all d:Data | 
                (pop[s1,s2,d] && push[s2,d,s3]) => (values[s1]=values[s3])
}

// predicates to generate some interesting scenarios
pred ShowNonEmpty {
   some Stack
}
pred ShowNonEmptyNoSharedNodesOrData {
   #Stack=2
   all disj s1,s2 : Stack | no (values[s1] & values[s2])
   all disj s1,s2 : Stack | no (nodes[s1] & nodes[s2])
}        
pred ShowStackEmptyAfterPop {
   #Stack = 2
   some s1,s2 : Stack | some d : Data | pop[s1,s2,d] && empty[s2]
}
pred ShowStackNonEmptyAfterPop {
   #Stack = 2
   some s1,s2 : Stack | some d : Data | pop[s1,s2,d] && !empty[s2]
}
pred ShowStackAfterPush {
   #Stack = 2
   some s1,s2 : Stack | some d : Data | push[s1,d,s2] 
}
// commands
sc1: run ShowNonEmpty for 4 expect 1
sc2: run ShowNonEmptyNoSharedNodesOrData for 4 expect 1
sc3: run ShowStackEmptyAfterPop for 4 expect 1
sc4: run ShowStackNonEmptyAfterPop for 4 but exactly 2 Data expect 1
sc5: run ShowStackAfterPush for 4 expect 1

che1: check PushProps for 4 expect 0
che2: check PopProps for 4 expect 0
che3: check PushPopProps for 4 expect 0



