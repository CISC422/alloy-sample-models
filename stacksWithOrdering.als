// CISC/CMPE 422/835
/*
Stacks with support for sequences of operations

Use Alloy's built-in 'ordering' module to formalize sequences of
stack operations.

For details, see
- Section 9.3.5 in courseware

Remember that you can
- customize the display of the instances that Alloy finds (use tab 'Theme'
  in the instance window)
- use the evaluator to test your understanding of the Alloy language and
  help you write Alloy expressions and formulas (use tab 'Evaluator' in
  the instance window).
*/

module Stacks

open util/ordering[Stack]

sig Data {}

sig Node {
   succ : lone Node,
   val : Data
}

sig Stack {
   head : lone Node
}

pred isEmpty[s : Stack] {
   no s.head
}

pred push[s1 : Stack, d : Data, s2 : Stack] {
   s2.head.val = d
   s2.head.succ= s1.head
}

pred pop[s1 : Stack, s2 : Stack, d : Data] {
   !isEmpty[s1]
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
   all n : Node | some s : Stack | n in nodes[s]
}

fact NoCycles {
   no n : Node | n in n.^succ
}

fact SuccessiveStacksAreTheResultOfAnOperation {
   all s1,s2 : Stack | s1.next=s2 =>
      (some d:Data | push[s1,d,s2] or pop[s1,s2,d])
}            

// create a sequence of stack operations ending in an empty stack
stackScenario1: run {isEmpty[last]} for 7

// create a sequence of stack operations that causes the top two values
// to be reversed
stackScenario2: run {some disj d1,d2 : Data |
   first.head.val=d1 && first.head.succ.val=d2 &&
   last.head.val=d2 && last.head.succ.val=d1} for 2

// create a sequence of stack operations that creates a stack with at least two different values 
stackScenario3: run { #values[last] = 2 } for 3

stackScenario4: run { #{s:Stack | #nodes[s]>=2}>=3 } for 8
            


