// CISC/CMPE 328, CISC 422
// Illustrates how to use Alloy to compute topological sorts for a specific problem (i.e., set of dependency constraints)

module TopSort
open util/ordering[Pos]
// makes elements of 'Pos' totally ordered
// first, last, prev, next, lt, gt, lte, gte, max, min available on elements of 'Pos'

sig Pos {}

abstract sig Task {
   dependsOn : set Task,
   pos : Pos
}

fact {
   all p:Pos | one pos.p     // p.~pos    // positions are neither shared nor unused
}

pred tasksAreTopSorted[] {
//   all t1,t2:Task | t2 in t1.dependsOn => lt[t2.pos,t1.pos]    // topological sort
   all t1,t2:Task | t1->t2 in dependsOn => lt[t2.pos,t1.pos]    // topological sort
}

one sig T0, T1, T2, T3, T4, T5, T6, T7 extends Task {}

pred ConstraintsA[] {
   dependsOn = T0->T1 + T1->T2 + T2->T3 + T3->T4 + T4->T5 + T5->T6 + T6->T7
}

pred ConstraintsB[] {
   dependsOn = T0->T1 + T1->T2 + T2->T3 + T3->T4 + T4->T5 + T5->T6 
}

pred ConstraintsC[] {
   dependsOn = T0->T0
}
      
scTop: run {tasksAreTopSorted[]} for 8
scNoTop: run {!tasksAreTopSorted[]} for 8

scA: run {tasksAreTopSorted[] && ConstraintsA[]} for 8
scB: run {tasksAreTopSorted[] && ConstraintsB[]} for 8
scC: run {tasksAreTopSorted[] && ConstraintsC[]} for 8



          
