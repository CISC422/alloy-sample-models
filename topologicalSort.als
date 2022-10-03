// CISC/CMPE 422/835

module TopSort
open util/ordering[Pos]
// makes elements of 'Pos' totally ordered
// first, last, prev, next, lt, gt, lte, gte, max, min available on elements of 'Pos'

sig Pos {}

sig Task {
   dependsOn: set Task,
   pos : Pos
}

fact {
   all p : Pos | one pos.p        // positions are neither shared nor unused
}

pred tasksAreTopSorted[] {
   all t1, t2 : Task | t2 in t1.dependsOn => lt[t2.pos, t1.pos]    // topological sort
}

pred dependsOnIsAyclic[] {
   all t : Task | t !in t.^dependsOn
}

assert A1 {
   tasksAreTopSorted[]
}

assert A2 {
  tasksAreTopSorted[] implies dependsOnIsAyclic[]
}

assert A3 {
  dependsOnIsAyclic[] implies tasksAreTopSorted[] 
}

sc_top: run {tasksAreTopSorted[]} for 5
sc_noTop: run {!tasksAreTopSorted[]} for 5

ch_alwaysTop: check A1 for 8
ch_topImpliesAcylic: check A2 for 8
ch_AcyclicImpliesTop: check A3 for 8


          
