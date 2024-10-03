// CISC/CMPE 422/835
// inspired by https://github.com/franklingu/collections/tree/master/Alloy/Samples

abstract sig Student {
   plan:  lone Plan,
   taken: set Course,
   grades: taken -> one Grade  // 'grades' is a 3-ary relation
}
sig Freshman, Sophomore, Junior, Senior extends Student {}

sig Plan {
   required : set Course
}

abstract sig Course {}
sig Introductory extends Course {}
sig Advanced extends Course {
   prereqs : some Course
}

abstract sig Grade {}
one sig A,B,C,D,F extends Grade {}	// singleton signatures representing grades

sig Dept {
   teaches : set Course,
   offers : set Plan   
}

fact prereqsAreAcyclic {
   all c: Course | c not in getAllPrereqs[c]
}

fun getAllPrereqs[cs: set Course] : set Course {
   cs.^prereqs
}

fact allPrereqsMet {
   all s:Student | meetsAllPrereqs[s]
}

pred meetsAllPrereqs[s:Student] {
   all c:s.plan.required |
      (c in Advanced && c in s.taken) =>
         (getAllPrereqs[c] in s.taken && getGrade[s,c] !in F)
}

fun getGrade[s:Student,c:Course] : lone Grade {
   c.(s.grades)
}
      
pred canGraduate [s: Student] { 
   s in Senior
   some s.plan
   s.plan.required in s.taken 
   all c:s.taken | getGrade[s,c] in (A + B + C)
}

pred createScenario1 {
   some d: Dept | some (d.teaches & Advanced)
   some s: Student | canGraduate[s]
}
someStudents: run createScenario1 for 5

pred createScenario2 {
   some d: Dept | some (d.teaches & Advanced)
   some s: Student | canGraduate[s]
   #Student = 3
}
threeStudents: run createScenario2 for 5

pred graduateImpliesAllPrereqs {
  all s: Student | canGraduate[s] =>
    getAllPrereqs[s.taken] in s.taken
}
assert graduatesCorrect {
  graduateImpliesAllPrereqs
}
check graduatesCorrect for 1 but 2 Course

