// CISC/CMPE 422/835
/*
To be able to use Alloy to solve the problem, we need to
- define a suitable notion of 'state' (with 'crossRiver'
  as only state-changing operation)
- use Alloy's built-in 'ordering' module to define 
  sequences of moves as linear sequence of states

For more details, see
- Sections 9.3.4 of courseware
- http://alloytools.org/tutorials/online
*/

open util/ordering[State]

// farmer and his possessions are objects
abstract sig Object {
   eats: set Object
}
one sig Farmer, Fox, Chicken, Grain extends Object {}

// defines who eats who
fact {
   eats = Fox->Chicken + Chicken->Grain
}
   
// stores the objects at near and far side of river
sig State { near, far: set Object }

// operation 1: farmer moves from 'near' to 'far'
pred crossRiverNear2Far[s, s' : State] {
   one x: s.near | {
      s'.near = s.near - x - Farmer - s'.near.eats
      s'.far = s.far + x + Farmer
  }
}
// operation 2: farmer moves from 'far' to 'near'
pred crossRiverFar2Near[s, s' : State] {
   one x: s.far | {
      s'.far = s.far - x - Farmer - s'.far.eats
      s'.near = s.near + x + Farmer
  }
}

// ensure that objects are always correctly distributed over both shores
fact isLegal {
   all s: State | s.far = Object-s.near
}

// any two pair of adjacent states, are related by one of the two crossing operations
fact {
   all s: State, s': s.next {
      Farmer in s.near =>
         crossRiverNear2Far[s,s']
      else
         crossRiverFar2Near[s,s']
   }
}

// objects only move together with farmer
assert nothingMovesWithoutFarmer {
   all s: State, s': s.next |
      (some s'.near-s.near =>
         (Farmer in s.far && Farmer in s'.near && crossRiverFar2Near[s,s'])) &&
      (some s'.far-s.far =>
         (Farmer in s.near && Farmer in s'.far && crossRiverNear2Far[s,s']))
}                
check nothingMovesWithoutFarmer for 8

assert whenMovingEverythingFromNearToFarFarmerIsNeverAlone {
    (first.near=Object && last.far=Object) => all s:State | (s.far != Farmer) && (s.near != Farmer)
}
check whenMovingEverythingFromNearToFarFarmerIsNeverAlone for 8
         
// starting with everything on near, move everything to far
// how many moves do we need at a minmum?
// note that for ordered signatures, the scope constraint is an exact cardinality restriction (i.e., not an upper bound)
scenario1: run { first.near=Object && last.far=Object } for 4 Object, 8 State

// starting with everything on far, move everything but fox to near
scenario2: run { first.far=Object && last.near=Object-Fox } for 8

// starting with everything on near, move 3 objects to far
scenario3: run { first.near=Object && #last.far=3 } for 8

// what are possible initial states such that after 2 moves the Fox is alone on near and 
// after 6 moves everything is on far?
scenario4: run { last.far=Object && first.next.next.near=Fox } for 7




