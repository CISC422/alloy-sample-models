// CISC/CMPE 422/835
// For integers (i.e., elements of signature 'Int'), scope means 'bitwidth'.
// You may get surprising analysis results when using the 'cardinality' operator '#' with a bidwidth that is too small.
// Default bitwidth is '4' which allows for 16 integers (-8 to 7).
// If you need more than that, use a larger bitwidth.

module ScopeForInts

check A1 {all i:Int | -4<=i && i<=3} for 3 Int expect 0     // bitwidth '3' allows for 8 integers: -4 to 3
check A2 {min[Int]=-4 && max[Int]=3} for 3 Int expect 0     // bitwidth '3' allows for 8 integers: -4 to 3
check A3 {all i:Int | -8<=i && i<=7} for 4 Int expect 0     // bitwidth '4' allows for 16 integers: -8 to 7
check A4 {min[Int]=-8 && max[Int]=7} for 4 Int expect 0     // bitwidth '4' allows for 16 integers: -8 to 7
check A5 {all i:Int | -8<=i && i<=7} expect 0               // bitwidth '4' allows for 16 integers: -8 to 7
check A6 {min[Int]=-8 && max[Int]=7} expect 0               // bitwidth '4' is default

// When trying to count beyond the possible range, analyses may fail unexpectedly...
sig S {} 
check B1 {#S=0 iff no S} for 7 S expect 0            	    // ok: can represent '7' with default bitwidth '4'
check B2 {#S=0 iff no S} for 8 S expect 0            	    // not ok: can't represent '8' with default bitwidth '4'; fails
check B3 {#S=0 iff no S} for 8 S, 5 Int expect 0            // ok: can represent '8' with default bitwidth '5' (-16 to 15)
run B4 {3<4} for 3 Int expect 1           	            // not ok: should succeed, but fails
run B5 {#S=4} for 4 S, 3 Int expect 1            	    // not ok: should succeed, but fails
run B6 {#S=8} for 8 S expect 1            	            // not ok: should succeed, but fails

// ... or not
check C1 {#S <= 3} for 4 S, 3 Int expect 1            	    // not ok: should fail, but succeeds
check C2 {#S <= 7} for 8 S, 4 Int expect 1            	    // not ok: should fail, but succeeds
check C3 {#S <= 7} for 8 S expect 1            	            // not ok: should fail, but succeeds








