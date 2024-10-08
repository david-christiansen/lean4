import Std.Tactic.BVDecide

open BitVec

/--
error: The prover found a potential counterexample, consider the following assignment:
y = 0xffffffffffffffff#64
-/
#guard_msgs in
example {y : BitVec 64} : zeroExtend 32 y = 0 := by
  bv_decide
