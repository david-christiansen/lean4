/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/

prelude
import Init.Data.Array.Basic
import Init.Data.Array.Subarray
import Init.Omega

/-
This module contains splitting operations on subarrays that crucially rely on `omega` for proof
automation. Placing them in another module breaks an import cycle, because `omega` itself uses the
array library.
-/

namespace Subarray
/--
Splits a subarray into two parts.
-/
def split (s : Subarray α) (i : Fin s.size.succ) : (Subarray α × Subarray α) :=
  let ⟨i', isLt⟩ := i
  have := s.start_le_stop
  have := s.stop_le_array_size
  have : i' ≤ s.stop - s.start := Nat.lt_succ.mp isLt
  have : s.start + i' ≤ s.stop := by omega
  have : s.start + i' ≤ s.array.size := by omega
  have : s.start + i' ≤ s.stop := by
    simp only [size] at isLt
    omega
  let pre := {s with
    stop := s.start + i',
    start_le_stop := by omega,
    stop_le_array_size := by assumption
  }
  let post := {s with
    start := s.start + i'
    start_le_stop := by assumption
  }
  (pre, post)

/--
Removes the first `i` elements of the subarray. If there are `i` or fewer elements, the resulting
subarray is empty.
-/
def drop (arr : Subarray α) (i : Nat) : Subarray α where
  array := arr.array
  start := if arr.start + i ≤ arr.stop then arr.start + i else arr.stop
  stop := arr.stop
  start_le_stop := by split <;> simp only [Nat.le_refl, *]
  stop_le_array_size := arr.stop_le_array_size

/--
Keeps only the first `i` elements of the subarray. If there are `i` or fewer elements, the resulting
subarray is empty.
-/
def take (arr : Subarray α) (i : Nat) : Subarray α where
  array := arr.array
  start := arr.start
  stop := if i ≤ arr.stop - arr.start then arr.start + i else arr.stop
  start_le_stop := by
    have := arr.start_le_stop
    split <;> omega
  stop_le_array_size := by
    have := arr.start_le_stop
    have := arr.stop_le_array_size
    split <;> omega
