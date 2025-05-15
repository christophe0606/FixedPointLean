/-
Copyright (c) 2025 Christophe Favergeon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christophe Favergeon

-/
import Std.Tactic.BVDecide

/-! ## Some theorems about fixed point numbers and their operations

It will have to be totally rewritten. The current version
does not make sense.

-/

namespace FixedPoint
open BitVec

-- This will have to be changed. Not the right way to express
-- the property
def bounded {n : Nat} (x : BitVec n) : Bool :=
  let shifted := (x >>> (n-2)) &&& 3#n
  (shifted == 0#n) ∧ (shifted == 3#n)

/-- Attempt to specify when an addition is not saturating.

-/
theorem unsat_add
   (x y : BitVec 32)
   (xpos : bounded x = true)
   (ypos : bounded y = true)
   : BitVec.saddOverflow x y = false := by
      simp_all [bounded]
      bv_decide

end FixedPoint
