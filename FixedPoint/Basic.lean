/-
Copyright (c) 2025 Christophe Favergeon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christophe Favergeon

-/

/-!
# Fixed point numbers

[The book](content/index.html)

This file defines fixed point numbers and some operations on them.
It is an exercise to learn Lean4.

It is far from being a complete library and it is a work in progress.

## Tags

fixed point, fixed point numbers, fixed point arithmetic, fixed point operations, fixed point library, dsp
-/

namespace FixedPoint
open BitVec

/-! ## Datatype definitions

-/

/-- Fixed point numbers can be signed or unsigned -/
inductive Sign where
| isSigned
| isUnsigned
deriving Repr

/-- Numbers of bits used by the sign in the encoding of the number -/
@[simp,reducible]
def signStorage (s : Sign) : Nat :=
  match s with
  | .isSigned => 1
  | .isUnsigned => 0

/--
Check if the BitVec has enough bit to encode the sign and
the fractional part. Remaining bits are the integer part.

-/
@[reducible,inline]
def hasEnoughStorage (s : Sign) (storage : Nat) (fractional : Nat) : Prop :=
  signStorage s + fractional ≤ storage

instance : (s : Sign) -> (storage fractional : Nat) -> Decidable (hasEnoughStorage s storage fractional) :=
  fun s storage fractional =>
    if h : signStorage s + fractional ≤ storage then
      isTrue h
    else
      isFalse (by
        simp only [signStorage, Nat.zero_add, ge_iff_le] at h
        exact h)

/-! ### The fixed point number definition

-/

/--

Definition for the fixed point datatype.

It has a sign, a width (in bits) and the numbers of bits for the
fractional part.

* `val` is the BitVec that contains the value of the fixed point number
* `enough_storage` is a proof that the BitVec has enough bits to encode the sign and the fractional part
* `fractional_not_zero` is a proof that the fractional part is not zero

-/
structure Q (s : Sign) (storage : Nat) (fractional : Nat) where
  val : BitVec storage
  enough_storage : hasEnoughStorage s storage fractional := by decide
  fractional_not_zero : 0 < fractional  := by decide
  deriving BEq,Ord,DecidableEq

/-- Fixed points are represented as string using float -/
instance : ToString (Q s storage fractional) where
  toString x := match s with
    | .isSigned => toString (Float.ofInt x.val.toInt / Float.ofInt (2^fractional))
    | .isUnsigned => toString (Float.ofInt x.val.toNat / Float.ofNat (2^fractional))


instance : Repr (Q (s : Sign) (storage : Nat) (fractional : Nat)) where
  reprPrec x _ :=
     match s with
     | .isSigned => reprPrec x.val.toInt 0
     | .isUnsigned => reprPrec x.val.toNat 0


/-! ### Abbreviations for common fixed point numbers

-/
abbrev sq7 := Q .isSigned 8 7
abbrev sq15 := Q .isSigned 16 15
abbrev sq31 := Q .isSigned 32 31
abbrev sq63 := Q .isSigned 64 63

abbrev uq7 := Q .isUnsigned 8 7
abbrev uq15 := Q .isUnsigned 16 15
abbrev uq31 := Q .isUnsigned 32 31
abbrev uq63 := Q .isUnsigned 64 63

/-! ### Conversion operations

-/

instance : Coe (BitVec 64) sq63  where
  coe x := .mk x

instance : Coe (BitVec 64) sq63  where
  coe x := .mk x

instance : Coe (BitVec 64) uq63 where
  coe x := .mk x

instance : Coe (BitVec 32) sq31  where
  coe x := .mk x

instance : Coe (BitVec 32) uq31  where
  coe x := .mk x

instance : Coe (BitVec 16) sq15  where
  coe x := .mk x

instance : Coe (BitVec 16) uq15  where
  coe x := .mk x

instance : Coe (BitVec 8) sq7  where
  coe x := .mk x

instance : Coe (BitVec 8) uq7  where
  coe x := .mk x

instance : OfNat sq63 n where
    ofNat := .mk n

instance : OfNat sq31 n where
    ofNat := .mk n

instance : OfNat sq15 n where
    ofNat := .mk n

instance : OfNat sq7 n where
    ofNat := .mk n

instance : OfNat uq63 n where
    ofNat := .mk n

instance : OfNat uq31 n where
    ofNat := .mk n

instance : OfNat uq15 n where
    ofNat := .mk n

instance : OfNat uq7 n where
    ofNat := .mk n

/-! ### Conversions between signed and unsigned

-/

instance : Coe (Q .isUnsigned s f) ((Q .isUnsigned (s+1) f))  where
  coe x := .mk (x.val.zeroExtend (s+1))
           (by
               have := x.enough_storage
               simp only [signStorage, ge_iff_le]
               omega
           )
           (by exact x.fractional_not_zero
           )

instance : Coe (Q .isUnsigned s f) ((Q .isSigned (s+1) f))  where
  coe x := .mk (x.val.signExtend (s+1))
           (by
               have := x.enough_storage
               simp only [signStorage, ge_iff_le]
               omega
           )
           (by exact x.fractional_not_zero
           )

instance : Coe (Q .isSigned s f) ((Q .isSigned (s+1) f))  where
  coe x := .mk (x.val.signExtend (s+1))
           (by
               have := x.enough_storage
               simp only [signStorage, ge_iff_le]
               omega
           )
           (by exact x.fractional_not_zero
           )


/-! ### Instance Operations for arithmetic operations

-/

instance : Add (Q (s : Sign) (storage : Nat) (fractional : Nat))  where
  add x y := .mk (x.val + y.val) x.enough_storage x.fractional_not_zero

instance : Sub (Q (s : Sign) (storage : Nat) (fractional : Nat))  where
  sub x y := .mk (x.val - y.val) x.enough_storage x.fractional_not_zero


instance : HMul (Q (s : Sign) (storage1 : Nat) (fractional1 : Nat))
                (Q (s : Sign) (storage2 : Nat) (fractional2 : Nat))
                (Q (s : Sign) (storage1+storage2 : Nat) (fractional1 + fractional2)) where
  hMul x y :=
    let nw := storage1 + storage2
    match s with
    | .isSigned => .mk (x.val.signExtend nw * y.val.signExtend nw)
      (by
          have := x.enough_storage
          have := y.enough_storage
          omega
      )
      ( by have := x.fractional_not_zero
           have := y.fractional_not_zero
           omega
      )
    | .isUnsigned => .mk (x.val.zeroExtend nw * y.val.zeroExtend nw)
       (by
          have := x.enough_storage
          have := y.enough_storage
          omega
      )
      ( by have := x.fractional_not_zero
           have := y.fractional_not_zero
           omega
      )

-- Nat
instance : HAdd (Q (s : Sign) (storage : Nat) (fractional : Nat)) Nat (Q (s : Sign) (storage : Nat) (fractional : Nat)) where
  hAdd x y := .mk (x.val + y) x.enough_storage x.fractional_not_zero

instance : HAdd Nat (Q (s : Sign) (storage : Nat) (fractional : Nat)) (Q (s : Sign) (storage : Nat) (fractional : Nat)) where
  hAdd x y := .mk (x + y.val) y.enough_storage y.fractional_not_zero

-- Int
instance : HAdd (Q (s : Sign) (storage : Nat) (fractional : Nat)) Int (Q (s : Sign) (storage : Nat) (fractional : Nat)) where
  hAdd x y := .mk (x.val + y) x.enough_storage x.fractional_not_zero

instance : HAdd Int (Q (s : Sign) (storage : Nat) (fractional : Nat)) (Q (s : Sign) (storage : Nat) (fractional : Nat)) where
  hAdd x y := .mk (x + y.val) y.enough_storage y.fractional_not_zero



/-! ### Other convertion Operations

Convertion operations that are more general and require
additional proofs.

-/


/--
  Create a fixed point number from an integer.

  Arguments :
  - `x` : The integer
  - `h0` : Proof that the fixed point is well formed.
  - `h1` : Proof that the fractional part is not zero.

  This function is *not* saturating the fixed point.
-/
def ofInt {w f : Nat} (x : Int) (h0 : 1 + f <= w := by decide) (h1: 0 < f := by decide): Q .isSigned w f :=
    .mk x (by
            simp only [signStorage, Nat.zero_add,hasEnoughStorage]
            assumption
         )
         (h1
         )

/--
  Create a fixed point number from a BitVec.

  Arguments :
  - `x` : The BitVec
  - `h0` : Proof that the fixed point is well formed.
  - `h1` : Proof that the fractional part is not zero.

  This function is *not* saturating the fixed point.
-/
def ofBitVec {w f : Nat} (x : BitVec w) (h0 : signStorage s + f <= w := by decide) (h1: 0 < f := by decide): Q s w f :=
    .mk x (by
            simp only [signStorage, Nat.zero_add,hasEnoughStorage]
            assumption
         )
         (h1
         )


/-! ## Fixed point specific operations

-/
namespace Q

/-- Number of bits for the integer part -/
def integerPartBits (_ : Q (s : Sign) (storage : Nat) (fractional : Nat)) : Nat :=
  storage - signStorage s - fractional

/-- Convert the number to a variant with more storage -/
def widen (q : Q (s : Sign) (storage : Nat) (fractional : Nat))  (n : Nat)
 (widening : n > storage := by decide):
  Q s n (fractional) :=
  match s with
  | .isSigned =>
      .mk (q.val.signExtend n)
         (by
            have := q.enough_storage
            simp only [signStorage, ge_iff_le]
            omega
         )
         (
            by exact q.fractional_not_zero
         )
  | .isUnsigned =>
      .mk (q.val.zeroExtend n)
          (by
            have := q.enough_storage
            simp only [signStorage, Nat.zero_add, ge_iff_le]
            omega
         )
         (
            by exact q.fractional_not_zero
         )

/--

Narrow the number to a variant with less storage.

The integer part if *truncated*.
No saturation and no rounding is applied.

-/
def narrow (q : Q (s : Sign) (storage : Nat) (fractional : Nat)) (n : Nat)
  (enough_bits : n >= fractional + signStorage s := by decide) (_ : storage > n := by decide):
  Q s n (fractional) :=
  match h : s with
  | .isSigned =>
      .mk ((q.val.sshiftRight (storage-n)).truncate n)
         (by
            have := q.enough_storage
            simp_all only [signStorage, Nat.zero_add, ge_iff_le]
            omega
         )
         ( by exact q.fractional_not_zero
         )
  | .isUnsigned =>
      .mk ((q.val >>> (storage - n)).truncate n)
          (by
            have := q.enough_storage
            simp only [signStorage, Nat.zero_add, ge_iff_le]
            omega
         )
         ( by exact q.fractional_not_zero
         )

/-- Convenience function for a common case -/
def widen1
 (q : Q (s : Sign) (storage : Nat) (fractional : Nat))  :
  Q s (storage + 1) (fractional) := widen q (storage + 1) (by omega)

/-- Saturating addition -/
def satAdd (x y : Q s w f) : Q s w f :=
  let res := x.val + y.val
  if x.val.saddOverflow y.val then
    if res.msb then .mk (.intMax w) x.enough_storage x.fractional_not_zero
    else .mk (.intMin w) x.enough_storage x.fractional_not_zero
  else
   .mk res x.enough_storage x.fractional_not_zero

/-- Saturating subtraction -/
def satSub (x y : Q s w f) : Q s w f :=
  let res := x.val - y.val
  if x.val.ssubOverflow y.val then
    if res.msb then .mk (.intMax w) x.enough_storage x.fractional_not_zero
    else .mk (.intMin w) x.enough_storage x.fractional_not_zero
  else
   .mk res x.enough_storage x.fractional_not_zero

/-- Multiply accumulate *without* saturation -/
def mac (acc : Q s wa (f+f)) (x y : Q s w f) (h0: w+w <= wa := by decide) : Q s wa (f+f) :=
    if h : w+w = wa then
       h ▸ (x*y) + acc
    else
    (widen (x * y) wa (by
       have := x.fractional_not_zero
       simp only [gt_iff_lt]
       omega
      )) + acc

/-- Multiply accumulate *with* saturation -/
def satMac (acc : Q s wa (f+f)) (x y : Q s w f) (h0: w+w <= wa := by decide) : Q s wa (f+f) :=
    if h : w+w = wa then
       (h ▸ (x*y)).satAdd acc
    else
    (widen (x * y) wa (by
       have := x.fractional_not_zero
       simp only [gt_iff_lt]
       omega
      )).satAdd acc

/-- Saturation  -/
def sat (x : Q s w f) (sat_pos : Nat)
(sat_bit: sat_pos <= (w - signStorage s) := by decide): Q s w f :=
  match s with
  | .isSigned =>
      let posSat := 2^sat_pos - 1
      let negSat := -2^sat_pos
      if x.val.toInt > posSat then
        .mk (posSat) x.enough_storage x.fractional_not_zero
      else if x.val.toInt < negSat then
        .mk (negSat) x.enough_storage x.fractional_not_zero
      else
        x
  | .isUnsigned =>
      let posSat := 2^sat_pos - 1
      if x.val.toNat > posSat then
        .mk (posSat) x.enough_storage x.fractional_not_zero
      else
        x

/--
Narrow with saturation

The saturation assumes that there is no integer part.

-/
def narrowWithSat (q : Q (s : Sign) (storage : Nat) (fractional : Nat)) (n : Nat)
  (enough_bits : n >= fractional + signStorage s := by decide)
  (narrowing : n < storage := by decide):
  Q s n fractional :=
    let narrowed := q.narrow n (by
         have := q.enough_storage
         have := q.fractional_not_zero
         simp_all only [signStorage, ge_iff_le]
      ) (narrowing)
    let saturated := narrowed.sat fractional (by
          simp_all only [signStorage]
          match h:s with
          | .isSigned =>
               simp_all only [h,ge_iff_le,signStorage]
               omega
          | .isUnsigned =>
               simp_all only [h,ge_iff_le,signStorage]
               omega
      )
    saturated



/--

Round a number.

If there is no integer part (only a sign bit for instance), then it is not
possible to round to 1 since 1 is not exactly representable.

As consequence, to be able to round we need at least one bit of
integer part hence the condition `signStorage s + f < w`.


-/
def round (x : Q s w f) : Q s w f :=
    let roundValue := .mk (1 <<< (f-1)) x.enough_storage x.fractional_not_zero
    let r := x.satAdd roundValue
    let mask := ~~~((BitVec.allOnes f).zeroExtend w)
    --dbg_trace s!"Round: {roundValue}"
    --dbg_trace s!"mask: {mask}"
    .mk (r.val &&& mask) x.enough_storage x.fractional_not_zero

/-- Narrow with rounding and saturation -/
def narrowWithRoundAndSat (q : Q (s : Sign) (storage : Nat) (fractional : Nat)) (n : Nat)
  (enough_bits : n >= fractional + signStorage s := by decide)
  (narrowing : n < storage := by decide):
  Q s n fractional :=
    let rounded := q.round
    let narrowed := rounded.narrow n
       (by simp_all only [signStorage,ge_iff_le])
       (by simp_all only [signStorage,ge_iff_le])
    let saturated := narrowed.sat fractional
        ( by match h:s with
             | .isSigned =>
                  simp_all only [h,ge_iff_le,signStorage]
                  omega
             | .isUnsigned =>
                  simp_all only [h,ge_iff_le,signStorage]
                  omega
        )
    saturated

end Q


end FixedPoint
