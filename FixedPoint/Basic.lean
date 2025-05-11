import Std.Tactic.BVDecide


namespace FixedPoint
open BitVec

def bounded {n : Nat} (x : BitVec n) : Bool :=
  let shifted := (x >>> (n-2)) &&& 3#n
  (shifted == 0#n) ∧ (shifted == 3#n)

theorem unsat_add
   (x y : BitVec 32)
   (xpos : bounded x = true)
   (ypos : bounded y = true)
   : BitVec.saddOverflow x y = false := by
      simp_all [bounded]
      bv_decide

inductive Sign where
| isSigned
| isUnsigned
deriving Repr,DecidableEq

@[simp]
def signStorage (s : Sign) : Nat :=
  match s with
  | .isSigned => 1
  | .isUnsigned => 0

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


structure Q (s : Sign) (storage : Nat) (fractional : Nat) where
  val : BitVec storage
  enough_storage : hasEnoughStorage s storage fractional := by decide
  no_zero_bitvec : storage > 0 := by decide
  deriving Repr

def mantissa (_ : Q (s : Sign) (storage : Nat) (fractional : Nat)) : Nat :=
  storage - signStorage s - fractional

abbrev sq7 := Q .isSigned 8 7
abbrev sq15 := Q .isSigned 16 15
abbrev sq31 := Q .isSigned 32 31
abbrev sq63 := Q .isSigned 64 63

abbrev uq7 := Q .isUnsigned 8 7
abbrev uq15 := Q .isUnsigned 16 15
abbrev uq31 := Q .isUnsigned 32 31
abbrev uq63 := Q .isUnsigned 64 63

@[inline,reducible]
def minFractional (s : Sign) (storage : Nat) : Nat :=
  match s with
  | .isSigned => storage - 1
  | .isUnsigned => storage


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

instance : Coe (Q .isUnsigned s f) ((Q .isUnsigned (s+1) f))  where
  coe x := .mk (x.val.zeroExtend (s+1))
           (by
               have h0 : signStorage .isUnsigned + f ≤ s := by
                 exact x.enough_storage
               simp only [signStorage, ge_iff_le]
               omega
           )
           (by have h0 : s > 0 := by
                 exact x.no_zero_bitvec
               simp only [gt_iff_lt, Nat.zero_lt_succ]
           )

instance : Coe (Q .isUnsigned s f) ((Q .isSigned (s+1) f))  where
  coe x := .mk (x.val.signExtend (s+1))
           (by
               have h0 : signStorage .isUnsigned + f ≤ s := by
                 exact x.enough_storage
               simp only [signStorage, ge_iff_le]
               omega
           )
           (by have h0 : s > 0 := by
                 exact x.no_zero_bitvec
               simp only [gt_iff_lt, Nat.zero_lt_succ]
           )

instance : Coe (Q .isSigned s f) ((Q .isSigned (s+1) f))  where
  coe x := .mk (x.val.signExtend (s+1))
           (by
               have h0 : signStorage .isSigned + f ≤ s := by
                 exact x.enough_storage
               simp only [signStorage, ge_iff_le]
               omega
           )
           (by have h0 : s > 0 := by
                 exact x.no_zero_bitvec
               simp only [gt_iff_lt, Nat.zero_lt_succ]
           )

instance : Repr (Q (s : Sign) (storage : Nat) (fractional : Nat)) where
  reprPrec x _ :=
     match s with
     | .isSigned => reprPrec x.val.toInt 0
     | .isUnsigned => reprPrec x.val.toNat 0

instance : Add (Q (s : Sign) (storage : Nat) (fractional : Nat))  where
  add x y := .mk (x.val + y.val) x.enough_storage x.no_zero_bitvec

instance : Sub (Q (s : Sign) (storage : Nat) (fractional : Nat))  where
  sub x y := .mk (x.val - y.val) x.enough_storage x.no_zero_bitvec


instance : HMul (Q (s : Sign) (storage1 : Nat) (fractional1 : Nat))
                (Q (s : Sign) (storage2 : Nat) (fractional2 : Nat))
                (Q (s : Sign) (storage1+storage2 : Nat) (fractional1 + fractional2)) where
  hMul x y :=
    let nw := storage1 + storage2
    match s with
    | .isSigned => .mk (x.val.signExtend nw * y.val.signExtend nw)
      (by
          have h0 : signStorage .isSigned + fractional1 ≤ storage1 := by
            exact x.enough_storage
          have h1 : signStorage .isSigned + fractional2 ≤ storage2 := by
            exact y.enough_storage
          omega
      )
      ( by have h0 : storage1 > 0 := by
            exact x.no_zero_bitvec
           have h1 : storage2 > 0 := by
            exact y.no_zero_bitvec
           omega
      )
    | .isUnsigned => .mk (x.val.zeroExtend nw * y.val.zeroExtend nw)
       (by
          have h0 : signStorage .isUnsigned + fractional1 ≤ storage1 := by
            exact x.enough_storage
          have h1 : signStorage .isUnsigned + fractional2 ≤ storage2 := by
            exact y.enough_storage
          omega
      )
      ( by have h0 : storage1 > 0 := by
            exact x.no_zero_bitvec
           have h1 : storage2 > 0 := by
            exact y.no_zero_bitvec
           omega
      )

-- Nat
instance : HAdd (Q (s : Sign) (storage : Nat) (fractional : Nat)) Nat (Q (s : Sign) (storage : Nat) (fractional : Nat)) where
  hAdd x y := .mk (x.val + y) x.enough_storage x.no_zero_bitvec

instance : HAdd Nat (Q (s : Sign) (storage : Nat) (fractional : Nat)) (Q (s : Sign) (storage : Nat) (fractional : Nat)) where
  hAdd x y := .mk (x + y.val) y.enough_storage y.no_zero_bitvec

-- Int
instance : HAdd (Q (s : Sign) (storage : Nat) (fractional : Nat)) Int (Q (s : Sign) (storage : Nat) (fractional : Nat)) where
  hAdd x y := .mk (x.val + y) x.enough_storage x.no_zero_bitvec

instance : HAdd Int (Q (s : Sign) (storage : Nat) (fractional : Nat)) (Q (s : Sign) (storage : Nat) (fractional : Nat)) where
  hAdd x y := .mk (x + y.val) y.enough_storage y.no_zero_bitvec

def widen (q : Q (s : Sign) (storage : Nat) (fractional : Nat))  (n : Nat)
 (hbigger : n > storage := by decide)
  :
  Q s n (fractional) :=
  match s with
  | .isSigned =>
      .mk (q.val.signExtend n)
         (by
            have h0 : signStorage .isSigned + fractional ≤ storage := by
                 exact q.enough_storage
            simp only [signStorage, ge_iff_le]
            omega
         )
         (
            by have h0 : storage > 0 := by
                 exact q.no_zero_bitvec
               omega
         )
  | .isUnsigned =>
      .mk (q.val.zeroExtend n)
          (by
            have h0 : signStorage .isUnsigned + fractional ≤ storage := by
                 exact q.enough_storage
            simp only [signStorage, Nat.zero_add, ge_iff_le]
            omega
         )
         (
            by have h0 : storage > 0 := by
                 exact q.no_zero_bitvec
               omega
         )

def narrow (q : Q (s : Sign) (storage : Nat) (fractional : Nat)) (n : Nat)
  (enough_bits : n >= fractional + signStorage s := by decide)
  (no_zero_bitvec : n > 0 := by decide):
  Q s n (fractional) :=
  match h : s with
  | .isSigned =>
      .mk ((q.val.sshiftRight (storage-n)).truncate n)
         (by
            have h0 : signStorage .isSigned + fractional ≤ storage := by
                 exact q.enough_storage
            simp_all only [signStorage, Nat.zero_add, ge_iff_le]
            omega
         )
         ( by simp_all only [signStorage,gt_iff_lt]
         )
  | .isUnsigned =>
      .mk ((q.val >>> (storage - n)).truncate n)
          (by
            have h0 : signStorage .isUnsigned + fractional ≤ storage := by
                 exact q.enough_storage
            simp only [signStorage, Nat.zero_add, ge_iff_le]
            omega
         )
         ( by simp_all only [signStorage,gt_iff_lt]
         )


def widen1
 (q : Q (s : Sign) (storage : Nat) (fractional : Nat))  :
  Q s (storage + 1) (fractional) := widen q (storage + 1) (by omega)

def a : sq15 := 0xffff#16
def b : sq15 := 0x2#16
def c : uq15 := 0xffff#16
def prod : Q .isSigned 32 30 := a * b
def mixedAdd : Q .isSigned 17 15 := (b : Q .isSigned 17 15) + (c : Q .isSigned 17 15)
def bigger : Q .isSigned 64 15 := widen a 64
def narrower : sq15 := narrow bigger 16

/--
  Create a fixed point number from an integer.

  Arguments :
  - `x` : The integer
  - `h0` : Proof that the fixed point is well formed.

  This function is not saturating the fixed point.
-/
def ofInt {w f : Nat} (x : Int) (h0 : 1 + f <= w := by decide): Q .isSigned w f :=
    .mk x (by
            simp only [signStorage, Nat.zero_add,hasEnoughStorage]
            assumption
         )
         (by simp only [gt_iff_lt]
             omega
         )

--#eval narrower

def satAdd (x y : Q s w f) : Q s w f :=
  let res := x.val + y.val
  if x.val.saddOverflow y.val then
    if res.msb then .mk (.intMax w) x.enough_storage x.no_zero_bitvec
    else .mk (.intMin w) x.enough_storage x.no_zero_bitvec
  else
   .mk res x.enough_storage x.no_zero_bitvec

def satSub (x y : Q s w f) : Q s w f :=
  let res := x.val - y.val
  if x.val.ssubOverflow y.val then
    if res.msb then .mk (.intMax w) x.enough_storage x.no_zero_bitvec
    else .mk (.intMin w) x.enough_storage x.no_zero_bitvec
  else
   .mk res x.enough_storage x.no_zero_bitvec

def mac (acc : Q s wa (f+f)) (x y : Q s w f) (h0: w+w <= wa := by decide) : Q s wa (f+f) :=
    if h : w+w = wa then
       h ▸ (x*y) + acc
    else
    (widen (x * y) wa (by
       have hpos : 0 < w := by
        exact x.no_zero_bitvec
       simp only [gt_iff_lt]
       omega
      )) + acc

--#eval (1#16:Q .isSigned 16 15)
#eval mac (ofInt 1:Q .isSigned 17 14) (0x81#8 : sq7) (4#8 : sq7)

end FixedPoint
