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
deriving Repr

@[simp]
def signStorage (s : Sign) : Nat :=
  match s with
  | .isSigned => 1
  | .isUnsigned => 0

structure Q (s : Sign) (storage : Nat) (fractional : Nat) where
  val : BitVec storage
  enough_storage : signStorage s + fractional ≤ storage
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

instance : Coe (BitVec 64) sq63  where
  coe x := .mk x (by decide)

instance : Coe (BitVec 64) uq63 where
  coe x := .mk x (by decide)

instance : Coe (BitVec 32) sq31  where
  coe x := .mk x (by decide)

instance : Coe (BitVec 32) uq31  where
  coe x := .mk x (by decide)

instance : Coe (BitVec 16) sq15  where
  coe x := .mk x (by decide)

instance : Coe (BitVec 16) uq15  where
  coe x := .mk x (by decide)

instance : Coe (BitVec 8) sq7  where
  coe x := .mk x (by decide)

instance : Coe (BitVec 8) uq7  where
  coe x := .mk x (by decide)

instance : Coe (Q .isUnsigned s f) ((Q .isUnsigned (s+1) f))  where
  coe x := .mk (x.val.zeroExtend (s+1))
           (by
               have h0 : signStorage .isUnsigned + f ≤ s := by
                 exact x.enough_storage
               simp_all
               omega
           )

instance : Coe (Q .isUnsigned s f) ((Q .isSigned (s+1) f))  where
  coe x := .mk (x.val.signExtend (s+1))
           (by
               have h0 : signStorage .isUnsigned + f ≤ s := by
                 exact x.enough_storage
               simp_all [signStorage]
               omega
           )

instance : Coe (Q .isSigned s f) ((Q .isSigned (s+1) f))  where
  coe x := .mk (x.val.signExtend (s+1))
           (by
               have h0 : signStorage .isSigned + f ≤ s := by
                 exact x.enough_storage
               simp_all [signStorage]
               omega
           )

instance : Repr (Q (s : Sign) (storage : Nat) (fractional : Nat)) where
  reprPrec x _ :=
     match s with
     | .isSigned => reprPrec x.val.toInt 0
     | .isUnsigned => reprPrec x.val.toNat 0

instance : Add (Q (s : Sign) (storage : Nat) (fractional : Nat))  where
  add x y := .mk (x.val + y.val) x.enough_storage

instance : Sub (Q (s : Sign) (storage : Nat) (fractional : Nat))  where
  sub x y := .mk (x.val - y.val) x.enough_storage


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
    | .isUnsigned => .mk (x.val.zeroExtend nw * y.val.zeroExtend nw)
       (by
          have h0 : signStorage .isUnsigned + fractional1 ≤ storage1 := by
            exact x.enough_storage
          have h1 : signStorage .isUnsigned + fractional2 ≤ storage2 := by
            exact y.enough_storage
          omega
      )

-- Nat
instance : HAdd (Q (s : Sign) (storage : Nat) (fractional : Nat)) Nat (Q (s : Sign) (storage : Nat) (fractional : Nat)) where
  hAdd x y := .mk (x.val + y) x.enough_storage

instance : HAdd Nat (Q (s : Sign) (storage : Nat) (fractional : Nat)) (Q (s : Sign) (storage : Nat) (fractional : Nat)) where
  hAdd x y := .mk (x + y.val) y.enough_storage

-- Int
instance : HAdd (Q (s : Sign) (storage : Nat) (fractional : Nat)) Int (Q (s : Sign) (storage : Nat) (fractional : Nat)) where
  hAdd x y := .mk (x.val + y) x.enough_storage

instance : HAdd Int (Q (s : Sign) (storage : Nat) (fractional : Nat)) (Q (s : Sign) (storage : Nat) (fractional : Nat)) where
  hAdd x y := .mk (x + y.val) y.enough_storage

def widen (n : Nat)
 (hbigger : n > storage)
 (q : Q (s : Sign) (storage : Nat) (fractional : Nat))  :
  Q s n (fractional) :=
  match s with
  | .isSigned =>
      .mk (q.val.signExtend n)
         (by
            have h0 : signStorage .isSigned + fractional ≤ storage := by
                 exact q.enough_storage
            simp_all [signStorage]
            omega
         )
  | .isUnsigned =>
      .mk (q.val.zeroExtend n)
          (by
            have h0 : signStorage .isUnsigned + fractional ≤ storage := by
                 exact q.enough_storage
            simp_all [signStorage]
            omega
         )

def narrow (n : Nat)
  (q : Q (s : Sign) (storage : Nat) (fractional : Nat))
  (enough_bits : n >= fractional + signStorage s):
  Q s n (fractional) :=
  match s with
  | .isSigned =>
      .mk ((q.val.sshiftRight (storage-n)).truncate n)
         (by
            have h0 : signStorage .isSigned + fractional ≤ storage := by
                 exact q.enough_storage
            simp_all [signStorage]
            omega
         )
  | .isUnsigned =>
      .mk ((q.val >>> (storage - n)).truncate n)
          (by
            have h0 : signStorage .isUnsigned + fractional ≤ storage := by
                 exact q.enough_storage
            simp_all [signStorage]
         )

def widen1
 (q : Q (s : Sign) (storage : Nat) (fractional : Nat))  :
  Q s (storage + 1) (fractional) := widen (storage + 1) (by omega) q

def a : sq15 := 0xffff#16
def b : sq15 := 0x2#16
def c : uq15 := 0xffff#16
def prod : Q .isSigned 32 30 := a * b
def mixedAdd : Q .isSigned 17 15 := (b : Q .isSigned 17 15) + (c : Q .isSigned 17 15)
def bigger : Q .isSigned 64 15 := widen 64 (by omega) a
def narrower : sq15 := narrow 16 bigger (by simp [signStorage])

#eval narrower

end FixedPoint
