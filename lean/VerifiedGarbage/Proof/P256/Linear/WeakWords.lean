import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Arithmetic
import VerifiedGarbage.Proof.Ed25519.Word64

namespace VG.Proof.P256.Linear.Weak
open VG.Proof.Ed25519.Word64
abbrev p : Nat := VG.Spec.P256.curve.p
abbrev R : Nat := 2^256
abbrev B : Nat := 2^64
abbrev W4 := Word × Word × Word × Word
def value (a : W4) : Nat := val4 a.1 a.2.1 a.2.2.1 a.2.2.2

def addWords (a b : W4) : W4 × Bool :=
  let c0:=carryOut a.1 b.1 false
  let c1:=carryOut a.2.1 b.2.1 c0
  let c2:=carryOut a.2.2.1 b.2.2.1 c1
  let c3:=carryOut a.2.2.2 b.2.2.2 c2
  ((addCarry a.1 b.1 false,addCarry a.2.1 b.2.1 c0,
    addCarry a.2.2.1 b.2.2.1 c1,addCarry a.2.2.2 b.2.2.2 c2),c3)

def subWords (a b : W4) : W4 × Bool :=
  let c0:=carryOut a.1 (~~~b.1) true
  let c1:=carryOut a.2.1 (~~~b.2.1) c0
  let c2:=carryOut a.2.2.1 (~~~b.2.2.1) c1
  let c3:=carryOut a.2.2.2 (~~~b.2.2.2) c2
  ((addCarry a.1 (~~~b.1) true,addCarry a.2.1 (~~~b.2.1) c0,
    addCarry a.2.2.1 (~~~b.2.2.1) c1,addCarry a.2.2.2 (~~~b.2.2.2) c2),c3)

theorem addWords_value (a b : W4) :
    value (addWords a b).1+R*(addWords a b).2.toNat=value a+value b := by
  simpa only [addWords,value,Bool.toNat_false,Nat.add_zero] using
    add4_value a.1 a.2.1 a.2.2.1 a.2.2.2 b.1 b.2.1 b.2.2.1 b.2.2.2 false

theorem subWords_value (a b : W4) :
    value (subWords a b).1+value b=value a+R*(1-(subWords a b).2.toNat) := by
  simpa only [subWords,value,Bool.toNat_true,Nat.sub_self,Nat.add_zero] using
    sub4_value a.1 a.2.1 a.2.2.1 a.2.2.2 b.1 b.2.1 b.2.2.1 b.2.2.2 true

def modulusWords : W4 := (-1,0xffffffff,0,0xffffffff00000001)
def weakWords (a : W4) (c : Bool) : W4 :=
  (subWords a (if c then modulusWords else (0,0,0,0))).1

theorem value_lt (a : W4) : value a<R := val4_lt ..
theorem weak_value_arith {l o x y : Nat} (c d : Bool)
    (hl : l<R) (ho : o<R) (hx : x<p) (hy : y<p)
    (he : l+R*c.toNat=x+y) (hs : o+p*c.toNat=l+R*(1-d.toNat)) :
    o+p*c.toNat=x+y := by
  cases c <;> cases d <;>
    simp only [Bool.toNat_false,Bool.toNat_true,Nat.mul_zero,Nat.mul_one,
      Nat.sub_zero,Nat.sub_self,Nat.add_zero,p,R,VG.Spec.P256.curve,VG.Spec.P256.p] at * <;> omega

theorem weakWords_value (a : W4) (c : Bool) {x y : Nat}
    (hx : x<p) (hy : y<p) (he : value a+R*c.toNat=x+y) :
    value (weakWords a c)+p*c.toNat=x+y := by
  have hv := subWords_value a (if c then modulusWords else (0,0,0,0))
  have hm : value (if c then modulusWords else (0,0,0,0))=p*c.toNat := by
    cases c <;> decide +kernel
  rw [hm] at hv
  exact weak_value_arith c (subWords a (if c then modulusWords else (0,0,0,0))).2
    (value_lt a) (value_lt _) hx hy he hv

theorem weakWords_mod (a b : W4) (ha : value a<p) (hb : value b<p) :
    value (weakWords (addWords a b).1 (addWords a b).2)%p=(value a+value b)%p := by
  have h := weakWords_value (addWords a b).1 (addWords a b).2 ha hb (addWords_value a b)
  rw [←h,Nat.add_mul_mod_self_left]
end VG.Proof.P256.Linear.Weak
