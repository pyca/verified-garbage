module

public import VerifiedGarbage.Impl.P256.Linear
public import VerifiedGarbage.Proof.P256.Linear.Words
public import VerifiedGarbage.Proof.P256.Linear.Arithmetic
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Impl.NatPairs
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.Mont.AArch64.Words
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! ### `P256.Linear.CorrectionWords`, which only this module used -/

section

/-! ### `P256.Linear.CorrectionValue`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.P256.Linear
open VG VG.Proof.Ed25519 VG.Proof.Mont.AArch64
open VG.Proof.P256.VerifySparse (four addFour_value)

private theorem mod_of_eq (out n q carry : Nat)
    (h : out+(q+1)*p=n+2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576*carry) :
    (out : Int)%(2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576:Int)=
      ((n:Int)-((q:Int)+1)*(p:Int))%(2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576:Int) := by
  have he : (out:Int)=(n:Int)-((q:Int)+1)*(p:Int)+(2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576:Int)*(carry:Int) := by
    simp only [p_value] at h ⊢
    omega_using [h]
  rw [he,Int.add_mul_emod_self_left]


/-- Arithmetic interface for the two carry chains implementing subtraction of q*p. -/
theorem subtractQ_equation (a b c d e d' e' : BitVec 64) (co : Bool)
    (out borrow : Nat) (he : e.toNat≤20)
    (hd : d'.toNat+2^64*co.toNat=d.toNat+(e.toNat+1)*2^32)
    (hh : e'.toNat=e.toNat+co.toNat)
    (hsub : out+five (0-(e+1)) ((e+1)<<<32-1) 0 (e+1) (e+1)=
      five a b c d' e'+2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576*borrow) :
    out+(e.toNat+1)*p=five a b c d e+2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576*borrow := by
  have eq : (e+1).toNat=e.toNat+1 := by
    simp only [BitVec.toNat_add,show (1 : BitVec 64).toNat=1 from rfl]; omega_using [he]
  have es : ((e+1)<<<32).toNat=(e.toNat+1)*2^32 := by
    simp only [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,eq]; omega_using [he]
  have ex : (0-(e+1)).toNat=2^64-(e.toNat+1) := by
    simp only [BitVec.toNat_sub,show (0 : BitVec 64).toNat=0 from rfl,eq]; omega_using []
  have ey : ((e+1)<<<32-1).toNat=(e.toNat+1)*2^32-1 := by
    simp only [BitVec.toNat_sub,show (1 : BitVec 64).toNat=1 from rfl,es]; omega_using [he]
  simp only [five,four,ex,ey,eq,show (0 : BitVec 64).toNat=0 from rfl] at hsub
  simp only [five,four,p_value]
  omega_using [hd, hh, hsub]

/-- A signed residual of magnitude below p has only zero or all-ones above bit255. -/
theorem remainder_shape (lo hi : Nat) (d : Int)
    (hlo : lo<2^256) (hhi : hi<2^64) (hd0 : -(p:Int)≤d) (hd1 : d<(p:Int))
    (h : ((lo:Int)+(2^256:Int)*(hi:Int))%(2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576:Int)=d%(2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576:Int)) :
    hi=(if d<0 then 2^64-1 else 0) ∧
      (lo:Int)=(if d<0 then (2^256:Int)+d else d) := by
  simp only [p_value] at hd0 hd1
  by_cases hz : d<0
  · rw [ite_eq_left hz,ite_eq_left hz]
    omega_using [hlo, hhi, hd0, h, hz]
  · rw [ite_eq_right hz,ite_eq_right hz]
    omega_using [hlo, hhi, hd1, h, hz]


/-- Add p through the sparse word pattern selected by a signed fifth word. -/
def addBack (a b c d e : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  let mask := (e<<<32)>>>32
  let a' := Word64.addCarry a e false
  let c0 := Word64.carryOut a e false
  let b' := Word64.addCarry b mask c0
  let c1 := Word64.carryOut b mask c0
  let c' := Word64.addCarry c 0 c1
  let c2 := Word64.carryOut c 0 c1
  let d' := Word64.addCarry d (0-mask) c2
  (a',b',c',d')

theorem addBack_value (a b c d e : BitVec 64) (neg : Bool)
    (he : e=if neg then -1 else 0) :
    let r:=addBack a b c d e
    four r.1 r.2.1 r.2.2.1 r.2.2.2=
      (four a b c d+(if neg then p else 0))%2^256 := by
  have hh := addFour_value a b c d e ((e<<<32)>>>32) 0 (0-((e<<<32)>>>32))
  have hm : four e ((e<<<32)>>>32) 0 (0-((e<<<32)>>>32))=(if neg then p else 0) := by
    subst e
    cases neg <;> decide +kernel
  rw [hm] at hh
  exact hh


private theorem finish_value (lo n : Nat) (delta : Int)
    (hs : (lo:Int)=if delta<0 then (2^256:Int)+delta else delta)
    (hc : (if delta<0 then delta+(p:Int) else delta)=(n%p:Int)) :
    (lo+(if decide (delta<0) then p else 0))%2^256=n%p := by
  have hm : n%p<p := Nat.mod_lt n (by decide)
  simp only [p_value] at hc hm ⊢
  by_cases hd : delta<0
  · simp only [hd,decide_true,ite_true] at hs hc ⊢
    omega_using [hs, hc]
  · simp only [hd,decide_false,Bool.false_eq_true,ite_false,Nat.add_zero] at hs hc ⊢
    omega_using [hs, hc]

/-- The estimated quotient plus signed correction produces the canonical residue. -/
theorem correction_value (n q borrow : Nat) (a b c d e : BitVec 64)
    (hn : n<21*p) (hq : q=n/2^256)
    (hv : five a b c d e+(q+1)*p=n+2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576*borrow) :
    ∃ neg : Bool, e=(if neg then -1 else 0) ∧
      (four a b c d+(if neg then p else 0))%2^256=n%p := by
  have hmod := mod_of_eq (five a b c d e) n q borrow hv
  have hh := quotient_bounds (n:Int) (by simp only [p_value]; omega_using [])
    (by simp only [p_value] at hn ⊢; omega_using [hn])
  have hq' : (q:Int)=(n:Int)/(radix:Int) := by
    simp only [radix] at *
    omega_using [hq]
  rw [←hq'] at hh
  let delta : Int := (n:Int)-((q:Int)+1)*(p:Int)
  have hlo := four_lt a b c d
  have hshape := remainder_shape (four a b c d) e.toNat delta hlo e.isLt hh.2.2.1 hh.2.2.2
    (by simpa only [five,Int.natCast_add,Int.natCast_mul,Int.natCast_pow,show ((2:Nat):Int)=2 from rfl] using hmod)
  have he : e=if decide (delta<0) then -1 else 0 := by
    apply BitVec.eq_of_toNat_eq
    by_cases hd : delta<0
    · simpa only [hd,decide_true,ite_true,show (-1 : BitVec 64).toNat=2^64-1 from rfl] using hshape.1
    · simpa only [hd,decide_false,Bool.false_eq_true,ite_false,show (0 : BitVec 64).toNat=0 from rfl] using hshape.1
  refine ⟨decide (delta<0),he,?_⟩
  have hc := corrected_mod (n:Int) (by simp only [p_value]; omega_using [])
    (by simp only [p_value] at hn ⊢; omega_using [hn])
  rw [←hq'] at hc
  change (if delta<0 then delta+(p:Int) else delta)=(n:Int)%(p:Int) at hc
  apply finish_value (four a b c d) n delta hshape.2
  simpa only [Int.natCast_emod] using hc


end VG.Proof.P256.Linear

end

end


@[expose] public section

namespace VG.Proof.P256.Linear
open VG.Proof.Ed25519.Word64
open VG.Proof.P256.VerifySparse (four)

private theorem pow320 : (2:Nat)^320=2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576 := by
  decide +kernel

abbrev W5 := Word × Word × Word × Word × Word

def w5value (a : W5) := five a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2

def subWords (a b c d e x y z w v : Word) : W5 × Bool :=
  let c0 := carryOut a (~~~x) true
  let c1 := carryOut b (~~~y) c0
  let c2 := carryOut c (~~~z) c1
  let c3 := carryOut d (~~~w) c2
  let c4 := carryOut e (~~~v) c3
  ((addCarry a (~~~x) true,addCarry b (~~~y) c0,addCarry c (~~~z) c1,
    addCarry d (~~~w) c2,addCarry e (~~~v) c3),!c4)

theorem subWords_value (a b c d e x y z w v : Word) :
    w5value (subWords a b c d e x y z w v).1+five x y z w v=
      five a b c d e+2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576*(subWords a b c d e x y z w v).2.toNat := by
  have h := subFive_value a b c d e x y z w v
  simp only [pow320] at h
  simp only [w5value, subWords]
  exact h

def subQ (a b c d e : Word) : W5 × Bool :=
  let q := e+1
  let ds := addCarry d (q<<<32) false
  let es := addCarry e 0 (carryOut d (q<<<32) false)
  subWords a b c ds es (0-q) ((q<<<32)-1) 0 q q

private theorem subQ_finish (a b c d e ds es : Word) (co : Bool)
    (he : e.toNat≤20)
    (hd : ds.toNat+2^64*co.toNat=d.toNat+(e.toNat+1)*2^32)
    (hh : es.toNat=e.toNat+co.toNat) :
    w5value (subWords a b c ds es (0-(e+1)) (((e+1)<<<32)-1) 0 (e+1) (e+1)).1+(e.toNat+1)*p=
      five a b c d e+2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576*(subWords a b c ds es (0-(e+1)) (((e+1)<<<32)-1) 0 (e+1) (e+1)).2.toNat := by
  have hsub := subWords_value a b c ds es (0-(e+1)) (((e+1)<<<32)-1) 0 (e+1) (e+1)
  generalize hr : subWords a b c ds es (0-(e+1)) (((e+1)<<<32)-1) 0 (e+1) (e+1) = output at hsub ⊢
  exact subtractQ_equation a b c d e ds es co (w5value output.1)
    output.2.toNat he hd hh hsub

private theorem qShift_value (e : Word) (he : e.toNat≤20) :
    ((e+1)<<<32).toNat=(e.toNat+1)*2^32 := by
  have hq : (e+1).toNat=e.toNat+1 := by
    simp only [BitVec.toNat_add,show (1 : Word).toNat=1 from rfl]
    omega_using [he]
  simp only [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,hq]
  omega_using [he]

private theorem tinyAdd_value (e : Word) (co : Bool) (he : e.toNat≤20) :
    (addCarry e 0 co).toNat=e.toNat+co.toNat := by
  have h := addCarry_value e 0 co
  have hc := Bool.toNat_le co
  have hl := (addCarry e 0 co).isLt
  change (addCarry e 0 co).toNat+2^64*(carryOut e 0 co).toNat=e.toNat+0+co.toNat at h
  omega_using [he, hc, h]

private theorem lowAdd_value (d x : Word) (n : Nat) (hx : x.toNat=n) :
    (addCarry d x false).toNat+2^64*(carryOut d x false).toNat=d.toNat+n := by
  have h := addCarry_value d x false
  simpa only [Bool.toNat_false,Nat.add_zero,hx] using h

private theorem prepareQ_value (d e : Word) (he : e.toNat≤20) :
    let q : Word := e+1
    let co := carryOut d (q<<<32) false
    let ds := addCarry d (q<<<32) false
    let es := addCarry e 0 co
    ds.toNat+2^64*co.toNat=d.toNat+(e.toNat+1)*2^32 ∧ es.toNat=e.toNat+co.toNat := by
  exact ⟨lowAdd_value d _ _ (qShift_value e he),tinyAdd_value e _ he⟩

theorem subQ_value (a b c d e : Word) (he : e.toNat≤20) :
    w5value (subQ a b c d e).1+(e.toNat+1)*p=
      five a b c d e+2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576*(subQ a b c d e).2.toNat := by
  let co := carryOut d ((e+1)<<<32) false
  let ds := addCarry d ((e+1)<<<32) false
  let es := addCarry e 0 co
  have hp := prepareQ_value d e he
  exact subQ_finish a b c d e ds es co he hp.1 hp.2

def correctionWords (a b c d e : Word) : Word × Word × Word × Word :=
  let w := (subQ a b c d e).1
  addBack w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2

theorem correctionWords_value (a b c d e : Word) (hn : five a b c d e<21*p) :
    let w:=correctionWords a b c d e;
    four w.1 w.2.1 w.2.2.1 w.2.2.2=five a b c d e%p := by
  have he : e.toNat≤20 := by
    simp only [five,p_value] at hn
    omega_using [hn]
  have hq : e.toNat=five a b c d e/2^256 := by
    have hl := four_lt a b c d
    simp only [five]
    omega_using [hl]
  have hv := subQ_value a b c d e he
  dsimp only [correctionWords]
  generalize hw : subQ a b c d e = result at hv ⊢
  obtain ⟨neg,hneg,hmod⟩ := correction_value (five a b c d e) e.toNat
    result.2.toNat result.1.1 result.1.2.1 result.1.2.2.1 result.1.2.2.2.1 result.1.2.2.2.2 hn hq hv
  rw [addBack_value _ _ _ _ _ neg hneg]
  exact hmod

end VG.Proof.P256.Linear

end

end


@[expose] public section

namespace VG.Proof.P256.Linear
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.P256.VerifySparse (four)

def correction : List Instr := ((Impl.P256.Linear.linear129 0 0 0).drop 52).take 20

private theorem correction_core (s : State) (hz : s.gpr .x17=0) :
    WP isa (.block correction) s fun t =>
      (t.gpr .x3,t.gpr .x4,t.gpr .x5,t.gpr .x6)=
        correctionWords (s.gpr .x3) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) ∧
      Keeps [.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x16] s t := by
  apply WP.of_runBlock
  simp only [correction,Impl.P256.Linear.linear129,List.drop_succ_cons,List.drop_zero,
    List.take_succ_cons,List.take_zero,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    RegUpd.gpr_write,RegUpd.c_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,
    BitVec.setWidth_eq,show 16*0<64 by decide,show 32<64 by decide,
    ite_true,ite_false,reduceCtorEq,hz,Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,rfl,rfl,rfl,rfl⟩
  · rfl
  · reg_keeps

theorem correction_ok (s : State) (hz : s.gpr .x17=0)
    (hn : regsVal s [.x3,.x4,.x5,.x6,.x7]<21*p) :
    WP isa (.block correction) s fun t =>
      regsVal t [.x3,.x4,.x5,.x6]=regsVal s [.x3,.x4,.x5,.x6,.x7]%p ∧
      Keeps [.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x16] s t := by
  have hs : regsVal s [.x3,.x4,.x5,.x6,.x7]=
      five (s.gpr .x3) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) := by
    simp only [regsVal,five,four,Nat.mul_zero,Nat.add_zero,Nat.mul_add,←Nat.mul_assoc,Nat.add_assoc]
  refine WP.mono (correction_core s hz) fun t ⟨he,hk⟩ => ⟨?_,hk⟩
  have ht : regsVal t [.x3,.x4,.x5,.x6]=four (t.gpr .x3) (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) := by
    simp only [regsVal,four,Nat.mul_zero,Nat.add_zero,Nat.mul_add,←Nat.mul_assoc]
  rw [ht,hs]
  change (let w:=(t.gpr .x3,t.gpr .x4,t.gpr .x5,t.gpr .x6);four w.1 w.2.1 w.2.2.1 w.2.2.2)=_
  rw [he]
  exact correctionWords_value _ _ _ _ _ (by rw [←hs]; exact hn)

end VG.Proof.P256.Linear
