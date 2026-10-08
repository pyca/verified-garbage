import VerifiedGarbage.Proof.P256.Linear.Words

namespace VG.Proof.P256.Linear
open VG VG.Proof.Ed25519 VG.Proof.Mont.AArch64
open VG.Proof.P256.VerifySparse (four addFour_value)

private theorem mod_of_eq (out n q carry : Nat)
    (h : out+(q+1)*p=n+2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576*carry) :
    (out : Int)%(2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576:Int)=
      ((n:Int)-((q:Int)+1)*(p:Int))%(2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576:Int) := by
  have he : (out:Int)=(n:Int)-((q:Int)+1)*(p:Int)+(2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576:Int)*(carry:Int) := by
    simp only [p_value] at h ⊢
    omega
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
    simp only [BitVec.toNat_add,show (1 : BitVec 64).toNat=1 from rfl]; omega
  have es : ((e+1)<<<32).toNat=(e.toNat+1)*2^32 := by
    simp only [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,eq]; omega
  have ex : (0-(e+1)).toNat=2^64-(e.toNat+1) := by
    simp only [BitVec.toNat_sub,show (0 : BitVec 64).toNat=0 from rfl,eq]; omega
  have ey : ((e+1)<<<32-1).toNat=(e.toNat+1)*2^32-1 := by
    simp only [BitVec.toNat_sub,show (1 : BitVec 64).toNat=1 from rfl,es]; omega
  simp only [five,four,ex,ey,eq,show (0 : BitVec 64).toNat=0 from rfl] at hsub
  simp only [five,four,p_value]
  omega

/-- A signed residual of magnitude below p has only zero or all-ones above bit255. -/
theorem remainder_shape (lo hi : Nat) (d : Int)
    (hlo : lo<2^256) (hhi : hi<2^64) (hd0 : -(p:Int)≤d) (hd1 : d<(p:Int))
    (h : ((lo:Int)+(2^256:Int)*(hi:Int))%(2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576:Int)=d%(2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576:Int)) :
    hi=(if d<0 then 2^64-1 else 0) ∧
      (lo:Int)=(if d<0 then (2^256:Int)+d else d) := by
  simp only [p_value] at hd0 hd1
  by_cases hz : d<0
  · rw [ite_eq_left hz,ite_eq_left hz]
    omega
  · rw [ite_eq_right hz,ite_eq_right hz]
    omega


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
    omega
  · simp only [hd,decide_false,Bool.false_eq_true,ite_false,Nat.add_zero] at hs hc ⊢
    omega

/-- The estimated quotient plus signed correction produces the canonical residue. -/
theorem correction_value (n q borrow : Nat) (a b c d e : BitVec 64)
    (hn : n<21*p) (hq : q=n/2^256)
    (hv : five a b c d e+(q+1)*p=n+2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576*borrow) :
    ∃ neg : Bool, e=(if neg then -1 else 0) ∧
      (four a b c d+(if neg then p else 0))%2^256=n%p := by
  have hmod := mod_of_eq (five a b c d e) n q borrow hv
  have hh := quotient_bounds (n:Int) (by simp only [p_value]; omega)
    (by simp only [p_value] at hn ⊢; omega)
  have hq' : (q:Int)=(n:Int)/(radix:Int) := by
    simp only [radix] at *
    omega
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
  have hc := corrected_mod (n:Int) (by simp only [p_value]; omega)
    (by simp only [p_value] at hn ⊢; omega)
  rw [←hq'] at hc
  change (if delta<0 then delta+(p:Int) else delta)=(n:Int)%(p:Int) at hc
  apply finish_value (four a b c d) n delta hshape.2
  simpa only [Int.natCast_emod] using hc


end VG.Proof.P256.Linear
