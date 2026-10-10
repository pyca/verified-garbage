import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Representation
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Word
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TailBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TailRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveCore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableMemory

/-! ## From `Mem.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith

theorem positiveWord_field (x : BitVec 32) :
    ofNat (positiveWord x).toNat = ofInt x.toInt := by
  have hp := positive_bounds (BitVec.le_toInt x) (BitVec.toInt_lt (x := x))
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [val_ofNat, Int.natCast_emod, positiveWord_nat,
    Int.toNat_of_nonneg (by omega), VG.Proof.MlDsa.KeyGen.ofInt_val]
  exact positive_mod _

/-- Normalizing signed representatives changes the internal storage relation,
not the polynomial represented by memory. No canonical-output claim is made. -/
theorem SignedPolyIs.positive {m m' : Mem} {p p' : Addr} {f : Poly} {lo hi : Int}
    (h : SignedPolyIs m p f lo hi)
    (hw : ∀ i < n, coeffAt m' p' i = positiveWord (coeffAt m p i)) :
    PosPolyIs m' p' f := by
  constructor
  · intro i hn
    rw [hw i hn, positiveWord_nat]
    have hp := positive_lt_three_q (BitVec.le_toInt (coeffAt m p i))
      (BitVec.toInt_lt (x := coeffAt m p i))
    omega
  · apply ext_getElem!
    intro i hn
    rw [polyAt_get _ _ hn, hw i hn, positiveWord_field]
    exact h.value i hn

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `TailValues.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def tailGroupSchedule (u : Nat) (root : Nat → Nat → Nat → Nat) (p : Fin 4 × Nat) : List Traversal.Op :=
  Traversal.packedSchedule (32*u+8*p.1.val) p.2 (root p.1.val p.2)

theorem tailValues_field (v : Vector (BitVec 128) 8) (w : Poly) (ps : List (Fin 4 × Nat))
    (hps : ∀ p∈ps,p.2=1 ∨ p.2=2) (root : Nat → Nat → Nat → Nat) {u : Nat} (hu : u<8) {b : Int}
    (hb : 0≤b) (hs : b+16760834*(ps.length : Int)<2147483648)
    (hv : BankBound v b) (hf : InnerBankField u v w) :
    BankBound (tailValues v (fun g len e => (zetaNat (root g len e) : Int)) ps)
      (b+16760834*(ps.length : Int)) ∧
    InnerBankField u (tailValues v (fun g len e => (zetaNat (root g len e) : Int)) ps)
      (Traversal.run (ps.flatMap (tailGroupSchedule u root)) w) := by
  induction ps generalizing v w b with
  | nil => simpa only [tailValues,List.length_nil,Int.natCast_zero,Int.mul_zero,Int.add_zero,
      List.flatMap_nil,Traversal.run,List.foldl_nil] using And.intro hv hf
  | cons p ps ih =>
    have hp := hps p (by simp)
    have hs' : b+16760834<2147483648 := by
      simp only [List.length_cons,Int.natCast_add,Int.natCast_one] at hs; omega
    have hb' := packedValues_bound v p.1.isLt hp (fun e => (zetaNat (root p.1.val p.2 e) : Int)) hb hs' hv
    have hf' := packedValues_field v w p.1.isLt hp hu (root p.1.val p.2) hb hs' hv hf
    have hh := ih _ (Traversal.run (tailGroupSchedule u root p) w)
      (fun a ha => hps a (by simp [ha])) (b := b+16760834) (by omega) (by
        simp only [List.length_cons,Int.natCast_add,Int.natCast_one] at hs
        omega) hb' hf'
    simpa only [tailValues,List.length_cons,Int.natCast_add,Int.natCast_one,List.flatMap_cons,
      Traversal.run_append,show b+16760834*((ps.length : Int)+1)=
        (b+16760834)+16760834*(ps.length : Int) by omega] using hh

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `FiveTraversal.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def innerRootIndex (u gap g : Nat) : Nat :=
  if gap=4 then 8+u else if gap=2 then 16+2*u+g else 32+4*u+g

def tailRootIndex (u g len e : Nat) : Nat :=
  if len=2 then 64+8*u+2*g+e/2 else 128+16*u+4*g+e

theorem inner_schedule (u : Nat) :
    outerSteps.flatMap (innerGroupSchedule u (innerRootIndex u)) ++
      tailSteps.flatMap (tailGroupSchedule u (tailRootIndex u))=Traversal.innerSlice u := by
  simp [outerSteps,tailSteps,innerGroupSchedule,tailGroupSchedule,innerRootIndex,tailRootIndex,
    Traversal.innerRegGroupSchedule,Traversal.packedSchedule,Traversal.innerSlice,Traversal.innerLoc,
    show (3:Fin 4).val=3 from rfl,List.range_succ,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  omega

theorem fiveValues_field (v : Vector (BitVec 128) 8) (w : Poly) {u : Nat} (hu : u<8)
    (hv : BankBound v (15*8380417)) (hf : InnerBankField u v w) :
    (∀ i : Fin 8, ∀ e<4, (vword (fiveValues v (innerRoot u) (tailRoot u))[i.val] e).toNat<3*8380417) ∧
    (∀ i : Fin 8, ∀ e<4, ofNat (vword (fiveValues v (innerRoot u) (tailRoot u))[i.val] e).toNat=
      (Traversal.run (Traversal.innerSlice u) w)[Traversal.innerLoc u i.val e]!) := by
  have hi := innerValues_field v w outerSteps outerSteps_valid (innerRootIndex u) hu
    (by decide) (by decide) hv hf
  have ht := tailValues_field _ _ tailSteps tailSteps_valid (tailRootIndex u) hu
    (by decide) (by decide) hi.1 hi.2
  have hei : (fun gap g _ => (zetaNat (innerRootIndex u gap g) : Int))=innerRoot u := rfl
  have het : (fun g len e => (zetaNat (tailRootIndex u g len e) : Int))=tailRoot u := rfl
  rw [hei,het,← Traversal.run_append,inner_schedule] at ht
  constructor
  · intro i e he
    simp only [fiveValues,Vector.getElem_map,positiveVector_word _ he,positiveWord_nat]
    have hb := positive_lt_three_q
      (BitVec.le_toInt (vword (tailValues (innerValues v (innerRoot u) outerSteps) (tailRoot u) tailSteps)[i.val] e))
      (BitVec.toInt_lt (x := vword (tailValues (innerValues v (innerRoot u) outerSteps) (tailRoot u) tailSteps)[i.val] e))
    simp only [q] at hb
    omega
  · intro i e he
    simp only [fiveValues,Vector.getElem_map,positiveVector_word _ he,positiveWord_field]
    exact ht.2 i e he

end VG.Proof.MlDsa.AArch64.Optimized

end
