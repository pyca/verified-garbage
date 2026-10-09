import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InnerTraversal
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InnerRun

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- Logical bank lanes represent the corresponding strided field coefficients. -/
def InnerBankField (u : Nat) (v : Vector (BitVec 128) 8) (w : Poly) : Prop :=
  ∀ i : Fin 8, ∀ e<4, ofInt (vword v[i.val] e).toInt=w[Traversal.innerLoc u i.val e]!

theorem innerCoreValues_field (v : Vector (BitVec 128) 8) (w : Poly) {gap g u : Nat}
    (hg : ValidGroup gap g) (hu : u<8) (rootIndex : Nat) {b : Int}
    (hb : 0≤b) (hs : b+16760834<2147483648) (hv : BankBound v b) (hf : InnerBankField u v w) :
    InnerBankField u (coreValues v gap g (fun _ => (zetaNat rootIndex : Int)))
      (Traversal.run (Traversal.innerRegGroupSchedule u (2*gap*g) gap rootIndex) w) := by
  intro i e he
  rw [coreValues_int v hg _ hb hs hv i he,Traversal.run_innerRegGroup,
    Traversal.innerRegBlock_get _ hg.bounds.1 hg.bounds.2 hu (Nat.le_refl _) _ i.isLt he,
    show 2*gap*g+gap+gap=2*gap*g+2*gap by omega]
  by_cases hl : 2*gap*g≤i.val ∧ i.val<2*gap*g+gap
  · rw [ite_eq_left hl,ite_eq_left hl,ofInt_add,fastMul_field,Traversal.ofInt_zetaNat,hf i e he]
    have hidx : i.val+gap<8 := by have := hg.bounds.2; omega
    have hae : v[i.val+gap]! = v[i.val+gap] := getElem!_pos v _ hidx
    rw [hae,hf ⟨i.val+gap,hidx⟩ e he,Fin.mul_comm]
  · rw [ite_eq_right hl,ite_eq_right hl]
    by_cases hr : 2*gap*g+gap≤i.val ∧ i.val<2*gap*g+2*gap
    · rw [ite_eq_left hr,ite_eq_left hr,ofInt_sub,fastMul_field,Traversal.ofInt_zetaNat,hf i e he]
      have hidx : i.val-gap<8 := by omega
      have hae : v[i.val-gap]! = v[i.val-gap] := getElem!_pos v _ hidx
      rw [hae,hf ⟨i.val-gap,hidx⟩ e he,Fin.mul_comm]
    · rw [ite_eq_right hr,ite_eq_right hr,hf i e he]


def innerGroupSchedule (u : Nat) (root : Nat → Nat → Nat) (p : Nat × Nat) : List Traversal.Op :=
  Traversal.innerRegGroupSchedule u (2*p.1*p.2) p.1 (root p.1 p.2)

theorem innerValues_field (v : Vector (BitVec 128) 8) (w : Poly) (ps : List (Nat × Nat))
    (hps : ∀ p∈ps,ValidGroup p.1 p.2) (root : Nat → Nat → Nat) {u : Nat} (hu : u<8) {b : Int}
    (hb : 0≤b) (hs : b+16760834*(ps.length : Int)<2147483648)
    (hv : BankBound v b) (hf : InnerBankField u v w) :
    BankBound (innerValues v (fun gap g _ => (zetaNat (root gap g) : Int)) ps)
      (b+16760834*(ps.length : Int)) ∧
    InnerBankField u (innerValues v (fun gap g _ => (zetaNat (root gap g) : Int)) ps)
      (Traversal.run (ps.flatMap (innerGroupSchedule u root)) w) := by
  induction ps generalizing v w b with
  | nil => simpa only [innerValues,List.length_nil,Int.natCast_zero,Int.mul_zero,Int.add_zero,
      List.flatMap_nil,Traversal.run,List.foldl_nil] using And.intro hv hf
  | cons p ps ih =>
    have hp := hps p (by simp)
    have hs' : b+16760834<2147483648 := by
      simp only [List.length_cons,Int.natCast_add,Int.natCast_one] at hs; omega
    have hb' := coreValues_bound v hp (fun _ => (zetaNat (root p.1 p.2) : Int)) hb hs' hv
    have hf' := innerCoreValues_field v w hp hu (root p.1 p.2) hb hs' hv hf
    have hh := ih (coreValues v p.1 p.2 (fun _ => (zetaNat (root p.1 p.2) : Int)))
      (Traversal.run (innerGroupSchedule u root p) w) (fun a ha => hps a (by simp [ha]))
      (b := b+16760834) (by omega) (by
        simp only [List.length_cons,Int.natCast_add,Int.natCast_one] at hs
        omega) hb' hf'
    simpa only [innerValues,List.length_cons,Int.natCast_add,Int.natCast_one,List.flatMap_cons,
      Traversal.run_append,show b+16760834*((ps.length : Int)+1)=
        (b+16760834)+16760834*(ps.length : Int) by omega] using hh

end VG.Proof.MlDsa.AArch64.Optimized
