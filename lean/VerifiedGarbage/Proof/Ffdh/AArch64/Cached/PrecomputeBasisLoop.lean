module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeBasis

/-! Four fixed public rounds finish all 32 canonical comb entries. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep count_loop)

private theorem basisCounterFlag : ∀ i<4,
 ((BitVec.ofNat 64 (2^((i+1)+1))-32#64).toNat≠0 ↔ i+1≠4) := by decide +kernel

theorem precomputeBasisLoop_ok (M : Mont) {s : State} {p : Parameters} (h : BasisState p 1 s) :
 WP isa (.loop (Precompute.basis M.mm) (.nonzero .x .x3)) s fun t =>
 BasisState p 5 t ∧ BuildFrame p s.mem t.mem ∧ Keep mmRegs s t := by
 let I := fun i t => BasisState p (i+1) t ∧ BuildFrame p s.mem t.mem ∧ Keep mmRegs s t
 refine WP.mono (count_loop (by decide : 0<4) I (fun i hi t inv => ?_)
  ⟨h,Frame.refl _ _,Keep.refl _ _⟩) ?_
 · refine WP.mono (precomputeBasis_ok M inv.1 (by omega : i+1<5)) ?_
   rintro u ⟨state,index,frame,rest⟩
   refine ⟨⟨state,inv.2.1.trans frame,(inv.2.2.trans rest).mono (by simp [mmRegs])⟩,?_⟩
   rw [index]
   exact basisCounterFlag i hi
 · rintro t ⟨state,frame,rest⟩
   exact ⟨state,frame,rest⟩

end VG.Proof.Ffdh.AArch64.Cached
