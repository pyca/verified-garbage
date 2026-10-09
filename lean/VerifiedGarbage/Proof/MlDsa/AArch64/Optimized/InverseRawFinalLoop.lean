import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRawFinalSlice
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.SliceFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def rawFinalPassMem (m : Mem) (p : Addr) : Nat → Mem
  | 0 => m
  | u+1 => let prior := rawFinalPassMem m p u
           let base := p+BitVec.ofNat 64 (16*u)
           writeBank (rawFinalValues (readBank prior base 128)) base 128 prior

theorem rawFinalPass_frame {m : Mem} {p : Addr} {u : Nat} (hu : u≤8) :
    Frame [⟨p,1024⟩] m (rawFinalPassMem m p u) := by
  induction u with
  | zero => exact Frame.refl _ _
  | succ u ih =>
    simp only [rawFinalPassMem]
    apply writeBank_frame _ _ _ (r := ⟨p,1024⟩) (by simp) ?_ (ih (by omega))
    intro i
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact Offset.contains_base p (by omega) (by omega)

theorem rawFinalLoop_ok {s : State} (hf : FinalRoots s) (hs : ScaleRoots s)
    (hc : s.gpr .x12=8)
    (hr : ∀ u<8, ∀ i : Fin 8, InRegions (s.rd++s.wr)
      ((s.gpr .x2+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (128*i.val)) 16)
    (hw : ∀ u<8, ∀ i : Fin 8, InRegions s.wr
      ((s.gpr .x2+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (128*i.val)) 16) :
    WP isa (.loop (.block (rawFinalSliceCode++finalAdvance)) (.nonzero .x .x12)) s fun t =>
      Keep [.x2,.x12] s t ∧ (∀ r∈finalConstants, t.v r=s.v r) ∧
      t.gpr .x2=s.gpr .x2+128 ∧ t.mem=rawFinalPassMem s.mem (s.gpr .x2) 8 := by
  let I := fun u t => Keep [.x2,.x12] s t ∧ (∀ r∈finalConstants, t.v r=s.v r) ∧
    t.gpr .x2=s.gpr .x2+BitVec.ofNat 64 (16*u) ∧
    t.mem=rawFinalPassMem s.mem (s.gpr .x2) u
  apply VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N := 8) (by decide) (by decide) I ?_ ?_ hc
  · intro u hu t ht _
    rcases ht with ⟨hk,hv,hp,hm⟩
    have hft : FinalRoots t := by
      constructor
      · intro i
        rw [hv _ ((show ∀ i : Fin 7, finalRootReg i.val∈finalConstants by decide +kernel) i)]
        exact hf.root i
      · intro i
        rw [hv _ ((show ∀ i : Fin 7, finalRecipReg i.val∈finalConstants by decide +kernel) i)]
        exact hf.recip i
      · intro e he; rw [hv .v31 (by decide)]; exact hf.q e he
    have hst : ScaleRoots t := by simpa only [ScaleRoots,hv .v30 (by decide)] using hs
    refine rawFinalSlice_ok hft hst ?_ ?_ fun t₁ ⟨v,hvc,hvm⟩ => ?_
    · intro i; simpa only [hk.rd,hk.wr,hp] using hr u hu i
    · intro i; simpa only [hk.wr,hp] using hw u hu i
    · have hk₁ : Keep [] t t₁ := (hvc.keep.trans hvm.keep).mono
      refine WP.mono (finalAdvance_ok t₁) fun t₂ ⟨⟨⟨hp₂,hc₂,hm₂⟩,hk₂⟩,hv₂⟩ => ?_
      refine ⟨⟨((hk.trans hk₁).trans hk₂).mono,?_,?_,?_⟩,?_⟩
      · intro r hr
        rw [hv₂,hvm.v,hvc.get r ((show ∀ r∈finalConstants, r∉runRegs by decide) r hr)]
        exact hv r hr
      · rw [hp₂,hk₁.get .x2,hp]
        rw [show 16*(u+1)=16*u+16 by omega,BitVec.ofNat_add,BitVec.add_assoc]
        rfl
      · rw [hm₂,hvm.mem]
        simp only [rawFinalSliceMem,hm,hp,rawFinalPassMem]
      · rw [hc₂,hk₁.get .x12]; rfl
  · exact ⟨Keep.refl _ _,fun _ _ => rfl,by simp,rfl⟩

theorem rawFinalLoop_eq :
    .loop (.block VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.rawFinalBody) (.nonzero .x .x12)=
      (.loop (.block (rawFinalSliceCode++finalAdvance)) (.nonzero .x .x12) : Prog isa) := by
  rw [rawFinalBody_eq]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
