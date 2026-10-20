module

public import VerifiedGarbage.Impl.Ffdh.Arm.NormalizedPrepare
public import VerifiedGarbage.Proof.Ffdh.Arm.Prepare
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareCT
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Bignum.Arm.NormalizedPrecomputeCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT

/-! # FFDH setup uses shared constant-time Montgomery precomputation -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem normalizedPrepare_ct {base src : BitVec 32} {len k : Nat}
    {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len (Spec.Rsa.modulusWords k) P regions)
    (ct : TwoExp.MontgomeryTiming K) (countFits : 128 * Spec.Rsa.modulusWords k < 2 ^ 32) :
    RelCT isa (fun s t => (PrepareInput base src len k s ∧ P s ∧ 2 ^ (64 * (Spec.Rsa.modulusWords k - 1)) ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)) ∧
      (PrepareInput base src len k t ∧ P t ∧ 2 ^ (64 * (Spec.Rsa.modulusWords k - 1)) ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (State.addr src) k)) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.NormalizedPrepare.code K.op) (fun _ _ => True) := by
  have ready (s : State) (h : PrepareInput base src len k s ∧ P s ∧ 2 ^ (64 * (Spec.Rsa.modulusWords k - 1)) ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)) :
      WP isa VG.Impl.Bignum.Arm.PublicFn.prepare s fun t =>
        PrecomputeInput base src len (Spec.Rsa.modulusWords k) k t ∧ P t ∧ 2 ^ (64 * (Spec.Rsa.modulusWords k - 1)) ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (State.addr src) k) :=
    by
    refine WP.mono (prepare_input s h.1) ?_
    rintro t ⟨ready, frame, rest⟩
    have bytes := rsa_bytes_frame (src := State.addr src) (k := k) frame
      (by have := h.1.maxLength; omega) (by simpa using h.1.separate)
    exact ⟨ready, K.stable frame rest h.2.1, by rw [bytes]; exact h.2.2⟩
  unfold VG.Impl.Ffdh.Arm.NormalizedPrepare.code
  exact relCT_chain (prepareInput_ct.mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h))
    ready ready (normalizedPrecompute_ct K ct countFits)

end VG.Proof.Ffdh.Arm
