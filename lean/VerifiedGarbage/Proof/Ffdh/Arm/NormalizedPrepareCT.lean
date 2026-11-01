module

public import VerifiedGarbage.Impl.Ffdh.Arm.NormalizedPrepare
public import VerifiedGarbage.Proof.Ffdh.Arm.Prepare
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT

import VerifiedGarbage.Proof.Ffdh.Arm.PrepareCT
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Impl.Bignum.Arm.NormalizedPrecompute
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
import VerifiedGarbage.Proof.Bignum.Arm.NormalizedR2CT
import VerifiedGarbage.Proof.Bignum.Arm.ImportModulus
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeInverse
/-! # FFDH setup uses shared constant-time Montgomery precomputation -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/NormalizedPrecomputeCT.lean`, which only this module imported.
section

/-! # Shared modulus precomputation has a public trace -/

section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem normalizedPrecompute_ct {base src : BitVec 32} {len w k : Nat}
    {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (ct : TwoExp.MontgomeryTiming K)
    (countFits : 128 * w < 2 ^ 32) :
    RelCT isa (fun s t => (PrecomputeInput base src len w k s ∧ P s ∧ 2 ^ (64 * (w - 1)) ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)) ∧
      (PrecomputeInput base src len w k t ∧ P t ∧ 2 ^ (64 * (w - 1)) ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (State.addr src) k)) ∧ s.sp = t.sp)
      (NormalizedPrecompute.precompute K.op) (fun _ _ => True) := by
  have imported (s : State) (h : PrecomputeInput base src len w k s ∧ P s ∧ 2 ^ (64 * (w - 1)) ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)) :
      WP isa importModulus s fun t => PrecomputeModulus base len w t ∧ P t ∧ 2 ^ (64 * (w - 1)) ≤ Proof.Rsa.Mont.numAt t.mem (State.addr base) w 0 := by
    refine (importModulus_ready s h.1).and ?_
    refine WP.mono (importModulus_ok s h.1.workspace h.1.layout h.1.width h.1.positive h.1.fits h.1.sourceFits
      h.1.readable h.1.separate h.1.ptr h.1.source h.1.count h.1.stackRead h.1.stackSep h.1.saved) ?_
    rintro t ⟨_, _, _, modulus, frame, rest⟩
    exact ⟨K.stable frame rest h.2.1, by rw [modulus]; exact h.2.2⟩
  have inverse (s : State) (h : PrecomputeModulus base len w s ∧ P s ∧ 2 ^ (64 * (w - 1)) ≤ Proof.Rsa.Mont.numAt s.mem (State.addr base) w 0) :
      WP isa precomputeInverse s fun t => ArithmeticReady base len w t ∧ P t ∧ 2 ^ (64 * (w - 1)) ≤ Proof.Rsa.Mont.numAt t.mem (State.addr base) w 0 := by
    refine (precomputeInverse_ready s h.1).and ?_
    refine WP.mono (precomputeInverse_ok s h.1.workspace h.1.layout h.1.width h.1.ptr h.1.odd h.1.large
      h.1.stackRead h.1.stackSep h.1.saved) ?_
    rintro t ⟨_, modulus, frame, rest⟩
    exact ⟨K.stable frame rest h.2.1, by rw [modulus]; exact h.2.2⟩
  unfold NormalizedPrecompute.precompute
  refine relCT_chain ((importModulus_ct (base := base) (src := src) (len := len) (w := w) (k := k)).mono
    (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)) imported imported ?_
  exact relCT_chain ((precomputeInverse_ct (base := base) (len := len) (w := w)).mono
    (fun _ _ h => ⟨h.1.1, h.2.1.1⟩) (fun _ _ h => h)) inverse inverse (NormalizedR2.r2_ct K ct countFits)

end VG.Proof.Bignum.Arm
end

end

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
