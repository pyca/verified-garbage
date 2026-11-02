module

public import VerifiedGarbage.Proof.Bignum.Arm.PrepareAcceptedPrime

import VerifiedGarbage.Proof.Bignum.Arm.CrtAcceptanceCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimeAcceptance
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.PreparePrime
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
import VerifiedGarbage.Proof.Bignum.Arm.R2CT
import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulus
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
/-! # Neither factor validation nor acceptance changes the preparation trace -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/PreparePrimeCT.lean`, which only this module imported.
section

/-! # Secret-factor preparation has only public workspace-dependent traces -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)

theorem sanitizeModulus_ready (s : State) {base : BitVec 32} {len w : Nat}
    (h : PrimeInput base len w s) : WP isa sanitizeModulus s (PrecomputeModulus base len w) := by
  refine WP.mono (sanitizeModulus_ok s h.workspace h.layout h.width h.ptr h.bit h.stackRead h.stackSep h.saved) ?_
  rintro t ⟨layout, width, value, _, frame, rest, ptr⟩
  have valid := safePrime_valid h.valid
  change numAt t.mem (State.addr base) w 0 = safePrime _ _ at value
  refine ⟨⟨h.workspace.congr rest.wr, layout, width, ptr, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead
  · rw [rest.sp]; exact h.stackSep
  · exact saved_base_kept frame h.stackSep h.saved rest.sp
  · rw [value]; exact valid.1
  · rw [value]; exact valid.2

theorem preparePrime_ct {base : BitVec 32} {len w : Nat} (countFits : 128 * w < 2 ^ 32) :
    RelCT isa (fun s t => PrimeInput base len w s ∧ PrimeInput base len w t ∧ s.sp = t.sp)
      preparePrime (fun _ _ => True) := by
  have sanitize := (sanitizeModulus_ct (base := base) (len := len) (w := w)).mono
    (P' := fun (s t : State) => PrimeInput base len w s ∧ PrimeInput base len w t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.toLayoutFrameReady, h.2.1.toLayoutFrameReady, h.2.2⟩) (fun _ _ _ => trivial)
  have first := (relCT_keep_sp sanitize (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨sanitizeModulus_ready s h.1, sanitizeModulus_ready t h.2.1⟩)
  have inverse := relCT_keep_sp ((precomputeInverse_ct (base := base) (len := len) (w := w)).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ PrecomputeModulus base len w s ∧ PrecomputeModulus base len w t)
    (fun _ _ h => h.2) (fun _ _ h => h)) (fun _ _ h => h.1)
  have ready := inverse.wp (fun s t h => ⟨precomputeInverse_ready s h.2.1, precomputeInverse_ready t h.2.2⟩)
  exact first.seq ((ready.mono (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩)).seq (r2_ct countFits))

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt

theorem prepareAcceptedPrime_ct {base : BitVec 32} {len w : Nat} (countFits : 128 * w < 2 ^ 32) :
    RelCT isa (fun s t => AcceptedPrimeInput base len w s ∧ AcceptedPrimeInput base len w t ∧ s.sp = t.sp)
      prepareAcceptedPrime (fun _ _ => True) := by
  let P := AcceptedPrimeInput base len w
  have install : RelCT isa (fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
      (.block installAcceptance) (fun _ _ => True) :=
    crt_installAcceptance_ct.mono (fun _ _ h => ⟨h.1.ptr.trans h.2.1.ptr.symm, h.2.2⟩) (fun _ _ _ => trivial)
  have ready := (relCT_keep_sp install (fun _ _ h => h.2.2)).wp (fun s t h =>
    ⟨(crt_primeAcceptance_ready s h.1.toLayoutFrameReady h.1.stackFit h.1.flagRead h.1.bit h.1.valid).mono
      (fun _ j => j.1),
      (crt_primeAcceptance_ready t h.2.1.toLayoutFrameReady h.2.1.stackFit h.2.1.flagRead h.2.1.bit h.2.1.valid).mono
      (fun _ j => j.1)⟩)
  exact ready.seq ((preparePrime_ct countFits).mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial))

end VG.Proof.Bignum.Arm
