module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicPrecomputeKernel
public import VerifiedGarbage.Proof.Bignum.Arm.PcPrepare

import VerifiedGarbage.Proof.Bignum.Arm.PcPrepareCT
import VerifiedGarbage.Proof.Bignum.Arm.PcComputed
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOutCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT

/-! # Successful public precomputation has no secret-dependent trace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem pcValid_ct {base dst src : BitVec 32} {len k : Nat} {nb : List Byte} (hk : k ≤ 1024)
    (kernel : PublicPrecomputeKernel := baselinePublicPrecomputeKernel) : RelCT isa (fun s t =>
      (PcValidInput base dst src len k s ∧ Spec.Rsa.bytesAt s.mem (State.addr src) k = nb) ∧
      (PcValidInput base dst src len k t ∧ Spec.Rsa.bytesAt t.mem (State.addr src) k = nb) ∧ s.sp = t.sp)
      (PcFn.validWith kernel.code) (fun _ _ => True) := by
  have countFit : 128 * Spec.Rsa.modulusWords k < 2 ^ 32 := by
    simp only [Spec.Rsa.modulusWords]; omega
  have prepared := (relCT_keep_sp ((pcPrepare_ct (base := base) (dst := dst) (src := src) (len := len) (k := k)).mono
    (P' := fun (s t : State) =>
      (PcValidInput base dst src len k s ∧ Spec.Rsa.bytesAt s.mem (State.addr src) k = nb) ∧
      (PcValidInput base dst src len k t ∧ Spec.Rsa.bytesAt t.mem (State.addr src) k = nb) ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => True.intro)) (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨pcPrepare_public_ready s h.1.1 h.1.2, pcPrepare_public_ready t h.2.1.1 h.2.1.2⟩)
  have arithmetic := (relCT_keep_sp ((kernel.ct (nb := nb) countFit).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧
      (PcPrepared base dst src len k s ∧ Spec.Rsa.bytesAt s.mem (State.addr src) k = nb) ∧
      (PcPrepared base dst src len k t ∧ Spec.Rsa.bytesAt t.mem (State.addr src) k = nb))
    (fun _ _ h => ⟨⟨h.2.1.1.input, h.2.1.2⟩, ⟨h.2.2.1.input, h.2.2.2⟩, h.1⟩)
    (fun _ _ h => h)) (fun _ _ h => h.1)).wp
    (fun s t h => ⟨pcComputed_ready s h.2.1.1 (kernel := kernel),
      pcComputed_ready t h.2.2.1 (kernel := kernel)⟩)
  have output := ((loadStack_ct .r4 4).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ PcComputed base dst src len k s ∧ PcComputed base dst src len k t)
    (fun _ _ h => h.1) (fun _ _ _ => True.intro)).wp
    (fun s t h => ⟨pcExport_ready s h.2.1, pcExport_ready t h.2.2⟩)
  have tail := arithmetic.seq ((output.mono (fun _ _ h => h) (fun _ _ h => h.2)).seq precomputeOut_ct)
  have all := prepared.seq tail
  intro s t tr1 tr2 u v h e1 e2
  cases e1 with
  | seq a1 b1 =>
    cases b1 with
    | seq b1 c1 =>
      cases c1 with
      | seq c1 d1 =>
        cases e2 with
        | seq a2 b2 =>
          cases b2 with
          | seq b2 c2 =>
            cases c2 with
            | seq c2 d2 =>
              obtain ⟨trace, post⟩ := all _ _ _ _ _ _ h
                (.seq (.seq a1 (.seq b1 c1)) d1) (.seq (.seq a2 (.seq b2 c2)) d2)
              exact ⟨by simpa only [List.append_assoc] using trace, post⟩

end VG.Proof.Bignum.Arm
