module

public import VerifiedGarbage.Proof.Bignum.Arm.PrepareAcceptedPrime
import VerifiedGarbage.Proof.Bignum.Arm.CrtAcceptanceCT
import VerifiedGarbage.Proof.Bignum.Arm.PreparePrimeCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimeAcceptance
import VerifiedGarbage.Proof.Bignum.Arm.StackCT

/-! # Neither factor validation nor acceptance changes the preparation trace -/

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
