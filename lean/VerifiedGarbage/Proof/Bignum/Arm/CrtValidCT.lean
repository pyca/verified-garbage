module

public import VerifiedGarbage.Proof.Bignum.Arm.WindowKernel

public import VerifiedGarbage.Proof.Bignum.Arm.CrtValidInput
import VerifiedGarbage.Proof.Bignum.Arm.CrtPrepareCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtValidateStageCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtComputeStageCT

/-! # The full private RSA path reveals no key, ciphertext, or rejection bit -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem crt_valid_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} (kernel : WindowKernel := baselineWindowKernel) :
    RelCT isa (fun s t => CrtValidInput g bs1 s ∧ CrtValidInput g bs2 t ∧ s.sp = t.sp)
      (CrtFn.validWith kernel.code) (fun _ _ => True) := by
  have prepare : RelCT isa (fun s t => CrtValidInput g bs1 s ∧ CrtValidInput g bs2 t ∧ s.sp = t.sp)
      CrtFn.prepare (fun _ _ => True) :=
    crt_prepare_ct.mono (fun _ _ h => ⟨h.1.prepare_input, h.2.1.prepare_input, h.2.2⟩) (fun _ _ _ => trivial)
  exact crt_seq_ct prepare (fun s h => crt_begin_selected s h) (fun s h => crt_begin_selected s h)
    (crt_seq_ct crt_validateStage_ct (fun s h => crt_validate_checked s h) (fun s h => crt_validate_checked s h)
      (crt_computeStage_ct (kernel := kernel)))

end VG.Proof.Bignum.Arm
