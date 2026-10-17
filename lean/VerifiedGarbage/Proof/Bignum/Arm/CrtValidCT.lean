module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtValidInput
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPrepareCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtValidateStageCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtComputeStageCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The full private RSA path reveals no key, ciphertext, or rejection bit -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem crt_valid_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => CrtValidInput g bs1 s ∧ CrtValidInput g bs2 t ∧ s.sp = t.sp)
      CrtFn.valid (fun _ _ => True) := by
  have prepare : RelCT isa (fun s t => CrtValidInput g bs1 s ∧ CrtValidInput g bs2 t ∧ s.sp = t.sp)
      CrtFn.prepare (fun _ _ => True) :=
    crt_prepare_ct.mono (fun _ _ h => ⟨h.1.prepare_input, h.2.1.prepare_input, h.2.2⟩) (fun _ _ _ => trivial)
  exact crt_seq_ct prepare (fun s h => crt_begin_selected s h) (fun s h => crt_begin_selected s h)
    (crt_seq_ct crt_validateStage_ct (fun s h => crt_validate_checked s h) (fun s h => crt_validate_checked s h)
      crt_computeStage_ct)

end VG.Proof.Bignum.Arm
