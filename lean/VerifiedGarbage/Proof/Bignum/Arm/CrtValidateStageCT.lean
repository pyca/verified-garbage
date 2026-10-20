module
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT

import VerifiedGarbage.Proof.Bignum.Arm.CrtValidationStagesCT
import VerifiedGarbage.Proof.Bignum.Arm.MergeAcceptanceCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtValidateProductCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtValidationGeometry
import VerifiedGarbage.Proof.Bignum.Arm.CrtLoadQStage
import VerifiedGarbage.Proof.Bignum.Arm.CrtLoadPStage
import VerifiedGarbage.Proof.Bignum.Arm.CrtAcceptStage
import VerifiedGarbage.Proof.Bignum.Arm.StackCT

/-! # The complete private key validation leaks no secret validation result -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_productStage_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => CrtSelected g bs1 g.base s ∧ CrtSelected g bs2 g.base t ∧ s.sp = t.sp)
      (.seq validateProduct (.block mergeAcceptance)) (fun _ _ => True) := by
  have product : RelCT isa (fun s t => CrtSelected g bs1 g.base s ∧ CrtSelected g bs2 g.base t ∧ s.sp = t.sp)
      validateProduct (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    have fit := (h.1.1.compare_input h.1.2).fit
    exact crt_validateProduct_ct fit s t tr1 tr2 u v
      ⟨h.1.1.validate_input h.1.2, h.2.1.1.validate_input h.2.1.2, h.2.2⟩ e1 e2
  exact (relCT_keep_sp product (fun _ _ h => h.2.2)).seq mergeAcceptance_ct

theorem crt_validateStage_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => CrtSelected g bs1 g.base s ∧ CrtSelected g bs2 g.base t ∧ s.sp = t.sp)
      CrtFn.validate (fun _ _ => True) := by
  have acceptWP (s : State) {bs : Fin 7 → List Byte} (h : CrtSelected g bs g.base s) :
      WP isa CrtFn.acceptInput s (CrtSelected g bs g.base) :=
    (crt_acceptStage_ok s h.1 h.2).mono (fun _ j => ⟨j.1, j.2.1⟩)
  have pWP (s : State) {bs : Fin 7 → List Byte} (h : CrtSelected g bs g.base s) :
      WP isa CrtFn.loadP s (CrtSelected g bs g.base) :=
    (crt_loadPStage_ok s h.1 h.2).mono (fun _ j => ⟨j.1, j.2.1⟩)
  have qWP (s : State) {bs : Fin 7 → List Byte} (h : CrtSelected g bs g.base s) :
      WP isa CrtFn.loadQ s (CrtSelected g bs g.base) :=
    (crt_loadQStage_ok s h.1 h.2).mono (fun _ j => ⟨j.1, j.2.1⟩)
  exact crt_seq_ct crt_acceptStage_ct (fun s h => acceptWP s h) (fun s h => acceptWP s h)
    (crt_seq_ct crt_loadPStage_ct (fun s h => pWP s h) (fun s h => pWP s h)
      (crt_seq_ct crt_loadQStage_ct (fun s h => qWP s h) (fun s h => qWP s h) crt_productStage_ct))

end VG.Proof.Bignum.Arm
