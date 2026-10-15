module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtValidationInputs
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSelectStageCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtAcceptInputCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtLoadPBodyCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtValidateProductCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The private RSA validation stages hide all key and ciphertext bytes -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_acceptStage_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => CrtSelected g bs1 g.base s ∧ CrtSelected g bs2 g.base t ∧ s.sp = t.sp)
      CrtFn.acceptInput (fun _ _ => True) :=
  crt_acceptInput_ct.mono (fun _ _ h => ⟨h.1.accept_input, h.2.1.accept_input, h.2.2⟩) (fun _ _ _ => trivial)

theorem crt_loadPStage_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => CrtSelected g bs1 g.base s ∧ CrtSelected g bs2 g.base t ∧ s.sp = t.sp)
      CrtFn.loadP (fun _ _ => True) := by
  have body : RelCT isa (fun s t => CrtSelected g bs1 (crtP g.base g.words) s ∧
      CrtSelected g bs2 (crtP g.base g.words) t ∧ s.sp = t.sp) CrtFn.loadPBody (fun _ _ => True) :=
    crt_loadPBody_ct.mono (fun _ _ h => ⟨h.1.loadP_input, h.2.1.loadP_input, h.2.2⟩) (fun _ _ _ => trivial)
  exact crt_seq_ct (crt_select_stage_ct 224) (fun s h => crt_selectP_stage s h) (fun s h => crt_selectP_stage s h)
    ((relCT_keep_sp body (fun _ _ h => h.2.2)).seq crt_selectMain_ct)

theorem crt_loadQStage_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => CrtSelected g bs1 g.base s ∧ CrtSelected g bs2 g.base t ∧ s.sp = t.sp)
      CrtFn.loadQ (fun _ _ => True) := by
  have load : RelCT isa (fun s t => CrtSelected g bs1 (crtQ g.base g.words) s ∧
      CrtSelected g bs2 (crtQ g.base g.words) t ∧ s.sp = t.sp) (savedOperand 0 72 76) (fun _ _ => True) :=
    (savedOperandLayout_ct (by decide : 0 < 8)).mono
      (fun _ _ h => ⟨⟨h.1.2, h.1.1.savedOperand 2 (by simp [crtRegions])⟩,
        ⟨h.2.1.2, h.2.1.1.savedOperand 2 (by simp [crtRegions])⟩, h.2.2⟩) (fun _ _ _ => trivial)
  exact crt_seq_ct (crt_select_stage_ct 228) (fun s h => crt_selectQ_stage s h) (fun s h => crt_selectQ_stage s h)
    ((relCT_keep_sp load (fun _ _ h => h.2.2)).seq crt_selectMain_ct)

end VG.Proof.Bignum.Arm
