module

import VerifiedGarbage.Proof.Ffdh.Arm.ExportResult
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.KeyMemory
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyOutputsCT
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeFinishCT
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.ExportResultCT

/-! Public-value export and final key masking have a fixed trace for every
secret exponent and result flag. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (numAt)

structure KeyExportInput (p : Inputs) (slots : List Nat) (s : State) : Prop where
  context : Context p slots s
  ready : ArithmeticReady p.base p.len p.w s
  outputs : KeyOutputs p s
  valueFit : numAt s.mem (State.addr p.base) p.w 6 < 2 ^ (8 * p.k)

theorem keySave_next (s : State) {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (outputY : p.output = p.publicValue) (h : KeyExportInput p slots s) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.Exchange.saveResult) s (KeyExportInput p slots) := by
  have exchange : ExchangeFinishInput p slots s :=
    ⟨h.context, h.ready, by rw [outputY]; exact h.outputs.publicBuffer,
      by rw [outputY]; exact h.outputs.publicWorkspace.symm,
      by rw [outputY]; exact h.outputs.publicStack, h.valueFit⟩
  refine WP.mono (withAllRest (exchangeSave_ready s exchange stable saved)) ?_
  rintro t ⟨result, rest⟩
  exact ⟨result.context, result.ready, h.outputs.after rest, result.valueFit⟩

theorem keyExport_next (s : State) {p : Inputs} {slots : List Nat}
    (saved : ∀ d ∈ slots, d + 4 ≤ 72) (h4 : 4 ∈ slots) (h32 : 32 ∈ slots)
    (outputY : p.output = p.publicValue) (h : KeyExportInput p slots s) :
    WP isa VG.Impl.Ffdh.Arm.Domain.Exchange.exportResult s (KeyOutputState p slots) := by
  refine WP.mono (exportResult_ok s h.context h4 h32 h.ready
    (by rw [outputY]; exact h.outputs.publicBuffer) (by rw [outputY]; exact h.outputs.publicWorkspace.symm) h.valueFit) ?_
  rintro t ⟨_, frame, rest⟩
  rw [outputY] at frame
  exact ⟨h.context.toArgumentMemory.after_output frame rest h.outputs.publicDomain h.outputs.publicStack saved,
    h.outputs.after rest⟩

theorem keyExportFinish_ct {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h4 : 4 ∈ slots) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d) (outputY : p.output = p.publicValue) :
    RelCT isa (fun s t => KeyExportInput p slots s ∧ KeyExportInput p slots t ∧ s.sp = t.sp)
      (.seq (.block VG.Impl.Ffdh.Arm.Domain.Exchange.saveResult)
        (.seq VG.Impl.Ffdh.Arm.Domain.Exchange.exportResult VG.Impl.Ffdh.Arm.Domain.GenerateKey.finish)) (fun _ _ => True) := by
  have bounds (d : Nat) (hd : d ∈ slots) := (stableSlots_at stable hd).1
  have save := (RelCT.block_append (stackAddr_ct.seq (storeLocal_ct .r11 64))).mono
    (P' := fun (s t : State) => KeyExportInput p slots s ∧ KeyExportInput p slots t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have exportCT := (exportResult_ct h4 h32).mono
    (P' := fun (s t : State) => KeyExportInput p slots s ∧ KeyExportInput p slots t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  exact relCT_chain save (keySave_next · stable saved outputY) (keySave_next · stable saved outputY)
    (relCT_chain exportCT (keyExport_next · bounds h4 h32 outputY) (keyExport_next · bounds h4 h32 outputY)
      (keyFinish_ct bounds h32 h36 h40))

end VG.Proof.Ffdh.Arm
