module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateFn
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyEntryCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateBodyCT
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
public import VerifiedGarbage.TCB.Arm.Isa

public import VerifiedGarbage.Impl.Ffdh.Arm.KeyGenerate

/-! The callable key-generation attempt reveals only its public domain and
buffer layout and the scalar-acceptance class documented by its status. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem keyGenerateFn_ct (prepare tail : Prog isa) (prep : KeyPrepareLaw prepare) (law : KeyTailLaw tail) {p : Inputs} {rb1 rb2 : List Byte}
    (classification : Spec.Rsa.modulusValid p.P p.k = true → (keyScalarValid p rb1 ↔ keyScalarValid p rb2)) :
    RelCT isa (fun s t => KeyGenerateFnInput p rb1 s ∧ KeyGenerateFnInput p rb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.KeyGenerate.code prepare tail) (fun _ _ => True) := by
  let P := fun (rb : List Byte) (a : State) => ∃ s, KeyGenerateFnInput p rb s ∧ a = entered s
  have entry := keyEntry_ct.mono
    (P' := fun (s t : State) => P rb1 s ∧ P rb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  have wp (a : State) {rb : List Byte} (h : P rb a) :
      WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.entry) a
        (fun u => KeyScalarInput p [0, 48, 44, 32, 28, 24, 4, 36, 40] rb u ∧ KeyCallMemory p u) := by
    obtain ⟨s, input, rfl⟩ := h
    refine WP.mono (withAllRest (keyEntry_ok (entered s) input.args input.incoming input.privateValue input.publicValue input.outputY input.privateLength)) ?_
    rintro u ⟨⟨context, frame⟩, rest⟩
    exact ⟨⟨context, input.entropy.after_frame frame rest (by simpa [input.size] using input.entropyStack),
      input.outputs.after rest, by rw [rest.sp]; exact input.entropyStack⟩, input.calls.after rest⟩
  unfold VG.Impl.Ffdh.Arm.KeyGenerate.code
  apply framed_ct (fun _ _ h => ⟨h.1.stackFits, h.2.1.stackFits⟩) (fun _ _ h => h.2.2)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s, t, related, rfl, rfl⟩ := h
  have body := relCT_chain entry (fun a h => wp a h) (fun a h => wp a h)
    (keyGenerateBody_ct prepare tail prep law (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by intro d hd; revert d; decide) related.1.size related.2.1.size classification related.1.entropySep
      related.1.privateLength related.1.outputY)
  exact body _ _ _ _ _ _ ⟨⟨s, related.1, rfl⟩, ⟨t, related.2.1, rfl⟩,
    by rw [entered_sp, entered_sp, related.2.2]⟩ e1 e2

end VG.Proof.Ffdh.Arm
