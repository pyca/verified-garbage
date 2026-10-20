module

public import VerifiedGarbage.Proof.Ffdh.Arm.SampleResult
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateFn
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleTailLaw
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Ffdh.Arm.KeyEntryCT
import VerifiedGarbage.Proof.Ffdh.Arm.SampleKeyGenerateBodyCT
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
public import VerifiedGarbage.TCB.Arm.Isa

public import VerifiedGarbage.Impl.Ffdh.Arm.SampleKeyGenerate

/-! The callable key-generation attempt reveals only its public domain and
buffer layout and the scalar-acceptance class documented by its status. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem sampleKeyGenerateFn_ct (prepare sample tail : Prog isa) (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p)
    (prep : KeyPrepareLaw prepare) (sampler : SampleLaw env layout sample) (law : SampleTailLaw tail) {p : Inputs} {rb1 rb2 : List Byte}
    (classification : Spec.Rsa.modulusValid p.P p.k = true → (sampleScalarValid p (layout p) rb1 ↔ sampleScalarValid p (layout p) rb2)) :
    RelCT isa (fun s t => (KeyGenerateFnInput p rb1 s ∧ env.holds p (entered s)) ∧ (KeyGenerateFnInput p rb2 t ∧ env.holds p (entered t)) ∧ env.publicRel s t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SampleKeyGenerate.code prepare sample tail) (fun _ _ => True) := by
  let P := fun (rb : List Byte) (a : State) => ∃ s, KeyGenerateFnInput p rb s ∧ a = entered s ∧ env.holds p a
  let Q := fun (rb : List Byte) (u : State) =>
    (KeyScalarInput p [0, 48, 44, 32, 28, 24, 4, 36, 40] rb u ∧ KeyCallMemory p u) ∧ env.holds p u
  have wp (a : State) {rb : List Byte} (h : P rb a) :
      WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.entry) a (Q rb) := by
    obtain ⟨s, input, rfl, environment⟩ := h
    refine WP.mono_syms (withAllRest (keyEntry_ok (entered s) input.args input.incoming input.privateValue input.publicValue input.outputY input.privateLength)) ?_
    rintro u ⟨⟨context, frame⟩, rest⟩ syms
    refine ⟨⟨⟨context, input.entropy.after_frame frame rest (by simpa [input.size] using input.entropyStack),
      input.outputs.after rest, by rw [rest.sp]; exact input.entropyStack⟩, input.calls.after rest⟩, ?_⟩
    apply env.stable environment _ (rest.mono (by simp [roundClobbers])) syms
    exact frame.mono (by simp [keyCallWrites, keyWrites])
  have entry : RelCT isa (fun s t => P rb1 s ∧ P rb2 t ∧ env.publicRel s t ∧ s.sp = t.sp)
      (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.entry)
      (fun s t => Q rb1 s ∧ Q rb2 t ∧ env.publicRel s t ∧ s.sp = t.sp) := by
    intro s t tr1 tr2 u v h e1 e2
    have timing := keyEntry_ct s t tr1 tr2 u v h.2.2.2 e1 e2
    obtain ⟨_, u', runU, postU⟩ := wp s h.1
    obtain ⟨_, v', runV, postV⟩ := wp t h.2.1
    obtain ⟨-, rfl⟩ := Exec.det e1 runU
    obtain ⟨-, rfl⟩ := Exec.det e2 runV
    exact ⟨timing.1, postU, postV,
      env.public_stable h.2.2.1 (Exec.syms e1) (Exec.syms e2),
      (Exec.sp e1).trans (h.2.2.2.trans (Exec.sp e2).symm)⟩
  unfold VG.Impl.Ffdh.Arm.SampleKeyGenerate.code
  apply framed_ct (fun _ _ h => ⟨h.1.1.stackFits, h.2.1.1.stackFits⟩) (fun _ _ h => h.2.2.2)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s, t, related, rfl, rfl⟩ := h
  have body := entry.seq
    (sampleKeyGenerateBody_ct prepare sample tail env layout prep sampler law (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by intro d hd; revert d; decide) (by intro d hd; revert d; decide) related.1.1.size related.2.1.1.size classification related.1.1.entropySep
      related.1.1.privateLength related.1.1.outputY)
  exact body _ _ _ _ _ _ ⟨⟨s, related.1.1, rfl, related.1.2⟩, ⟨t, related.2.1.1, rfl, related.2.1.2⟩,
    env.public_stable related.2.2.1 (by rfl) (by rfl),
    by rw [entered_sp, entered_sp, related.2.2.2]⟩ e1 e2

end VG.Proof.Ffdh.Arm
