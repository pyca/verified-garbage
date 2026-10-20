module

public import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateFn
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateEntryCT
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateBodyCT
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateEntry

/-! Cached key-generation timing reveals only the reviewed attempt classification. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem cachedKeyGenerateFn_ct (prepare sample tail : Prog isa) (env : SampleEnvironment)
    (layout : (p : Inputs) → ScalarLayout p) (prep : EnvironmentPrepareLaw env prepare)
    (sampler : EnvironmentSampleLaw env layout sample) (law : EnvironmentTailLaw env layout tail)
    (layoutBound : ∀ (p : Inputs) (rb : List Byte), rb.length = p.k →
      Spec.Rsa.os2ip ((layout p).encode rb) < 2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (publicRelAll : ∀ s t, env.publicRel s t)
    (afterMem : ∀ {p : Inputs} {s t : State}, env.holds p s → t.mem = s.mem → VG.Proof.X25519.Arm.Rest [] s t → env.holds p t)
    {p : Inputs} {rb1 rb2 : List Byte}
    (valid : Spec.Rsa.modulusValid p.P p.k = true)
    (classification : sampleScalarValid p (layout p) rb1 ↔ sampleScalarValid p (layout p) rb2) :
    RelCT isa (fun s t => (CachedKeyGenerateFnInput p rb1 s ∧ env.holds p (entered s)) ∧
      (CachedKeyGenerateFnInput p rb2 t ∧ env.holds p (entered t)) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.CachedKeyGenerate.code prepare sample tail) (fun _ _ => True) := by
  let P := fun (rb : List Byte) (a : State) =>
    ∃ s, CachedKeyGenerateFnInput p rb s ∧ a = entered s ∧ env.holds p a
  let Q := fun (rb : List Byte) (u : State) =>
    (KeyScalarInput p [52, 0, 48, 44, 32, 28, 24, 4, 36, 40] rb u ∧ KeyCallMemory p u) ∧ env.holds p u
  have entry := cachedKeyGenerateEntry_ct.mono
    (P' := fun (s t : State) => P rb1 s ∧ P rb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  have wp (a : State) {rb : List Byte} (h : P rb a) :
      WP isa (.block VG.Impl.Ffdh.Arm.CachedKeyGenerate.entry) a (Q rb) := by
    obtain ⟨s, allInput, rfl, environment⟩ := h
    have input := allInput.input
    refine WP.mono_syms (withAllRest (cachedKeyGenerateEntry_ok (entered s) input.args input.incoming allInput.cache
      input.privateValue input.publicValue input.outputY input.privateLength)) ?_
    rintro u ⟨⟨context, frame⟩, rest⟩ syms
    refine ⟨⟨⟨context, input.entropy.after_frame frame rest (by simpa [input.size] using input.entropyStack),
      input.outputs.after rest, by rw [rest.sp]; exact input.entropyStack⟩, input.calls.after rest⟩, ?_⟩
    exact env.stable environment (frame.mono (by simp [keyCallWrites, keyWrites]))
      (rest.mono (by simp [roundClobbers])) syms
  unfold VG.Impl.Ffdh.Arm.CachedKeyGenerate.code
  apply framed_ct (fun _ _ h => ⟨h.1.1.input.stackFits, h.2.1.1.input.stackFits⟩) (fun _ _ h => h.2.2)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s, t, related, rfl, rfl⟩ := h
  have body := relCT_chain entry (fun a h => wp a h) (fun a h => wp a h)
    (cachedKeyGenerateBody_ct prepare sample tail env layout prep sampler law layoutBound publicRelAll afterMem
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by intro d hd; revert d; decide) (by intro d hd; revert d; decide)
      related.1.1.input.size related.2.1.1.input.size classification related.1.1.input.entropySep
      related.1.1.input.privateLength related.1.1.input.outputY valid)
  exact body _ _ _ _ _ _ ⟨⟨s, related.1.1, rfl, related.1.2⟩,
    ⟨t, related.2.1.1, rfl, related.2.1.2⟩,
    by rw [entered_sp, entered_sp, related.2.2]⟩ e1 e2

end VG.Proof.Ffdh.Arm
