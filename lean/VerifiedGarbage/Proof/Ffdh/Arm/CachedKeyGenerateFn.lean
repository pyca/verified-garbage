module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateFn
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedKeyGenerate
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentPrepareLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentSampleLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentTailLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleResult
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyEntry

import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateEntry
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentKeyGenerateMain
import VerifiedGarbage.Proof.Ffdh.Arm.Head
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.Ffdh.Arm.SampleKeyGenerate
/-! Cached key attempts retain the established outer frame and callee stack bound. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedKeyGenerateBody.lean`, which only this module imported.
section

/-! Checked cached domains need only the shared native argument setup prefix. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem cachedKeyGenerateBody_ok (prepare sample tail : Prog isa) (env : SampleEnvironment)
    (layout : (p : Inputs) → ScalarLayout p) (prep : EnvironmentPrepareLaw env prepare)
    (sampler : EnvironmentSampleLaw env layout sample) (law : EnvironmentTailLaw env layout tail)
    (layoutBound : ∀ (p : Inputs) (rb : List Byte), rb.length = p.k →
      Spec.Rsa.os2ip ((layout p).encode rb) <
        2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (h : Context p slots s) (environment : env.holds p s) (calls : KeyCallMemory p s)
    (stable : stableSlots slots = true)
    (h52 : 52 ∈ slots) (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots)
    (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots)
    (h44 : 44 ∈ slots) (h48 : 48 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d) (special : sampleSlots slots)
    (valid : Spec.Rsa.modulusValid p.P p.k = true)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr s.sp, 72⟩)
    (outputs : KeyOutputs p s)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (privateLength : p.privateLength = p.k) (outputY : p.output = p.publicValue) :
    WP isa (VG.Impl.Ffdh.Arm.CachedKeyGenerate.body prepare sample tail) s fun t =>
      sampleResult p (layout p) rb t ∧ Frame (keyCallWrites p s) s.mem t.mem := by
  rw [VG.Impl.Ffdh.Arm.CachedKeyGenerate.body, WP.seq_iff]
  refine WP.mono_syms (headPrefix_ok s h stable h0 h24 h32) ?_
  rintro u ⟨contextU, _, _, frameU, restU⟩ symsU
  have fullU : Frame (keyCallWrites p s) s.mem u.mem := frameU.mono (by simp [keyCallWrites, keyWrites])
  have environmentU := env.stable environment fullU restU symsU
  have entropyU := entropy.after_frame frameU restU (by simpa only [List.mem_singleton, forall_eq, size] using entropyStack)
  have facts := VG.Proof.Bignum.valid_facts valid p.minLength
  have stableU : stableSlots (60 :: 56 :: slots) = true := by
    change (true && (true && stableSlots slots)) = true
    simp only [Bool.true_and, stable]
  refine WP.mono (environmentKeyGenerateMain_ok prepare sample tail env layout prep sampler law layoutBound u
    contextU environmentU (calls.after restU) stableU
    (by simp [h52]) (by simp [h0]) (by simp [h4]) (by simp [h24]) (by simp [h28])
    (by simp [h32]) (by simp [h36]) (by simp [h40]) (by simp [h44]) (by simp [h48]) (by simp) (by simp)
    (by intro d hd; simp only [List.mem_cons] at hd; rcases hd with rfl | rfl | hd <;> first | decide | exact saved d hd)
    (by intro d hd; simp only [List.mem_cons] at hd; rcases hd with rfl | rfl | hd <;> first | decide | exact special d hd)
    facts.2.1 facts.1 facts.2.2 entropyU size (by rw [restU.sp]; exact entropyStack)
    (outputs.after restU) entropySep privateLength outputY) ?_
  rintro t ⟨status, privateT, publicT, frameT⟩
  exact ⟨⟨status, privateT, publicT⟩,
    fullU.trans (by simpa only [keyCallWrites, keyWrites, restU.sp] using frameT)⟩

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem cachedKeyGenerateEntered_ok (prepare sample tail : Prog isa) (env : SampleEnvironment)
    (layout : (p : Inputs) → ScalarLayout p) (prep : EnvironmentPrepareLaw env prepare)
    (sampler : EnvironmentSampleLaw env layout sample) (law : EnvironmentTailLaw env layout tail)
    (layoutBound : ∀ (p : Inputs) (rb : List Byte), rb.length = p.k →
      Spec.Rsa.os2ip ((layout p).encode rb) <
        2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (s : State) {p : Inputs} {rb : List Byte} (h : ArgumentMemory p [] s)
    (environment : env.holds p s) (calls : KeyCallMemory p s) (incoming : KeyIncoming p s)
    (cache : IncomingWord p.cachedContext 156 s)
    (privateValue : s.gpr .r0 = p.privateValue) (publicValue : s.gpr .r2 = p.publicValue)
    (outputY : p.output = p.publicValue) (privateLength : p.privateLength = p.k)
    (valid : Spec.Rsa.modulusValid p.P p.k = true)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr s.sp, 72⟩)
    (outputs : KeyOutputs p s)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩) :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.CachedKeyGenerate.entry)
      (VG.Impl.Ffdh.Arm.CachedKeyGenerate.body prepare sample tail)) s fun t =>
      sampleResult p (layout p) rb t ∧ Frame (keyCallWrites p s) s.mem t.mem := by
  rw [WP.seq_iff]
  refine WP.mono_syms (withAllRest (cachedKeyGenerateEntry_ok s h incoming cache privateValue publicValue outputY privateLength)) ?_
  rintro u ⟨⟨contextU, frameU⟩, restU⟩ symsU
  have fullU : Frame (keyCallWrites p s) s.mem u.mem := frameU.mono (by simp [keyCallWrites, keyWrites])
  have environmentU := env.stable environment fullU (restU.mono (by simp [roundClobbers])) symsU
  have entropyU := entropy.after_frame frameU restU (by simpa only [List.mem_singleton, forall_eq, size] using entropyStack)
  refine WP.mono (cachedKeyGenerateBody_ok prepare sample tail env layout prep sampler law layoutBound u
    contextU environmentU (calls.after restU) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by intro d hd; revert d; decide) (by intro d hd; revert d; decide)
    valid entropyU size (by rw [restU.sp]; exact entropyStack)
    (outputs.after restU) entropySep privateLength outputY) ?_
  rintro t ⟨result, frameT⟩
  exact ⟨result, fullU.trans (by simpa only [keyCallWrites, keyWrites, restU.sp] using frameT)⟩

structure CachedKeyGenerateFnInput (p : Inputs) (rb : List Byte) (s : State) : Prop where
  input : KeyGenerateFnInput p rb s
  cache : IncomingWord p.cachedContext 156 (entered s)

theorem cachedKeyGenerateFn_ok (prepare sample tail : Prog isa) (env : SampleEnvironment)
    (layout : (p : Inputs) → ScalarLayout p) (prep : EnvironmentPrepareLaw env prepare)
    (sampler : EnvironmentSampleLaw env layout sample) (law : EnvironmentTailLaw env layout tail)
    (layoutBound : ∀ (p : Inputs) (rb : List Byte), rb.length = p.k →
      Spec.Rsa.os2ip ((layout p).encode rb) <
        2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (s : State) {p : Inputs} {rb : List Byte} (h : CachedKeyGenerateFnInput p rb s)
    (environment : env.holds p (entered s)) (valid : Spec.Rsa.modulusValid p.P p.k = true) :
    WP isa (VG.Impl.Ffdh.Arm.CachedKeyGenerate.code prepare sample tail) s fun t =>
      abiPreserved s t ∧ sampleResult p (layout p) rb t := by
  unfold VG.Impl.Ffdh.Arm.CachedKeyGenerate.code
  refine framed_of_separate _ s h.input.stackFits (keyCallWrites p (entered s))
    (fun m status =>
      status = sampleMainFlag p (layout p) rb ∧ Spec.Rsa.bytesAt m (State.addr p.privateValue) p.k =
        (if sampleSuccess p (layout p) rb then (layout p).encode rb else List.replicate p.k 0) ∧
      Spec.Rsa.bytesAt m (State.addr p.publicValue) p.k =
        (if sampleSuccess p (layout p) rb then Spec.Rsa.i2osp (keyPower p ((layout p).encode rb)) p.k else List.replicate p.k 0)) ?_ ?_
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact h.input.saved r hr
    · have eq := List.mem_singleton.mp hr; subst r; exact h.input.savedCall
  refine WP.mono (cachedKeyGenerateEntered_ok prepare sample tail env layout prep sampler law layoutBound (entered s)
    h.input.args environment h.input.calls h.input.incoming h.cache h.input.privateValue h.input.publicValue
    h.input.outputY h.input.privateLength valid h.input.entropy h.input.size h.input.entropyStack
    h.input.outputs h.input.entropySep) ?_
  rintro t ⟨result, frameT⟩
  exact ⟨frameT, result⟩

end VG.Proof.Ffdh.Arm
