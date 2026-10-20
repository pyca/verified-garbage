module

import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentKeyGenerateMainCT
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedKeyGenerate
import VerifiedGarbage.Proof.Ffdh.Arm.Head
import VerifiedGarbage.Proof.Ffdh.Arm.HeadCT
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.Arm.Syms
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentPrepareLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentSampleLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentTailLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleResult

/-! The cached attempt uses only the native public setup prefix before sampling. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem cachedKeyGenerateBody_ct (prepare sample tail : Prog isa) (env : SampleEnvironment)
    (layout : (p : Inputs) → ScalarLayout p) (prep : EnvironmentPrepareLaw env prepare)
    (sampler : EnvironmentSampleLaw env layout sample) (law : EnvironmentTailLaw env layout tail)
    (layoutBound : ∀ (p : Inputs) (rb : List Byte), rb.length = p.k →
      Spec.Rsa.os2ip ((layout p).encode rb) < 2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (publicRelAll : ∀ s t, env.publicRel s t)
    (afterMem : ∀ {p : Inputs} {s t : State}, env.holds p s → t.mem = s.mem → VG.Proof.X25519.Arm.Rest [] s t → env.holds p t)
    {p : Inputs} {slots : List Nat} {rb1 rb2 : List Byte}
    (stable : stableSlots slots = true)
    (h52 : 52 ∈ slots) (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots)
    (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots)
    (h44 : 44 ∈ slots) (h48 : 48 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d) (special : sampleSlots slots)
    (size1 : rb1.length = p.k) (size2 : rb2.length = p.k)
    (classification : sampleScalarValid p (layout p) rb1 ↔ sampleScalarValid p (layout p) rb2)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (privateLength : p.privateLength = p.k) (outputY : p.output = p.publicValue)
    (valid : Spec.Rsa.modulusValid p.P p.k = true) :
    RelCT isa (fun s t => ((KeyScalarInput p slots rb1 s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧
      ((KeyScalarInput p slots rb2 t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.CachedKeyGenerate.body prepare sample tail) (fun _ _ => True) := by
  let P := fun rb s => (KeyScalarInput p slots rb s ∧ KeyCallMemory p s) ∧ env.holds p s
  let Q := fun rb s => (KeyScalarInput p (60 :: 56 :: slots) rb s ∧ KeyCallMemory p s) ∧ env.holds p s
  have head := (headPrefix_ct stable h0 h24 h32).mono
    (P' := fun (s t : State) => P rb1 s ∧ P rb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.1.1.context, h.2.1.1.1.context, h.2.2⟩) (fun _ _ h => h)
  have wp (s : State) {rb : List Byte} (size : rb.length = p.k) (h : P rb s) :
      WP isa (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24 ++ VG.Impl.Ffdh.Arm.Domain.domainPointers)) s (Q rb) := by
    refine WP.mono_syms (headPrefix_ok s h.1.1.context stable h0 h24 h32) ?_
    rintro u ⟨context, _, _, frame, rest⟩ syms
    refine ⟨⟨⟨context, h.1.1.entropy.after_frame frame rest (by simpa [size] using h.1.1.entropyStack),
      h.1.1.outputs.after rest, by rw [rest.sp]; exact h.1.1.entropyStack⟩, h.1.2.after rest⟩, ?_⟩
    exact env.stable h.2 (frame.mono (by simp [keyCallWrites, keyWrites])) rest syms
  have stableU : stableSlots (60 :: 56 :: slots) = true := by
    change (true && (true && stableSlots slots)) = true
    simp only [Bool.true_and, stable]
  have facts := VG.Proof.Bignum.valid_facts valid p.minLength
  have main := (environmentKeyGenerateMain_ct prepare sample tail env layout prep sampler law layoutBound
    publicRelAll afterMem stableU
    (by simp [h52]) (by simp [h0]) (by simp [h4]) (by simp [h24]) (by simp [h28])
    (by simp [h32]) (by simp [h36]) (by simp [h40]) (by simp [h44]) (by simp [h48]) (by simp) (by simp)
    (by intro d hd; simp only [List.mem_cons] at hd; rcases hd with rfl | rfl | hd <;> first | decide | exact saved d hd)
    (by intro d hd; simp only [List.mem_cons] at hd; rcases hd with rfl | rfl | hd <;> first | decide | exact special d hd)
    size1 size2 classification entropySep privateLength outputY facts.2.1 facts.1 facts.2.2).mono
      (P' := fun (s t : State) => Q rb1 s ∧ Q rb2 t ∧ s.sp = t.sp)
      (fun s t h => ⟨h.1, h.2.1, publicRelAll s t, h.2.2⟩) (fun _ _ h => h)
  exact relCT_chain head (fun s h => wp s size1 h) (fun s h => wp s size2 h) main

end VG.Proof.Ffdh.Arm
