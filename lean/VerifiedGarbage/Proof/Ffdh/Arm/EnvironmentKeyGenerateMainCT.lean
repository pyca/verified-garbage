module

public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentPrepareLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentTailLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentSampleLaw
public import VerifiedGarbage.Impl.Ffdh.Arm.SampleKeyGenerate
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleResult
import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentSampleState
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentPrepareState
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateCalls
import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.FlagCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalarCT
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.Arm.Isa

import VerifiedGarbage.Impl.Ffdh.Arm.KeyGenerate
public import VerifiedGarbage.TCB.Mem

/-! The only secret-dependent key-generation branch is scalar acceptance,
whose classification is disclosed by the attempt's returned status. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem environmentKeyGenerateMain_ct (prepare sample tail : Prog isa) (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p) (prep : EnvironmentPrepareLaw env prepare) (sampler : EnvironmentSampleLaw env layout sample) (law : EnvironmentTailLaw env layout tail) {p : Inputs} {slots : List Nat} {rb1 rb2 : List Byte}
    (layoutBound : ∀ (p : Inputs) (rb : List Byte), rb.length = p.k → Spec.Rsa.os2ip ((layout p).encode rb) < 2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (publicRelAll : ∀ s t, env.publicRel s t)
    (afterMem : ∀ {p : Inputs} {s t : State}, env.holds p s → t.mem = s.mem → VG.Proof.X25519.Arm.Rest [] s t → env.holds p t)
    (stable : stableSlots slots = true) (h52 : 52 ∈ slots) (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h48 : 48 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (special : sampleSlots slots)
    (size1 : rb1.length = p.k) (size2 : rb2.length = p.k)
    (classification : sampleScalarValid p (layout p) rb1 ↔ sampleScalarValid p (layout p) rb2)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (privateLength : p.privateLength = p.k) (outputY : p.output = p.publicValue)
    (large : 1 < p.P) (odd : p.P % 2 = 1) (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) :
    RelCT isa (fun s t => ((KeyScalarInput p slots rb1 s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧ ((KeyScalarInput p slots rb2 t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SampleKeyGenerate.main prepare sample tail) (fun _ _ => True) := by
  have preparePost (s : State) {rb : List Byte} (size : rb.length = p.k)
      (h : (KeyScalarInput p slots rb s ∧ KeyCallMemory p s) ∧ env.holds p s) :
      WP isa prepare s (fun t => (KeyPrepared p slots rb t ∧ KeyCallMemory p t) ∧ env.holds p t) := by
    refine (environmentPrepare_next env prepare prep s stable h52 h0 h24 h32 large odd normalized size h.1.1 h.1.2 h.2).and ?_
    refine WP.mono_syms (prep.correct s h.1.1.context h.2 h.1.2 stable h52 h0 h24 h32 large odd normalized) ?_
    rintro t ⟨_, _, _, _, frame, rest⟩ syms
    apply env.stable h.2 _ rest syms
    exact frame.sub (by
      intro r hr
      simp only [keyPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl) | rfl
      · exact ⟨⟨State.addr p.base, 8 * p.len⟩, by simp [keyCallWrites, keyWrites], by intro a ha; exact ha⟩
      · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], Offset.sub_base _ (by decide)⟩
      · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], Offset.sub_base _ (by decide)⟩
      · exact ⟨_, by simp [keyCallWrites], fun _ hx => hx⟩)
  have prepareCT : RelCT isa (fun s t =>
      ((KeyScalarInput p slots rb1 s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧
      ((KeyScalarInput p slots rb2 t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp)
      prepare (fun s t => ((KeyPrepared p slots rb1 s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧
      ((KeyPrepared p slots rb2 t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨trace, _⟩ := prep.ct stable h52 h0 h24 h32 large odd normalized s t tr1 tr2 u v
      ⟨⟨⟨h.1.1.1.context, h.1.1.2⟩, h.1.2⟩, ⟨⟨h.2.1.1.1.context, h.2.1.1.2⟩, h.2.1.2⟩, h.2.2⟩ e1 e2
    obtain ⟨_, u', runU, postU⟩ := preparePost s size1 h.1
    obtain ⟨_, v', runV, postV⟩ := preparePost t size2 h.2.1
    obtain ⟨-, rfl⟩ := Exec.det e1 runU
    obtain ⟨-, rfl⟩ := Exec.det e2 runV
    exact ⟨trace, postU, postV, env.public_stable h.2.2.1 (Exec.syms e1) (Exec.syms e2),
      (Exec.sp e1).trans (h.2.2.2.trans (Exec.sp e2).symm)⟩
  have sampleCT := (sampler.ct stable special normalized odd h52 h0 h24 h28 h32 h40 h48 h60 size1 size2 entropySep).mono
    (P' := fun (s t : State) => ((KeyPrepared p slots rb1 s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧
      ((KeyPrepared p slots rb2 t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.1.1.toKeyScalarInput, h.1.2⟩, ⟨h.2.1.1.1.toKeyScalarInput, h.2.1.2⟩, h.2.2⟩) (fun _ _ h => h)
  have sampled := (relCT_keep_sp sampleCT (fun _ _ h => h.2.2.2)).wp (fun s t h =>
    ⟨environmentSample_next env sample layout sampler s stable special h52 h0 h24 h28 h32 h40 h48 h60 size1 entropySep h.1.1.1 h.1.1.2 h.1.2 normalized odd,
     environmentSample_next env sample layout sampler t stable special h52 h0 h24 h28 h32 h40 h48 h60 size2 entropySep h.2.1.1.1 h.2.1.1.2 h.2.1.2 normalized odd⟩)
  have imports := (importAt_ct (p := p) (a := 1) (slot := 40) (countSlot := 44) (k := p.k) stable (by simp [h40]) (by simp [h44])
    (by change BitVec.ofNat 32 p.privateLength = _; rw [privateLength]) (by decide)).mono
    (P' := fun (s t : State) => ((SampleReady p (layout p) slots rb1 s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧ ((SampleReady p (layout p) slots rb2 t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.1.1.context.toContext, h.1.1.1.ready⟩, ⟨h.2.1.1.1.context.toContext, h.2.1.1.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  have ranges := (scalarRange_ct stable (by simp [h28]) (by simp [h32]) (by simp [h60]) odd).mono
    (P' := fun (s t : State) => ((SampleImported p (layout p) slots rb1 s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧ ((SampleImported p (layout p) slots rb2 t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.1.1.context.toContext, h.1.1.1.ready, h.1.1.1.modulus⟩, ⟨h.2.1.1.1.context.toContext, h.2.1.1.1.ready, h.2.1.1.1.modulus⟩, h.2.2⟩) (fun _ _ h => h)
  have sigSize {rb : List Byte} (size : rb.length = p.k) : (((layout p).encode rb).drop (layout p).lead).length = (layout p).width := by
    rw [List.length_drop, (layout p).encode_length size]
    rfl
  have branches : RelCT isa (fun s t => ((SampleRanged p (layout p) slots rb1 s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧ ((SampleRanged p (layout p) slots rb2 t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.ifFlag tail VG.Impl.Ffdh.Arm.Domain.GenerateKey.failScalar)
      (fun _ _ => True) := by
    apply ifFlag_pair_ct (decide (sampleScalarValid p (layout p) rb1))
      (fun s h => by
        have f := h.1.1.flag
        change s.gpr .r11 = (if sampleScalarValid p (layout p) rb1 then 1 else 0) at f
        simpa only [decide_eq_true_eq] using f)
      (fun s h => by
        have f := h.1.1.flag
        change s.gpr .r11 = (if sampleScalarValid p (layout p) rb2 then 1 else 0) at f
        simp only [← classification] at f
        simpa only [decide_eq_true_eq] using f)
      (fun _ _ h mem rest => ⟨⟨h.1.1.after_mem mem rest, h.1.2.after rest⟩, afterMem h.2 mem rest⟩) (fun _ _ h mem rest => ⟨⟨h.1.1.after_mem mem rest, h.1.2.after rest⟩, afterMem h.2 mem rest⟩)
    · intro _
      exact (law.ct stable h52 h4 h32 h36
        h40 h56 saved (sigSize size1) (sigSize size2)
        (by rw [(layout p).encode_significant rb1]; exact layoutBound p rb1 size1)
        (by rw [(layout p).encode_significant rb2]; exact layoutBound p rb2 size2) odd outputY).mono
        (fun s t h => ⟨⟨⟨⟨h.1.1.1.context, h.1.1.1.ready, h.1.1.1.modulus, h.1.1.1.r2, h.1.1.1.significant, h.1.1.1.outputs⟩, h.1.1.2⟩, h.1.2⟩,
          ⟨⟨⟨h.2.1.1.1.context, h.2.1.1.1.ready, h.2.1.1.1.modulus, h.2.1.1.1.r2, h.2.1.1.1.significant, h.2.1.1.1.outputs⟩, h.2.1.1.2⟩, h.2.1.2⟩, publicRelAll s t, h.2.2⟩)
        (fun _ _ h => h)
    · intro _
      exact (keyFail_ct (fun d hd => (stableSlots_at stable hd).1) (by simp [h32]) (by simp [h36]) (by simp [h40])).mono
        (fun _ _ h => ⟨⟨h.1.1.1.context.toContext.toArgumentMemory, h.1.1.1.outputs⟩, ⟨h.2.1.1.1.context.toContext.toArgumentMemory, h.2.1.1.1.outputs⟩, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.SampleKeyGenerate.main
  exact prepareCT.seq (sampled.seq ((relCT_chain imports
        (fun s h => environmentImport_next env s stable (by simp [h40]) (by simp [h44]) size1 privateLength h.1.1 h.1.2 h.2)
        (fun s h => environmentImport_next env s stable (by simp [h40]) (by simp [h44]) size2 privateLength h.1.1 h.1.2 h.2)
        (relCT_chain ranges
          (fun s h => environmentRange_next env s stable (by simp [h28]) (by simp [h32]) (by simp [h60]) odd h.1.1 h.1.2 h.2)
          (fun s h => environmentRange_next env s stable (by simp [h28]) (by simp [h32]) (by simp [h60]) odd h.1.1 h.1.2 h.2)
          branches)).mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)))

end VG.Proof.Ffdh.Arm
