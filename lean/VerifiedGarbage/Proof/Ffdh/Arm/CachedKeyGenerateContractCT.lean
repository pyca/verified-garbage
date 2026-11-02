module

public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedKeyGenerate
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentPrepareLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentSampleLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentTailLaw

import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateData
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateInput
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateEnvironment
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSamplePolicy
import VerifiedGarbage.Proof.Ffdh.Arm.PrivateSpec
import VerifiedGarbage.Proof.Ffdh.Arm.KeyClassification
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicSpec
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGeneratePre
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyEntryCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.SampleMemory
import VerifiedGarbage.Proof.Ffdh.Arm.SampleState
import VerifiedGarbage.Proof.Ffdh.Arm.KeyCallMemory
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Ffdh.Arm.KeyState
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAt
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Ffdh.Arm.Context
import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Impl.Ffdh.Arm.SampleKeyGenerate
import VerifiedGarbage.Proof.Ffdh.Arm.SampleResult
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.FlagCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalarCT
import VerifiedGarbage.TCB.Code
import VerifiedGarbage.TCB.Mem
import VerifiedGarbage.Proof.Ffdh.Arm.Head
import VerifiedGarbage.Proof.Ffdh.Arm.HeadCT
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateFn
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateEntry
import VerifiedGarbage.Proof.Framework.Mem
/-! Cached attempts compare independent entropy tapes under the reviewed public leakage. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedKeyGenerateEntryCT.lean`, which only this module imported.
section

/-! Retaining the appended context reads and writes only fixed stack offsets. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem cachedKeyGenerateEntry_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block VG.Impl.Ffdh.Arm.CachedKeyGenerate.entry) (fun _ _ => True) := by
  have extra := RelCT.block_append (stackAddr_ct.seq (RelCT.block_append
    ((loadLocal_ct .r3 156 (by decide)).seq (storeLocal_ct .r3 52))))
  exact RelCT.block_append ((relCT_keep_sp keyEntry_ct (fun _ _ h => h)).seq
    (extra.mono (fun _ _ h => h) (fun _ _ _ => trivial)))

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/EnvironmentSampleState.lean`, which only this module imported.
section

/-! Native key-generation states used to compose functional and timing proofs. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt Operand arrAt)
open VG.Proof.X25519.Arm (Rest)

theorem environmentSample_next (env : SampleEnvironment) (sample : Prog isa) (layout : (p : Inputs) → ScalarLayout p)
    (sampler : EnvironmentSampleLaw env layout sample) (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (stable : stableSlots slots = true) (special : sampleSlots slots)
    (h52 : 52 ∈ slots) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h40 : 40 ∈ slots) (h48 : 48 ∈ slots) (h60 : 60 ∈ slots) (size : rb.length = p.k)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (h : KeyPrepared p slots rb s) (calls : KeyCallMemory p s) (environment : env.holds p s) (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) (odd : p.P % 2 = 1) :
    WP isa sample s (fun t => (SampleReady p (layout p) slots rb t ∧ KeyCallMemory p t) ∧ env.holds p t) := by
  refine WP.mono_syms (sampler.correct s h.context environment normalized odd stable special h52 h0 h24 h28 h32 h40 h48 h60 h.ready h.modulus h.r2
    h.entropy size h.entropyStack h.outputs entropySep) ?_
  rintro t ⟨context, ready, modulus, r2, scalar, significant, frame, rest⟩ syms
  refine ⟨⟨⟨context, ready, modulus, r2, scalar, significant, h.outputs.after rest⟩, calls.after rest⟩, env.stable environment ?_ rest syms⟩
  exact frame.sub (by
    intro r hr
    simp only [keyScalarWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr p.privateValue, p.k⟩, by simp [keyCallWrites, keyWrites], fun _ hx => hx⟩)

theorem environmentImport_next (env : SampleEnvironment) (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {rb : List Byte}
    (stable : stableSlots slots = true) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (size : rb.length = p.k) (privateLength : p.privateLength = p.k) (h : SampleReady p l slots rb s) (calls : KeyCallMemory p s) (environment : env.holds p s) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 40 44) s (fun t => (SampleImported p l slots rb t ∧ KeyCallMemory p t) ∧ env.holds p t) := by
  have length := l.encode_length size
  refine WP.mono_syms (importAt_ok s 1 40 44 h.context.toContext stable h40 h44 h.ready (by decide) (by decide) h.scalar
    (by rw [length]; have := p.minLength; omega) (by rw [length]; exact p.width.2.2.2.1)
    (by change BitVec.ofNat 32 p.privateLength = _; rw [privateLength, length])) ?_
  rintro t ⟨context, ready, imported, keeps, frame, rest⟩ syms
  have fits : arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
  refine ⟨⟨⟨⟨h.context.after_workspace frame rest context.ptr (fun d hd => (stableSlots_at stable hd).1), ready,
    (keeps_array_num keeps fits (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 0) (by decide)).trans h.modulus,
    (keeps_array_num keeps fits (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 4) (by decide)).trans h.r2,
    h.scalar.after_workspace frame rest, h.significant.after_workspace frame rest, h.outputs.after rest⟩, imported⟩, calls.after rest⟩, env.stable environment ?_ rest syms⟩
  exact frame.mono (by simp [keyCallWrites, keyWrites])

theorem environmentRange_next (env : SampleEnvironment) (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {rb : List Byte}
    (stable : stableSlots slots = true) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots)
    (odd : p.P % 2 = 1) (h : SampleImported p l slots rb s) (calls : KeyCallMemory p s) (environment : env.holds p s) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckPrivate.scalarRange s (fun t => (SampleRanged p l slots rb t ∧ KeyCallMemory p t) ∧ env.holds p t) := by
  refine WP.mono_syms (scalarRange_ok s h.context.toContext stable h28 h32 h60 h.ready h.modulus odd) ?_
  rintro t ⟨context, ready, flag, arrays, frame, rest⟩ syms
  rw [h.imported] at flag
  refine ⟨⟨⟨⟨h.context.after_workspace frame rest context.ptr (fun d hd => (stableSlots_at stable hd).1), ready, (arrays 0 (by simp)).trans h.modulus, (arrays 4 (by simp)).trans h.r2,
    h.scalar.after_workspace frame rest, h.significant.after_workspace frame rest, h.outputs.after rest⟩, flag⟩, calls.after rest⟩, env.stable environment ?_ rest syms⟩
  exact frame.mono (by simp [keyCallWrites, keyWrites])

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/EnvironmentPrepareState.lean`, which only this module imported.
section

/-! # Modulus preparation preserves key-generation input and call geometry -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem environmentPrepare_next (env : SampleEnvironment) (prepare : Prog isa) (prep : EnvironmentPrepareLaw env prepare) (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (stable : stableSlots slots = true) (h52 : 52 ∈ slots) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1) (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) (size : rb.length = p.k) (h : KeyScalarInput p slots rb s) (calls : KeyCallMemory p s) (environment : env.holds p s) :
    WP isa prepare s (fun t => KeyPrepared p slots rb t ∧ KeyCallMemory p t) := by
  refine WP.mono (prep.correct s h.context environment calls stable h52 h0 h24 h32 large odd normalized) ?_
  rintro t ⟨context, ready, modulus, r2, frame, rest⟩
  have entropy := h.entropy.after_frame frame rest (by
    intro r hr
    simp only [keyPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact h.entropy.separate
    · rw [size]; exact h.entropyStack.sub_right (Offset.sub_base _ (by decide))
    · rw [size]; exact h.entropyStack.sub_right (Offset.sub_base _ (by decide))
    · rw [size]; exact calls.entropy)
  exact ⟨⟨⟨context, entropy, h.outputs.after rest, by rw [rest.sp]; exact h.entropyStack⟩, ready, modulus, r2⟩, calls.after rest⟩

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/EnvironmentKeyGenerateMainCT.lean`, which only this module imported.
section

/-! The only secret-dependent key-generation branch is scalar acceptance,
whose classification is disclosed by the attempt's returned status. -/

section
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
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedKeyGenerateBodyCT.lean`, which only this module imported.
section

/-! The cached attempt uses only the native public setup prefix before sampling. -/

section
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
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedKeyGenerateFnCT.lean`, which only this module imported.
section

/-! Cached key-generation timing reveals only the reviewed attempt classification. -/

section
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
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedGenerationMemory.lean`, which only this module imported.
section

/-! The immutable canonical context survives silent argument and flag operations. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem cachedGeneration_publicRel (s t : State) : cachedGenerationEnvironment.publicRel s t := trivial

theorem cachedGeneration_afterMem {p : Inputs} {s t : State}
    (h : cachedGenerationEnvironment.holds p s) (mem : t.mem = s.mem) (rest : Rest [] s t) :
    cachedGenerationEnvironment.holds p t := by
  have frame : Frame (keyCallWrites p s) s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact h.after frame (rest.mono (by simp [roundClobbers]))

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem cachedKeyGenerate_contract_ct (prepare sample tail : Prog isa)
    (prep : EnvironmentPrepareLaw cachedGenerationEnvironment prepare)
    (sampler : EnvironmentSampleLaw cachedGenerationEnvironment ScalarLayout.vetted sample)
    (law : EnvironmentTailLaw cachedGenerationEnvironment ScalarLayout.vetted tail) :
    ConstantTime isa (Spec.Ffdh.cachedGenerateKeyContract abi 176).pre
      (Spec.Ffdh.cachedGenerateKeyContract abi 176).pub
      (VG.Impl.Ffdh.Arm.CachedKeyGenerate.code prepare sample tail) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, rb, base, privateValue, publicValue, domain, count, capacity, entropy, domainBytes, entropyBytes, allInputS,cachedS,validS,cachePointer,cacheWords⟩ := cachedKeyGenerate_data s hs
  have inputS := allInputS.input
  have randLength (a : State) (h : (Spec.Ffdh.cachedGenerateKeyContract abi 176).pre a) :
      (stackArg a 4).toNat = (stackArg a 2).toNat := by
    have h := cachedKeyGenerate_plain_pre a h
    sig_pre [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, length, _⟩ := h
    exact length
  sig_pub [Spec.Ffdh.cachedGenerateKeyContract, Spec.Ffdh.cachedGenerateKeySig, Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, _, p4, p5, p6, p7, _, p9, p10, p11, p12⟩ := hp
  rw [randLength s hs, randLength t ht, ← p4, ← p5, ← p6, ← p7] at bytes
  obtain ⟨domEqNat, statusEq⟩ := List.append_inj bytes
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  have recover {a b : List Byte} (h : a.map BitVec.toNat = b.map BitVec.toNat) : a = b := by
    have eq := congrArg (List.map (BitVec.ofNat 8)) h
    simpa only [List.map_map, Function.comp_def, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, List.map_id'] using eq
  have domEq := recover domEqNat
  let rb2 := Spec.Rsa.bytesAt t.mem (State.addr p.entropy) p.k
  have allInputT := cachedKeyGenerate_input t ht (p := p) (rb := rb2)
    (p9.symm.trans base) (p0.symm.trans privateValue) (p2.symm.trans publicValue) (p4.symm.trans domain)
    (by rw [← p6]; exact count) (by rw [← p10]; exact capacity) (p7.symm.trans entropy) (p11.symm.trans cachePointer) inputS.outputY inputS.privateLength ?_ rfl
  · have inputT := allInputT.input
    have cachedT := (cachedKeyGenerate_environment t ht (p9.symm.trans base)
      (p0.symm.trans privateValue) (p2.symm.trans publicValue) (p4.symm.trans domain)
      (by rw [←p6]; exact count) (by rw [←p10]; exact capacity)
      (p11.symm.trans cachePointer) (by rw [←p12]; exact cacheWords)
      (by rw [←p5,←domain]; change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (stackArg s 0)) (stackArg s 1).toNat=p.dom; rw [←domEq,domain]; exact domainBytes)).1
    have status := (List.cons.inj statusEq).1
    rw [← domEq] at status
    simp only [State.addr] at domainBytes entropyBytes
    simp only [count, domain, entropy, domainBytes, entropyBytes] at status
    change Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom) (Spec.Ffdh.vettedScalarOfOctets (Spec.Ffdh.domainOf p.k p.dom) rb) =
      Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom) (Spec.Ffdh.vettedScalarOfOctets (Spec.Ffdh.domainOf p.k p.dom) rb2) at status
    rw [← ScalarLayout.vetted_value inputS.size, ← ScalarLayout.vetted_value inputT.size] at status
    have classification := keyStatus_validity_same (Spec.Ffdh.domainOf p.k p.dom)
      (Spec.Rsa.os2ip ((ScalarLayout.vetted p).encode rb))
      (Spec.Rsa.os2ip ((ScalarLayout.vetted p).encode rb2)) status
    rw [p.privateValid_native, p.privateValid_native] at classification
    have modValid := VG.Proof.Ffdh.domainValid_mod validS
    rw [p.domainP] at modValid
    exact (cachedKeyGenerateFn_ct prepare sample tail cachedGenerationEnvironment ScalarLayout.vetted
      prep sampler law CachedSample.layoutBound cachedGeneration_publicRel cachedGeneration_afterMem
      modValid classification s t tr1 tr2 u v
      ⟨⟨allInputS,cachedS⟩,⟨allInputT,cachedT⟩,sp⟩ e1 e2).1
  · rw [← p5, ← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (stackArg s 0)) (stackArg s 1).toNat = p.dom
    rw [← domEq, domain]
    exact domainBytes


end VG.Proof.Ffdh.Arm
