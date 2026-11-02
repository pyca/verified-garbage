module

public import VerifiedGarbage.Proof.Ffdh.Arm.VettedBoundInstance
public import VerifiedGarbage.Impl.Ffdh.Arm.SampleScalar
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBackend
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Spec.Ffdh.VettedKeyGenerationContract
public import VerifiedGarbage.Proof.Ffdh.Arm.SamplePowerLaw
public import VerifiedGarbage.Impl.Bignum.Arm.SharedWindow
public import VerifiedGarbage.Impl.Ffdh.Arm.KeyPower
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Impl.Ffdh.Arm.KeyGenerate
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleTailLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrograms
public import VerifiedGarbage.Impl.Ffdh.Arm.SampleKeyGenerate

import VerifiedGarbage.Proof.Ffdh.Arm.NormalizedPrepareAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.VettedKeyGenerateTable
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPower
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailInstance
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeMain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.KeyFinish
import VerifiedGarbage.Proof.Ffdh.Arm.ExportResult
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticExternal
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ffdh.Arm.KeyMemory
import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailLaw
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.SampleLaw
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrepareLaw
import VerifiedGarbage.Proof.Ffdh.Arm.SampleKeyGenerateMain
import VerifiedGarbage.Proof.Ffdh.Arm.SampleResult
import VerifiedGarbage.Proof.Ffdh.Arm.Head
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.KeyEntry
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateFn
import VerifiedGarbage.Proof.Ffdh.Arm.Frame
import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
import VerifiedGarbage.Proof.Ffdh.Arm.KeyOutputs
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.SampleSpec
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicSpec
import VerifiedGarbage.Proof.Ffdh.Arm.VettedKeyGenerateInput
import VerifiedGarbage.Proof.Ffdh.Arm.VettedKeyGenerateSat
import VerifiedGarbage.Proof.Ffdh.Arm.SampleBoundLaw
import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalar
import VerifiedGarbage.Proof.Ffdh.Arm.SampleScalarArgs
import VerifiedGarbage.Proof.Ffdh.Arm.SampleCut
import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.TCB.Code
import VerifiedGarbage.Proof.Ffdh.Arm.Context
import VerifiedGarbage.Proof.Ffdh.Arm.SampleScalarCT
import VerifiedGarbage.Proof.Ffdh.Arm.SampleState
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateState
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateCalls
import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.FlagCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalarCT
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.TCB.Mem
import VerifiedGarbage.Proof.Ffdh.Arm.HeadCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyEntryCT
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsConsts
import VerifiedGarbage.Proof.Ffdh.Arm.PrivateSpec
import VerifiedGarbage.Proof.Ffdh.Arm.KeyClassification
import VerifiedGarbage.Proof.Framework.Sig
import Init.Data.BitVec.Basic
import Init.Prelude
import VerifiedGarbage.TCB.Artifact
/-! Every callable Montgomery backend supplies the vetted attempt. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SampleKeyGenerateMainCT.lean`, which only this module imported.
section

/-! The only secret-dependent key-generation branch is scalar acceptance,
whose classification is disclosed by the attempt's returned status. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem sampleKeyGenerateMain_ct (prepare sample tail : Prog isa) (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p) (prep : KeyPrepareLaw prepare) (sampler : SampleLaw env layout sample) (law : SampleTailLaw tail) {p : Inputs} {slots : List Nat} {rb1 rb2 : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots)
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
    refine (keyGeneratePrepare_next prepare prep s stable h0 h24 h32 large odd normalized size h.1.1 h.1.2).and ?_
    refine WP.mono_syms (prep.correct s h.1.1.context h.1.2 stable h0 h24 h32 large odd normalized) ?_
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
    obtain ⟨trace, _⟩ := prep.ct stable h0 h24 h32 large odd normalized s t tr1 tr2 u v
      ⟨⟨h.1.1.1.context, h.1.1.2⟩, ⟨h.2.1.1.1.context, h.2.1.1.2⟩, h.2.2.2⟩ e1 e2
    obtain ⟨_, u', runU, postU⟩ := preparePost s size1 h.1
    obtain ⟨_, v', runV, postV⟩ := preparePost t size2 h.2.1
    obtain ⟨-, rfl⟩ := Exec.det e1 runU
    obtain ⟨-, rfl⟩ := Exec.det e2 runV
    exact ⟨trace, postU, postV, env.public_stable h.2.2.1 (Exec.syms e1) (Exec.syms e2),
      (Exec.sp e1).trans (h.2.2.2.trans (Exec.sp e2).symm)⟩
  have sampleCT := (sampler.ct stable special normalized odd h0 h24 h28 h32 h40 h48 h60 size1 size2 entropySep).mono
    (P' := fun (s t : State) => ((KeyPrepared p slots rb1 s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧
      ((KeyPrepared p slots rb2 t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.1.1.toKeyScalarInput, h.1.2⟩, ⟨h.2.1.1.1.toKeyScalarInput, h.2.1.2⟩, h.2.2⟩) (fun _ _ h => h)
  have sampled := (relCT_keep_sp sampleCT (fun _ _ h => h.2.2.2)).wp (fun s t h =>
    ⟨keyGenerateWP_calls (sampleSample_next env sample layout sampler s stable special h0 h24 h28 h32 h40 h48 h60 size1 entropySep h.1.1.1 h.1.2 normalized odd) h.1.1.2,
     keyGenerateWP_calls (sampleSample_next env sample layout sampler t stable special h0 h24 h28 h32 h40 h48 h60 size2 entropySep h.2.1.1.1 h.2.1.2 normalized odd) h.2.1.1.2⟩)
  have imports := (importAt_ct (p := p) (a := 1) (slot := 40) (countSlot := 44) (k := p.k) stable (by simp [h40]) (by simp [h44])
    (by change BitVec.ofNat 32 p.privateLength = _; rw [privateLength]) (by decide)).mono
    (P' := fun (s t : State) => SampleReady p (layout p) slots rb1 s ∧ SampleReady p (layout p) slots rb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context.toContext, h.1.ready⟩, ⟨h.2.1.context.toContext, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  have ranges := (scalarRange_ct stable (by simp [h28]) (by simp [h32]) (by simp [h60]) odd).mono
    (P' := fun (s t : State) => SampleImported p (layout p) slots rb1 s ∧ SampleImported p (layout p) slots rb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context.toContext, h.1.ready, h.1.modulus⟩, ⟨h.2.1.context.toContext, h.2.1.ready, h.2.1.modulus⟩, h.2.2⟩) (fun _ _ h => h)
  have sigSize {rb : List Byte} (size : rb.length = p.k) : (((layout p).encode rb).drop (layout p).lead).length = (layout p).width := by
    rw [List.length_drop, (layout p).encode_length size]
    rfl
  have branches : RelCT isa (fun s t => (SampleRanged p (layout p) slots rb1 s ∧ KeyCallMemory p s) ∧ (SampleRanged p (layout p) slots rb2 t ∧ KeyCallMemory p t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.ifFlag tail VG.Impl.Ffdh.Arm.Domain.GenerateKey.failScalar)
      (fun _ _ => True) := by
    apply ifFlag_pair_ct (decide (sampleScalarValid p (layout p) rb1))
      (fun s h => by
        have f := h.1.flag
        change s.gpr .r11 = (if sampleScalarValid p (layout p) rb1 then 1 else 0) at f
        simpa only [decide_eq_true_eq] using f)
      (fun s h => by
        have f := h.1.flag
        change s.gpr .r11 = (if sampleScalarValid p (layout p) rb2 then 1 else 0) at f
        simp only [← classification] at f
        simpa only [decide_eq_true_eq] using f)
      (fun _ _ h mem rest => ⟨h.1.after_mem mem rest, h.2.after rest⟩) (fun _ _ h mem rest => ⟨h.1.after_mem mem rest, h.2.after rest⟩)
    · intro _
      exact (law.ct stable h4 h32 h36
        h40 h56 saved (sigSize size1) (sigSize size2) odd outputY).mono
        (fun _ _ h => ⟨⟨⟨h.1.1.context, h.1.1.ready, h.1.1.modulus, h.1.1.r2, h.1.1.significant, h.1.1.outputs⟩, h.1.2⟩,
          ⟨⟨h.2.1.1.context, h.2.1.1.ready, h.2.1.1.modulus, h.2.1.1.r2, h.2.1.1.significant, h.2.1.1.outputs⟩, h.2.1.2⟩, h.2.2⟩)
        (fun _ _ h => h)
    · intro _
      exact (keyFail_ct (fun d hd => (stableSlots_at stable hd).1) (by simp [h32]) (by simp [h36]) (by simp [h40])).mono
        (fun _ _ h => ⟨⟨h.1.1.context.toContext.toArgumentMemory, h.1.1.outputs⟩, ⟨h.2.1.1.context.toContext.toArgumentMemory, h.2.1.1.outputs⟩, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.SampleKeyGenerate.main
  exact prepareCT.seq (sampled.seq ((relCT_chain (keyGenerateCT_calls imports)
        (fun s h => keyGenerateWP_calls (sampleImport_next s stable (by simp [h40]) (by simp [h44]) size1 privateLength h.1) h.2)
        (fun s h => keyGenerateWP_calls (sampleImport_next s stable (by simp [h40]) (by simp [h44]) size2 privateLength h.1) h.2)
        (relCT_chain (keyGenerateCT_calls ranges)
          (fun s h => keyGenerateWP_calls (sampleRange_scalar_next s stable (by simp [h28]) (by simp [h32]) (by simp [h60]) odd h.1) h.2)
          (fun s h => keyGenerateWP_calls (sampleRange_scalar_next s stable (by simp [h28]) (by simp [h32]) (by simp [h60]) odd h.1) h.2)
          branches)).mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)))

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SampleKeyGenerateBodyCT.lean`, which only this module imported.
section

/-! Key generation's public modulus gate and documented retry-status class
account for every branch before native exponentiation. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem sampleKeyGenerateBody_ct (prepare sample tail : Prog isa) (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p)
    (prep : KeyPrepareLaw prepare) (sampler : SampleLaw env layout sample) (law : SampleTailLaw tail) {p : Inputs} {slots : List Nat} {rb1 rb2 : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h48 : 48 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (special : sampleSlots slots)
    (size1 : rb1.length = p.k) (size2 : rb2.length = p.k)
    (classification : Spec.Rsa.modulusValid p.P p.k = true → (sampleScalarValid p (layout p) rb1 ↔ sampleScalarValid p (layout p) rb2))
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (privateLength : p.privateLength = p.k) (outputY : p.output = p.publicValue) :
    RelCT isa (fun s t => ((KeyScalarInput p slots rb1 s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧
      ((KeyScalarInput p slots rb2 t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.head (VG.Impl.Ffdh.Arm.SampleKeyGenerate.main prepare sample tail)) (fun _ _ => True) := by
  let Q := fun (rb : List Byte) (s : State) =>
    ((KeyScalarInput p (60 :: 56 :: slots) rb s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧
      s.z = Spec.Rsa.modulusValid p.P p.k
  have wp (s : State) {rb : List Byte} (size : rb.length = p.k)
      (h : (KeyScalarInput p slots rb s ∧ KeyCallMemory p s) ∧ env.holds p s) :
      WP isa (.seq (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24 ++ VG.Impl.Ffdh.Arm.Domain.domainPointers))
        (.block VG.Impl.Bignum.Arm.modulusCheck)) s (Q rb) := by
    refine WP.mono_syms (head_ok s h.1.1.context stable h0 h24 h32) ?_
    rintro t ⟨context, zero, frame, rest⟩ syms
    refine ⟨⟨⟨⟨context, h.1.1.entropy.after_frame frame rest (by simpa [size] using h.1.1.entropyStack),
      h.1.1.outputs.after rest, by rw [rest.sp]; exact h.1.1.entropyStack⟩, h.1.2.after rest⟩, ?_⟩, zero⟩
    apply env.stable h.2 _ rest syms
    exact frame.mono (by simp [keyCallWrites, keyWrites])
  have head : RelCT isa (fun s t =>
      ((KeyScalarInput p slots rb1 s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧
      ((KeyScalarInput p slots rb2 t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp)
      (.seq (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24 ++ VG.Impl.Ffdh.Arm.Domain.domainPointers))
        (.block VG.Impl.Bignum.Arm.modulusCheck))
      (fun s t => Q rb1 s ∧ Q rb2 t ∧ env.publicRel s t ∧ s.sp = t.sp) := by
    intro s t tr1 tr2 u v h e1 e2
    have timing := (head_ct stable h0 h24 h32) s t tr1 tr2 u v
      ⟨h.1.1.1.context, h.2.1.1.1.context, h.2.2.2⟩ e1 e2
    obtain ⟨_, u', runU, postU⟩ := wp s size1 h.1
    obtain ⟨_, v', runV, postV⟩ := wp t size2 h.2.1
    obtain ⟨-, rfl⟩ := Exec.det e1 runU
    obtain ⟨-, rfl⟩ := Exec.det e2 runV
    exact ⟨timing.1, postU, postV,
      env.public_stable h.2.2.1 (Exec.syms e1) (Exec.syms e2),
      (Exec.sp e1).trans (h.2.2.2.trans (Exec.sp e2).symm)⟩
  have stable' : stableSlots (60 :: 56 :: slots) = true := by
    change (true && (true && stableSlots slots)) = true
    rw [Bool.true_and, Bool.true_and, stable]
  have saved' : ∀ d ∈ 60 :: 56 :: slots, d + 4 ≤ 64 ∨ 68 ≤ d := by
    intro d hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · left; decide
    · left; decide
    · exact saved d hd
  have branches : RelCT isa (fun s t => Q rb1 s ∧ Q rb2 t ∧ env.publicRel s t ∧ s.sp = t.sp)
      (.ite .eq (VG.Impl.Ffdh.Arm.SampleKeyGenerate.main prepare sample tail) (VG.Impl.Ffdh.Arm.Domain.ret 0)) (fun _ _ => True) := by
    apply RelCT.ite (fun s t h => by change some s.z = some t.z; rw [h.1.2, h.2.1.2])
    · intro s t tr1 tr2 u v h e1 e2
      have valid : Spec.Rsa.modulusValid p.P p.k = true := by
        have selected := h.2
        change some s.z = some true at selected
        rw [h.1.1.2] at selected
        exact Option.some.inj selected
      have facts := VG.Proof.Bignum.valid_facts valid p.minLength
      exact sampleKeyGenerateMain_ct prepare sample tail env layout prep sampler law stable' (by simp [h0]) (by simp [h4]) (by simp [h24]) (by simp [h28])
        (by simp [h32]) (by simp [h36]) (by simp [h40]) (by simp [h44]) (by simp [h48]) (by simp) (by simp)
        saved' (by
          intro d hd
          simp only [List.mem_cons] at hd
          rcases hd with rfl | rfl | hd
          · decide
          · decide
          · exact special d hd) size1 size2 (classification valid) entropySep privateLength outputY facts.2.1 facts.1 facts.2.2
        s t tr1 tr2 u v ⟨h.1.1.1, h.1.2.1.1, h.1.2.2⟩ e1 e2
    · exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply RelCT.assoc
  exact head.seq branches

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SampleKeyGenerateFnCT.lean`, which only this module imported.
section

/-! The callable key-generation attempt reveals only its public domain and
buffer layout and the scalar-acceptance class documented by its status. -/

section
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
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SampleKeyGenerateContractCT.lean`, which only this module imported.
section

/-! Native key generation satisfies the shared timing policy for arbitrary
secret entropy tapes with the same public domain and disclosed attempt status. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableConsts tableSym tableWords)

theorem vettedKeyGenerate_contract_ct (prepare sample tail : Prog isa) (env : SampleEnvironment)
    (prep : KeyPrepareLaw prepare) (sampler : SampleLaw env ScalarLayout.vetted sample) (law : SampleTailLaw tail)
    (makeEnvironment : ∀ (s : State),
      (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176).pre s →
      ∀ {p : Inputs} {rb : List Byte}, KeyGenerateFnInput p rb s → env.holds p (entered s))
    (publicEnvironment : ∀ (s t : State), s.syms tableSym = t.syms tableSym → env.publicRel s t) :
    ConstantTime isa (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176).pre
      (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176).pub
      (VG.Impl.Ffdh.Arm.SampleKeyGenerate.code prepare sample tail) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, rb, base, privateValue, publicValue, domain, count, capacity, entropy, domainBytes, entropyBytes, inputS⟩ := vettedKeyGenerate_data_base s hs
  have randLength (a : State) (h : (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176).pre a) :
      (stackArg a 4).toNat = (stackArg a 2).toNat := by
    have h := (vettedKeyGenerate_pre h).1
    sig_pre [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, length, _⟩ := h
    exact length
  have symbol := VettedGroups.consts_singleton_symEq (name := tableSym) (words := tableWords) (pub_consts.mp hp).2
  have hp := (pub_consts.mp hp).1
  sig_pub [Spec.Ffdh.vettedGenerateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, _, p4, p5, p6, p7, _, p9, p10⟩ := hp
  rw [randLength s hs, randLength t ht, ← p4, ← p5, ← p6, ← p7] at bytes
  obtain ⟨domEqNat, statusEq⟩ := List.append_inj bytes
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  have recover {a b : List Byte} (h : a.map BitVec.toNat = b.map BitVec.toNat) : a = b := by
    have eq := congrArg (List.map (BitVec.ofNat 8)) h
    simpa only [List.map_map, Function.comp_def, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, List.map_id'] using eq
  have domEq := recover domEqNat
  let rb2 := Spec.Rsa.bytesAt t.mem (State.addr p.entropy) p.k
  have inputT := vettedKeyGenerate_input t ht (p := p) (rb := rb2)
    (p9.symm.trans base) (p0.symm.trans privateValue) (p2.symm.trans publicValue) (p4.symm.trans domain)
    (by rw [← p6]; exact count) (by rw [← p10]; exact capacity) (p7.symm.trans entropy) inputS.outputY inputS.privateLength ?_ rfl
  · have status := (List.cons.inj statusEq).1
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
    exact (sampleKeyGenerateFn_ct prepare sample tail env ScalarLayout.vetted prep sampler law
      (fun _ => classification) s t tr1 tr2 u v
      ⟨⟨inputS, makeEnvironment s hs inputS⟩, ⟨inputT, makeEnvironment t ht inputT⟩,
        publicEnvironment s t symbol, sp⟩ e1 e2).1
  · rw [← p5, ← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (stackArg s 0)) (stackArg s 1).toNat = p.dom
    rw [← domEq, domain]
    exact domainBytes

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SamplePowerArgs.lean`, which only this module imported.
section

/-! # Load the selected public scalar layout from saved arguments -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem samplePowerArgs_ok (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat}
    (h : SampleContext p l slots s) (_stable : stableSlots slots = true)
    (h56 : 56 ∈ slots) (h32 : 32 ∈ slots) :
    WP isa (.block (VG.Impl.Ffdh.Arm.Domain.powerArgs 56 16 20)) s fun t =>
      (t.gpr .r4 = p.g ∧ t.gpr .r6 = BitVec.ofNat 32 p.k ∧
        t.gpr .r1 = l.start ∧ t.gpr .r2 = BitVec.ofNat 32 l.width ∧ t.mem = s.mem) ∧
      Rest [.r1, .r2, .r4, .r6] s t := by
  have bounds (d : Nat) (hd : d ≤ 68) : d + 4 ≤ 72 := by omega
  have addr (d : Nat) (hd : d ≤ 68) :
      State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega)
  have rb := h.locals.read (bounds 56 (by decide))
  have re := h.locals.read (bounds 16 (by decide))
  have rc := h.locals.read (bounds 20 (by decide))
  have rk := h.locals.read (bounds 32 (by decide))
  have vb := h.saved 56 h56
  have ve := h.scalarStart
  have vc := h.scalarWidth
  have vk := h.saved 32 h32
  change s.mem.readW (off (State.addr s.sp) 56) 32 = p.g at vb
  change s.mem.readW (off (State.addr s.sp) 32) 32 = BitVec.ofNat 32 p.k at vk
  refine withRest_all [.r1, .r2, .r4, .r6] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.Domain.powerArgs
  ffrun [addr 56 (by decide), addr 16 (by decide), addr 20 (by decide), addr 32 (by decide),
    rb, re, rc, rk, vb, ve, vc, vk, off]

theorem samplePowerArgs_input (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat}
    {P : State → Prop} {regions : List Region} {eb : List Byte}
    (A : TwoExp.Montgomery p.base p.len p.w P regions)
    (stable : stableSlots slots = true) (h56 : 56 ∈ slots) (h32 : 32 ∈ slots)
    (context : SampleContext p l slots s) (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (exponent : Octets p.base l.start p.len eb s) (size : eb.length = l.width)
    (hp : P s) (separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr l.start, eb.length⟩ r) :
    WP isa (.block (VG.Impl.Ffdh.Arm.Domain.powerArgs 56 16 20)) s fun t =>
      KeyPower.Input p.base p.g l.start p.len p.w p.P P regions ((p.dom.drop p.k).take p.k) eb t ∧
        t.mem = s.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (samplePowerArgs_ok s context stable h56 h32) ?_
  rintro t ⟨⟨source, count, pointer, exponentCount, mem⟩, rest⟩
  have frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  have readyT := ready.of_mem mem rest ((rest.gpr .r0 (by simp)).trans ready.ptr)
  refine ⟨⟨⟨readyT, ?_, odd, ?_, context.gBytes.after_workspace frame rest,
    exponent.after_workspace frame rest, ?_, ?_, ?_, ?_, source, ?_, pointer, ?_⟩,
    A.stable frame (rest.mono (by simp [roundClobbers])) hp, separate⟩, mem,
    rest.mono (by simp [roundClobbers])⟩
  · rw [mem]; exact modulus
  · rw [mem]; exact r2
  · rw [p.gLength]; have := p.minLength; omega
  · rw [p.gLength]; exact p.width.2.2.2.1
  · rw [size]; exact l.width_bounds.1
  · rw [size]; have := l.width_bounds; have := p.maxLength; omega
  · rw [p.gLength]; exact count
  · rw [size]; exact exponentCount

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SamplePowerInstance.lean`, which only this module imported.
section

/-! # Shared exponentiation consumes the selected public scalar layout -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SampleKeyGenerate
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

def power (b : MontBackend) : Prog isa :=
  VG.Impl.Ffdh.Arm.KeyPower.powerAt
    (VG.Impl.Ffdh.Arm.KeyPower.twoPhase (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul))
    (VG.Impl.Bignum.Arm.SharedWindow.phase (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul)) 56 16 20

private theorem significant_below {p : Inputs} {l : ScalarLayout p} {s : State}
    (h : KeyCallMemory p s) :
    Region.Disjoint ⟨State.addr l.start, l.width⟩ (belowA s.sp 48) := by
  have fit := h.privateFits
  have lead := l.lead_lt
  rw [ScalarLayout.start, VG.Arm.addr_add (by omega)]
  exact h.privateValue.sub_left (Offset.sub_base _ (by unfold ScalarLayout.width; omega))

theorem powerLaw (b : MontBackend) : SamplePowerLaw (power b) := by
  constructor
  · intro s p l slots eb context calls stable h56 h32 ready modulus odd r2 exponent size
    let A := KeyGenerate.arithmetic b p.base s.sp p.len p.w
    let F := KeyGenerate.fallback A (KeyGenerate.timing b p.base s.sp p.len p.w) p.width.2.2.1
    have separate : ∀ r ∈ [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48],
        Region.Disjoint ⟨State.addr l.start, eb.length⟩ r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact exponent.separate
      · rw [size]; exact significant_below calls
    change WP isa (VG.Impl.Ffdh.Arm.KeyPower.powerAt A.phase F.code 56 16 20) s _
    rw [VG.Impl.Ffdh.Arm.KeyPower.powerAt, WP.seq_iff]
    refine WP.mono (samplePowerArgs_input s A stable h56 h32 context ready modulus odd r2 exponent size
      ⟨calls.stack, rfl⟩ separate) ?_
    rintro u ⟨input, memU, restU⟩
    refine WP.mono (KeyPower.power_ok A F u input) ?_
    rintro t ⟨rd, value, m, rr, one, _, frameT, restT⟩
    have frame : Frame [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48] s.mem t.mem := by
      rw [memU] at frameT; exact frameT
    have rest := restU.trans restT
    exact ⟨context.toContext.after_call calls frame rest rd.ptr (fun d hd => (stableSlots_at stable hd).1),
      rd, value, m, rr, one, frame, rest⟩
  · intro p l slots eb1 eb2 stable h56 h32 size1 size2 odd s t tr1 tr2 u v h e1 e2
    let A := KeyGenerate.arithmetic b p.base s.sp p.len p.w
    let F := KeyGenerate.fallback A (KeyGenerate.timing b p.base s.sp p.len p.w) p.width.2.2.1
    have separate (z : State) (eb : List Byte) (hz : SamplePowerInput p l slots eb z)
        (calls : KeyCallMemory p z) (sp : z.sp = s.sp) (size : eb.length = l.width) :
        ∀ r ∈ [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48],
          Region.Disjoint ⟨State.addr l.start, eb.length⟩ r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hz.exponent.separate
      · rw [size, ← sp]; exact significant_below calls
    have args (z : State) (eb : List Byte) (hz : SamplePowerInput p l slots eb z)
        (calls : KeyCallMemory p z) (sp : z.sp = s.sp) (size : eb.length = l.width) :=
      samplePowerArgs_input z A stable h56 h32 hz.context hz.ready hz.modulus odd hz.r2 hz.exponent size
        ⟨calls.stack, sp⟩ (separate z eb hz calls sp size)
    have fit : arrAt p.w 3 + 32 ≤ 8 * p.len := by
      have f := p.width.2.2.1
      simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at *
      omega
    have hn : 0 < 2 * p.w := by have := p.width.1; omega
    have initial : RelCT isa (fun z z' =>
        (SamplePowerInput p l slots eb1 z ∧ KeyCallMemory p z ∧ z.sp = s.sp) ∧
        (SamplePowerInput p l slots eb2 z' ∧ KeyCallMemory p z' ∧ z'.sp = s.sp) ∧ z.sp = z'.sp)
        (VG.Impl.Ffdh.Arm.KeyPower.powerAt A.phase F.code 56 16 20) (fun _ _ => True) := by
      unfold VG.Impl.Ffdh.Arm.KeyPower.powerAt
      exact relCT_chain
        ((powerArgs_ct 56 16 20).mono (fun _ _ k => k.2.2) (fun _ _ _ => trivial))
        (fun z k => WP.mono (args z eb1 k.1 k.2.1 k.2.2 size1) fun _ a => a.1)
        (fun z k => WP.mono (args z eb2 k.1 k.2.1 k.2.2 size2) fun _ a => a.1)
        (KeyPower.power_ct A (KeyGenerate.timing b p.base s.sp p.len p.w) F fit hn
          (by rw [size1]; exact l.width_bounds.1) (size1.trans size2.symm))
    exact initial s t tr1 tr2 u v ⟨⟨h.1.1, h.1.2, rfl⟩, ⟨h.2.1.1, h.2.1.2, h.2.2.symm⟩, h.2.2⟩ e1 e2

end VG.Proof.Ffdh.Arm.SampleKeyGenerate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SampleCallTail.lean`, which only this module imported.
section

/-! # Finish a key-generation attempt using shared arithmetic calls -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem sampleCallTail_ok {power : Prog isa} (law : SamplePowerLaw power) (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {xb eb : List Byte}
    (h : SampleContext p l slots s) (calls : KeyCallMemory p s) (stable : stableSlots slots = true)
    (h4 : 4 ∈ slots) (h32 : 32 ∈ slots)
    (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h56 : 56 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (scalar : Octets p.base p.privateValue p.len xb s) (scalarSize : xb.length = p.k)
    (significant : Octets p.base l.start p.len eb s) (significantSize : eb.length = l.width)
    (significantValue : Spec.Rsa.os2ip eb = Spec.Rsa.os2ip xb)
    (outputs : KeyOutputs p s) (outputY : p.output = p.publicValue) :
    WP isa (VG.Impl.Ffdh.Arm.KeyGenerate.tail power) s fun t =>
      t.gpr .r0 = (if keyAccepted p xb then 1 else 3) ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.k =
        (if keyAccepted p xb then xb else List.replicate p.k 0) ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.publicValue) p.k =
        (if keyAccepted p xb then Spec.Rsa.i2osp (keyPower p xb) p.k else List.replicate p.k 0) ∧
      Frame (keyCallWrites p s) s.mem t.mem := by
  have fits : Proof.Rsa.Mont.arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
  rw [VG.Impl.Ffdh.Arm.KeyGenerate.tail, WP.seq_iff]
  refine WP.mono (law.correct s h calls stable h56 h32 ready modulus odd r2 significant significantSize) ?_
  rintro u ⟨contextU, readyU, powerU, modU, _, _, frameU, restU⟩
  rw [significantValue] at powerU
  change numAt u.mem (State.addr p.base) p.w 6 = keyPower p xb at powerU
  rw [WP.seq_iff]
  refine WP.mono (inRange_ok u readyU (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 6)
    (by decide) (by rw [modU]; exact odd)) ?_
  rintro v ⟨readyV, flag, arraysV, frameV, restV⟩
  have contextV := contextU.after_workspace frameV restV readyV.ptr (fun d hd => (stableSlots_at stable hd).1)
  have powerV := (arraysV 6 (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)).trans powerU
  have flagV : v.gpr .r11 = if keyAccepted p xb then 1 else 0 := by
    rw [powerU, modU] at flag
    simpa only [keyAccepted, decide_eq_true_eq] using flag
  rw [WP.seq_iff]
  refine WP.mono (saveResult_ok v contextV.locals) ?_
  rintro w ⟨⟨_, resultW, frameW⟩, restW⟩
  have ptrW := (restW.gpr .r0 (by simp)).trans contextV.ptr
  have contextW := contextV.after_local (by decide : 64 + 4 ≤ 72) frameW restW ptrW
    (fun d hd => (stableSlots_at stable hd).1) saved
  have readyW := readyV.after_external frameW (by
    intro r hr; rw [List.mem_singleton] at hr; subst r
    exact contextV.locals.separate.symm.sub_right (Offset.sub_base _ (by decide))) (by
    intro r hr; rw [List.mem_singleton] at hr; subst r
    simpa only [off, BitVec.add_zero] using
      Offset.disjoint (State.addr v.sp) (d := 0) (n := 4) (e := 64) (k := 4) (by left; decide) (by decide) (by decide)) restW ptrW
  have powerW := (readyW.2.number fits (by decide : 6 < 8)).trans powerV
  have powerFits : numAt w.mem (State.addr p.base) p.w 6 < 2 ^ (8 * p.k) := by
    rw [powerW, keyPower, VG.Proof.Bignum.powMod_eq]
    have large := ready.modulus
    rw [modulus] at large
    exact Nat.lt_trans (Nat.mod_lt _ (by omega)) p.modulusBound
  rw [WP.seq_iff]
  refine WP.mono (exportResult_ok w contextW h4 h32 readyW.1
    (by rw [outputY]; exact ((outputs.publicBuffer.after restU).after restV).after restW)
    (by rw [outputY]; exact outputs.publicWorkspace.symm) powerFits) ?_
  rintro z ⟨publicZ, frameZ, restZ⟩
  rw [powerW, outputY] at publicZ
  rw [outputY] at frameZ
  have outW := ((outputs.after restU).after restV).after restW
  have contextZ := contextW.toArgumentMemory.after_output frameZ restZ outW.publicDomain outW.publicStack
    (fun d hd => (stableSlots_at stable hd).1)
  have resultZ : z.mem.readW (off (State.addr z.sp) 64) 32 = if keyAccepted p xb then 1 else 0 := by
    rw [restZ.sp, frameZ.readW (r := ⟨off (State.addr w.sp) 64, 4⟩) (Region.contains_self _ _)
      (by simpa using outW.publicStack.sub_left (Offset.sub_base _ (by decide : 64 + 4 ≤ 72))) (by decide), restW.sp, resultW, flagV]
  refine WP.mono (keyFinish_ok z (keyAccepted p xb) contextZ (fun d hd => (stableSlots_at stable hd).1)
    h32 h36 h40 (outW.after restZ) resultZ) ?_
  rintro t ⟨status, privateT, publicT, frameT, _⟩
  have privateU := scalar.after_call frameU restU (by simpa only [scalarSize] using calls.privateValue)
  have privateW := (privateU.after_workspace frameV restV).after_frame frameW restW (by
    intro r hr; rw [List.mem_singleton] at hr; subst r
    simpa only [scalarSize, restV.sp, restU.sp] using
      outputs.privateStack.symm.sub_right (Offset.sub_base _ (by decide : 64 + 4 ≤ 72)))
  have privateZ := privateW.after_frame frameZ restZ (by simpa only [scalarSize, List.mem_singleton, forall_eq] using outputs.separate)
  have privateBytesZ := privateZ.bytes
  rw [scalarSize] at privateBytesZ
  rw [privateBytesZ] at privateT
  rw [publicZ] at publicT
  refine ⟨status, privateT, publicT, ?_⟩
  have fullU : Frame (keyCallWrites p s) s.mem u.mem := frameU.mono (by simp [keyCallWrites, keyWrites])
  have fullV : Frame (keyCallWrites p s) u.mem v.mem := frameV.mono (by simp [keyCallWrites, keyWrites])
  have fullW : Frame (keyCallWrites p s) v.mem w.mem := frameW.sub (by
    intro r hr; rw [List.mem_singleton] at hr; subst r
    refine ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], ?_⟩
    rw [restV.sp, restU.sp]
    exact Offset.sub_base _ (by decide))
  exact (((fullU.trans fullV).trans fullW).trans (frameZ.mono (by simp [keyCallWrites, keyWrites]))).trans
    (frameT.mono (by simp [keyCallWrites, keyWrites]))

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SampleCallTailCT.lean`, which only this module imported.
section

/-! # Key-generation finish timing with shared exponentiation -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt Operand)

theorem sampleCallPower_next {power : Prog isa} (law : SamplePowerLaw power) (s : State)
    {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {eb : List Byte}
    (stable : stableSlots slots = true)
    (h32 : 32 ∈ slots) (h56 : 56 ∈ slots) (size : eb.length = l.width) (odd : p.P % 2 = 1)
    (h : SamplePowerInput p l slots eb s ∧ KeyCallMemory p s) :
    WP isa power s (KeyRangeInput p slots) := by
  refine WP.mono (law.correct s h.1.context h.2 stable h56 h32 h.1.ready h.1.modulus odd
    h.1.r2 h.1.exponent size) ?_
  rintro t ⟨context, ready, value, modulus, _, _, _, rest⟩
  refine ⟨⟨context, ready, h.1.outputs.after rest, ?_⟩, modulus⟩
  rw [value, VG.Proof.Bignum.powMod_eq]
  have large := h.1.ready.modulus
  rw [h.1.modulus] at large
  exact Nat.lt_trans (Nat.mod_lt _ (by omega)) p.modulusBound

theorem sampleCallTail_ct {power : Prog isa} (law : SamplePowerLaw power)
    {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {eb1 eb2 : List Byte}
    (stable : stableSlots slots = true) (h4 : 4 ∈ slots) (h32 : 32 ∈ slots)
    (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h56 : 56 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (size1 : eb1.length = l.width) (size2 : eb2.length = l.width)
    (odd : p.P % 2 = 1) (outputY : p.output = p.publicValue) :
    RelCT isa (fun s t => (SamplePowerInput p l slots eb1 s ∧ KeyCallMemory p s) ∧
      (SamplePowerInput p l slots eb2 t ∧ KeyCallMemory p t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.KeyGenerate.tail power) (fun _ _ => True) := by
  have range := (inRange_ct (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 6) (by decide)).mono
    (P' := fun (s t : State) => KeyRangeInput p slots s ∧ KeyRangeInput p slots t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.KeyGenerate.tail
  exact relCT_chain (law.ct stable h56 h32 size1 size2 odd)
    (sampleCallPower_next law · stable h32 h56 size1 odd)
    (sampleCallPower_next law · stable h32 h56 size2 odd)
    (relCT_chain range (keyRange_next · stable odd) (keyRange_next · stable odd)
      (keyExportFinish_ct stable h4 h32 h36 h40 saved outputY))

theorem sampleCallTail_law {power : Prog isa} (law : SamplePowerLaw power) :
    SampleTailLaw (VG.Impl.Ffdh.Arm.KeyGenerate.tail power) where
  correct := sampleCallTail_ok law
  ct := sampleCallTail_ct law

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SampleTailInstance.lean`, which only this module imported.
section

/-! The selected public scalar width uses the existing shared exponentiator. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SampleKeyGenerate
open VG VG.Arm VG.Proof.Bignum.Arm

def tail (b : MontBackend) : Prog isa :=
  VG.Impl.Ffdh.Arm.KeyGenerate.tail (power b)

theorem tailLaw (b : MontBackend) : SampleTailLaw (tail b) :=
  sampleCallTail_law (powerLaw b)

end VG.Proof.Ffdh.Arm.SampleKeyGenerate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SamplePrograms.lean`, which only this module imported.
section

/-! Sampling policies reuse the shared Montgomery key-generation program. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SampleKeyGenerate
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Bignum.Arm

def code (b : MontBackend) (sample : Prog isa) : Prog isa :=
  VG.Impl.Ffdh.Arm.SampleKeyGenerate.code (KeyGenerate.prepare b) sample (tail b)

theorem stack_ok (b : MontBackend) (sample : Prog isa)
    (sampleStack : FrameStack.armStack sample = 0) : FrameStack.armStack (code b sample) ≤ 176 := by
  have bound := b.stackOk
  have s0 : FrameStack.armStack (PublicFn.prepare) = 0 := by rfl
  have s1 : FrameStack.armStack (importModulus) = 0 := by rfl
  have s2 : FrameStack.armStack (precomputeInverse) = 0 := by rfl
  have s3 : FrameStack.armStack (NormalizedR2.init) = 0 := by rfl
  have s4 : FrameStack.armStack (doubleLoop) = 0 := by rfl
  have s5 : FrameStack.armStack (smallConst 7 1) = 0 := by rfl
  have s6 : FrameStack.armStack (smallConst 5 2) = 0 := by rfl
  have s7 : FrameStack.armStack (selectArray 6 6 1) = 0 := by rfl
  have s8 : FrameStack.armStack (VG.Impl.Bignum.Arm.TwoExp.candidate) = 0 := by rfl
  have s9 : FrameStack.armStack (SharedWindow.tablePrepare) = 0 := by rfl
  have s10 : FrameStack.armStack (entryCopy 1) = 0 := by rfl
  have s11 : FrameStack.armStack (scan) = 0 := by rfl
  have s12 : FrameStack.armStack (expByteHead) = 0 := by rfl
  have s15 : FrameStack.armStack (VG.Impl.Ffdh.Arm.Domain.importAt 1 40 44) = 0 := by rfl
  have s16 : FrameStack.armStack (VG.Impl.Ffdh.Arm.Domain.CheckPrivate.scalarRange) = 0 := by rfl
  have s17 : FrameStack.armStack (VG.Impl.Ffdh.Arm.inRange 6) = 0 := by rfl
  have s18 : FrameStack.armStack (VG.Impl.Ffdh.Arm.Domain.Exchange.exportResult) = 0 := by rfl
  have s19 : FrameStack.armStack (VG.Impl.Ffdh.Arm.Domain.GenerateKey.finish) = 0 := by rfl
  have s20 : FrameStack.armStack (VG.Impl.Ffdh.Arm.Domain.GenerateKey.failScalar) = 0 := by rfl
  have s21 : FrameStack.armStack (VG.Impl.Ffdh.Arm.powerImport) = 0 := by rfl
  have s22 : FrameStack.armStack (VG.Impl.Ffdh.Arm.detectTwo) = 0 := by rfl
  simp only [code, KeyGenerate.prepare, tail, power,
    VG.Impl.Ffdh.Arm.SampleKeyGenerate.code, VG.Impl.Ffdh.Arm.SampleKeyGenerate.main,
    VG.Impl.Ffdh.Arm.KeyGenerate.tail,
    VG.Impl.Ffdh.Arm.framed, VG.Impl.Ffdh.Arm.Domain.head,
    VG.Impl.Ffdh.Arm.Domain.ifFlag, VG.Impl.Ffdh.Arm.Domain.testFlag,
    VG.Impl.Ffdh.Arm.Domain.ret, VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt,
    VG.Impl.Ffdh.Arm.NormalizedPrepare.code,
    NormalizedPrecompute.precompute, NormalizedR2.r2, SharedR2.squares,
    VG.Impl.Ffdh.Arm.KeyPower.powerAt, VG.Impl.Ffdh.Arm.KeyPower.power,
    VG.Impl.Ffdh.Arm.KeyPower.phase, VG.Impl.Ffdh.Arm.KeyPower.twoPhase,
    VG.Impl.Bignum.Arm.TwoExp.phase, VG.Impl.Bignum.Arm.TwoExp.initial,
    VG.Impl.Bignum.Arm.TwoExp.bytes, VG.Impl.Bignum.Arm.TwoExp.bits,
    VG.Impl.Bignum.Arm.TwoExp.round, VG.Impl.Bignum.Arm.TwoExp.bit,
    SharedWindow.phase, SharedWindow.init, SharedWindow.tableBuild,
    SharedWindow.tableBody, SharedWindow.bytes, SharedWindow.bits,
    SharedWindow.round, SharedWindow.bit, SharedWindow.apply,
    MontCall.op, FrameStack.armStack,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul,
    Nat.max_self, Nat.max_zero, Nat.zero_max,
    sampleStack, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s15, s16, s17, s18, s19, s20, s21, s22]
  omega

end VG.Proof.Ffdh.Arm.SampleKeyGenerate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SampleKeyGenerateBody.lean`, which only this module imported.
section

/-! The native key-generation body is safe for every domain encoding and
returns the specified key-generation result for valid public moduli. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem sampleKeyGenerateBody_ok (prepare sample tail : Prog isa) (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p)
    (prep : KeyPrepareLaw prepare) (sampler : SampleLaw env layout sample) (law : SampleTailLaw tail) (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (h : Context p slots s) (environment : env.holds p s) (calls : KeyCallMemory p s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h48 : 48 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (sampleSlots : ∀ d ∈ slots, d + 4 ≤ 16 ∨ 24 ≤ d ∧ d + 4 ≤ 68)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr s.sp, 72⟩)
    (outputs : KeyOutputs p s)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (privateLength : p.privateLength = p.k) (outputY : p.output = p.publicValue) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.head (VG.Impl.Ffdh.Arm.SampleKeyGenerate.main prepare sample tail)) s fun t =>
      (Spec.Rsa.modulusValid p.P p.k = true → sampleResult p (layout p) rb t) ∧
      Frame (keyCallWrites p s) s.mem t.mem := by
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply WP.assoc
  rw [WP.seq_iff]
  refine WP.mono_syms (head_ok s h stable h0 h24 h32) ?_
  rintro u ⟨context, zero, frame, rest⟩ syms
  have entryFrame : Frame (keyCallWrites p s) s.mem u.mem := frame.mono (by simp [keyCallWrites, keyWrites])
  have environmentU := env.stable environment entryFrame (rest.mono (by simp [roundClobbers])) syms
  by_cases valid : Spec.Rsa.modulusValid p.P p.k = true
  · refine WP.ite true (by change some u.z = some true; rw [zero, valid]) ?_ (by intro hf; cases hf)
    intro _
    have facts := VG.Proof.Bignum.valid_facts valid p.minLength
    have stable' : stableSlots (60 :: 56 :: slots) = true := by
      change (true && (true && stableSlots slots)) = true
      rw [Bool.true_and, Bool.true_and, stable]
    have saved' : ∀ d ∈ 60 :: 56 :: slots, d + 4 ≤ 64 ∨ 68 ≤ d := by
      intro d hd
      simp only [List.mem_cons] at hd
      rcases hd with rfl | rfl | hd
      · left; decide
      · left; decide
      · exact saved d hd
    have entropyU := entropy.after_frame frame rest (by simpa [size] using entropyStack)
    refine WP.mono (sampleKeyGenerateMain_ok prepare sample tail env layout prep sampler law u context environmentU (calls.after rest) stable' (by simp [h0]) (by simp [h4]) (by simp [h24])
      (by simp [h28]) (by simp [h32]) (by simp [h36]) (by simp [h40]) (by simp [h44]) (by simp [h48])
      (by simp) (by simp) saved' (by
        intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with rfl | rfl | hd
        · decide
        · decide
        · exact sampleSlots d hd) facts.2.1 facts.1 facts.2.2 entropyU size (by rw [rest.sp]; exact entropyStack)
      (outputs.after rest) entropySep privateLength outputY) ?_
    rintro t ⟨result, privateT, publicT, frameT⟩
    exact ⟨fun _ => ⟨result, privateT, publicT⟩, entryFrame.trans (by simpa only [keyCallWrites, keyWrites, rest.sp] using frameT)⟩
  · have invalid : Spec.Rsa.modulusValid p.P p.k = false := Bool.eq_false_iff.mpr valid
    refine WP.ite false (by change some u.z = some false; rw [zero, invalid]) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (ret_ok u 0 (by decide)) ?_
    rintro t ⟨⟨_, mem⟩, _⟩
    exact ⟨fun hv => (valid hv).elim, by rw [mem]; exact entryFrame⟩

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SampleKeyGenerateFn.lean`, which only this module imported.
section

/-! AAPCS key generation from caller-provided entropy with native rejection. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem sampleKeyGenerateEntered_ok (prepare sample tail : Prog isa) (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p)
    (prep : KeyPrepareLaw prepare) (sampler : SampleLaw env layout sample) (law : SampleTailLaw tail) (s : State) {p : Inputs} {rb : List Byte}
    (h : ArgumentMemory p [] s) (environment : env.holds p s) (calls : KeyCallMemory p s) (incoming : KeyIncoming p s)
    (privateValue : s.gpr .r0 = p.privateValue) (publicValue : s.gpr .r2 = p.publicValue)
    (outputY : p.output = p.publicValue) (privateLength : p.privateLength = p.k)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr s.sp, 72⟩)
    (outputs : KeyOutputs p s)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩) :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.entry)
      (VG.Impl.Ffdh.Arm.Domain.head (VG.Impl.Ffdh.Arm.SampleKeyGenerate.main prepare sample tail))) s fun t =>
      (Spec.Rsa.modulusValid p.P p.k = true → sampleResult p (layout p) rb t) ∧
      Frame (keyCallWrites p s) s.mem t.mem := by
  rw [WP.seq_iff]
  refine WP.mono_syms (withAllRest (keyEntry_ok s h incoming privateValue publicValue outputY privateLength)) ?_
  rintro u ⟨⟨context, frame⟩, rest⟩ syms
  have entryFrame : Frame (keyCallWrites p s) s.mem u.mem := frame.mono (by simp [keyCallWrites, keyWrites])
  have environmentU := env.stable environment entryFrame (rest.mono (by simp [roundClobbers])) syms
  have entropyU := entropy.after_frame frame rest (by simpa [size] using entropyStack)
  refine WP.mono (sampleKeyGenerateBody_ok prepare sample tail env layout prep sampler law u context environmentU (calls.after rest) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by intro d hd; revert d; decide) (by intro d hd; revert d; decide)
    entropyU size (by rw [rest.sp]; exact entropyStack) (outputs.after rest) entropySep privateLength outputY) ?_
  rintro t ⟨result, frameT⟩
  exact ⟨result, entryFrame.trans (by simpa only [keyCallWrites, keyWrites, rest.sp] using frameT)⟩

theorem sampleKeyGenerateFn_ok (prepare sample tail : Prog isa) (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p)
    (prep : KeyPrepareLaw prepare) (sampler : SampleLaw env layout sample) (law : SampleTailLaw tail) (s : State) {p : Inputs} {rb : List Byte} (h : KeyGenerateFnInput p rb s) (environment : env.holds p (entered s)) :
    WP isa (VG.Impl.Ffdh.Arm.SampleKeyGenerate.code prepare sample tail) s fun t => abiPreserved s t ∧
      (Spec.Rsa.modulusValid p.P p.k = true → sampleResult p (layout p) rb t) := by
  unfold VG.Impl.Ffdh.Arm.SampleKeyGenerate.code
  refine framed_of_separate _ s h.stackFits (keyCallWrites p (entered s))
    (fun m status => Spec.Rsa.modulusValid p.P p.k = true →
      status = sampleMainFlag p (layout p) rb ∧ Spec.Rsa.bytesAt m (State.addr p.privateValue) p.k =
        (if sampleSuccess p (layout p) rb then (layout p).encode rb else List.replicate p.k 0) ∧
      Spec.Rsa.bytesAt m (State.addr p.publicValue) p.k =
        (if sampleSuccess p (layout p) rb then Spec.Rsa.i2osp (keyPower p ((layout p).encode rb)) p.k else List.replicate p.k 0)) ?_ ?_
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact h.saved r hr
    · have eq := List.mem_singleton.mp hr; subst r; exact h.savedCall
  refine WP.mono (sampleKeyGenerateEntered_ok prepare sample tail env layout prep sampler law (entered s) h.args environment h.calls h.incoming h.privateValue h.publicValue h.outputY h.privateLength
    h.entropy h.size h.entropyStack h.outputs h.entropySep) ?_
  rintro t ⟨result, frame⟩
  exact ⟨frame, result⟩

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/VettedKeyGeneratePost.lean`, which only this module imported.
section

/-! The selected scalar layout satisfies the separately reviewed vetted policy. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem vettedKeyGenerate_post (s t : State) {p : Inputs} {rb : List Byte}
    (privateValue : s.gpr .r0 = p.privateValue) (publicValue : s.gpr .r2 = p.publicValue)
    (domain : stackArg s 0 = p.domain) (count : (stackArg s 2).toNat = p.k)
    (entropy : stackArg s 3 = p.entropy)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (stackArg s 1).toNat = p.dom)
    (entropyBytes : Spec.Rsa.bytesAt s.mem (State.addr p.entropy) p.k = rb)
    (randLength : (stackArg s 4).toNat = (stackArg s 2).toNat) (size : rb.length = p.k)
    (result : Spec.Rsa.modulusValid p.P p.k = true → sampleResult p (ScalarLayout.vetted p) rb t) :
    (Spec.Ffdh.vettedGenerateKeyContract abi 176).post s t := by
  sig_post [Spec.Ffdh.vettedGenerateKeyContract, Spec.Ffdh.generateKeySig, abi,
    argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  simp only [State.addr] at domainBytes entropyBytes
  simp only [randLength, count, domain, entropy, domainBytes, entropyBytes, privateValue, publicValue]
  intro valid
  have modValid := VG.Proof.Ffdh.domainValid_mod valid
  rw [p.domainP] at modValid
  have output := sampleResult_spec size valid (result modValid)
  rwa [ScalarLayout.vetted_value size] at output

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/VettedKeyGenerateCorrect.lean`, which only this module imported.
section

/-! The callable attempt implements the reviewed vetted scalar distribution. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableConsts)

theorem vettedKeyGenerate_correct (prepare sample tail : Prog isa) (env : SampleEnvironment)
    (prep : KeyPrepareLaw prepare) (sampler : SampleLaw env ScalarLayout.vetted sample)
    (law : SampleTailLaw tail)
    (makeEnvironment : ∀ (s : State),
      (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176).pre s →
      ∀ {p : Inputs} {rb : List Byte}, KeyGenerateFnInput p rb s → env.holds p (entered s))
    (s : State) (pre : (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176).pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.Arm.SampleKeyGenerate.code prepare sample tail) s tr t ∧
      abiPreserved s t ∧
      (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176).post s t := by
  obtain ⟨p, rb, _, privateValue, publicValue, domain, count, _, entropy, domainBytes, entropyBytes, input⟩ :=
    vettedKeyGenerate_data_base s pre
  obtain ⟨tr, t, run, preserved, result⟩ := sampleKeyGenerateFn_ok prepare sample tail env
    ScalarLayout.vetted prep sampler law s input (makeEnvironment s pre input)
  refine ⟨tr, t, run, preserved, post_consts.mpr ?_⟩
  have randLength : (stackArg s 4).toNat = (stackArg s 2).toNat := by
    have old := (vettedKeyGenerate_pre pre).1
    sig_pre [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi,
      argRegs, reduceClassify, Loc.val, State.addr] at old
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, length, _⟩ := old
    exact length
  exact vettedKeyGenerate_post (stripConsts tableConsts s) t privateValue publicValue
    domain count entropy domainBytes entropyBytes randLength input.size result

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/VettedKeyGenerateVerified.lean`, which only this module imported.
section

/-! Vetted attempts combine the reviewed functional and timing policies. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableConsts tableSym)

theorem vettedKeyGenerate_verified (prepare sample tail : Prog isa) (env : SampleEnvironment)
    (prep : KeyPrepareLaw prepare) (sampler : SampleLaw env ScalarLayout.vetted sample)
    (law : SampleTailLaw tail)
    (makeEnvironment : ∀ (s : State),
      (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176).pre s →
      ∀ {p : Inputs} {rb : List Byte}, KeyGenerateFnInput p rb s → env.holds p (entered s))
    (publicEnvironment : ∀ (s t : State), s.syms tableSym = t.syms tableSym → env.publicRel s t) :
    Verified target (VG.Impl.Ffdh.Arm.SampleKeyGenerate.code prepare sample tail)
      (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176) :=
  ⟨vettedKeyGenerate_correct prepare sample tail env prep sampler law makeEnvironment,
    vettedKeyGenerate_contract_ct prepare sample tail env prep sampler law makeEnvironment publicEnvironment,
    vettedKeyGenerate_sat⟩

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SampleScalar.lean`, which only this module imported.
section

/-! A public sampling bound drives the existing fixed byte-cutting instructions. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem sampleScalar_ok (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p) (bound : Prog isa)
    (law : SampleBoundLaw env layout bound) (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (h : Context p slots s) (environment : env.holds p s)
    (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) (odd : p.P % 2 = 1) (stable : stableSlots slots = true) (special : sampleSlots slots)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h40 : 40 ∈ slots) (h48 : 48 ∈ slots) (h60 : 60 ∈ slots)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr s.sp, 72⟩)
    (output : OutputBuffer p.privateValue p.k s)
    (domainSep : Region.Disjoint ⟨State.addr p.domain, p.dom.length⟩ ⟨State.addr p.privateValue, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.privateValue, p.k⟩)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩) :
    WP isa (VG.Impl.Ffdh.Arm.SampleScalar.code bound) s fun t =>
      SampleContext p (layout p) slots t ∧ Octets p.base p.entropy p.len rb t ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.k = (layout p).encode rb ∧
      Frame (keyScalarWrites p s) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.SampleScalar.code, WP.seq_iff]
  refine WP.mono (law.correct s h environment normalized odd stable special h24 h28 h32 h60) ?_
  rintro u ⟨contextU, widthU, maskU, frameU, restU⟩
  have entropyU := entropy.after_frame frameU restU (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [size]
    rcases hr with rfl | rfl <;> exact entropyStack.sub_right (Offset.sub_base _ (by decide)))
  rw [WP.seq_iff]
  refine WP.mono (sampleScalarArgs_retained u contextU stable special widthU maskU h32 h40 h48) ?_
  rintro v ⟨contextV, dstV, srcV, countV, zeroV, frameV, restV⟩
  have entropyV := entropyU.after_frame frameV restV (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    rw [size, restU.sp]
    exact entropyStack.sub_right (Offset.sub_base _ (by decide)))
  rw [WP.seq_iff]
  refine WP.mono (sampleCut_ok v contextV (fun d hd => (stableSlots_at stable hd).1)
    entropyV size ((output.after restU).after restV) domainSep (by rw [restV.sp, restU.sp]; exact stackSep)
    entropySep srcV dstV countV zeroV) ?_
  rintro w ⟨contextW, entropyW, bytesW, frameW, restW⟩
  refine WP.mono (localLoad_ok w .r0 contextW.locals (by decide : 0 + 4 ≤ 72)) ?_
  rintro t ⟨loaded, memT, restT⟩
  have ptr : t.gpr .r0 = p.base := loaded.trans (contextW.saved 0 h0)
  have memFrame : Frame [] w.mem t.mem := by rw [memT]; exact Frame.refl _ _
  have args := contextW.toArgumentMemory.after_frame memFrame restT (by simp) (by simp)
  have contextT : SampleContext p (layout p) slots t := by
    refine ⟨⟨args, ptr⟩, ?_, ?_, ?_⟩
    · rw [memT, restT.sp]; exact contextW.scalarStart
    · rw [memT, restT.sp]; exact contextW.scalarWidth
    · rw [memT, restT.sp]; exact contextW.scalarMask
  have entropyT := entropyW.after_frame memFrame restT (by simp)
  have fullU : Frame (keyScalarWrites p s) s.mem u.mem := frameU.mono (by simp [keyScalarWrites])
  have fullV : Frame (keyScalarWrites p s) u.mem v.mem := by
    rw [restU.sp] at frameV
    exact frameV.mono (by simp [keyScalarWrites])
  have fullW : Frame (keyScalarWrites p s) v.mem w.mem := frameW.mono (by simp [keyScalarWrites])
  refine ⟨contextT, entropyT, by rw [memT]; exact bytesW, ?_, ?_⟩
  · rw [memT]
    exact (fullU.trans fullV).trans fullW
  · exact restU.trans ((restV.mono (by simp [roundClobbers])).trans
      ((restW.mono (by simp [roundClobbers])).trans (restT.mono (by simp [roundClobbers]))))

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SampleSample.lean`, which only this module imported.
section

/-! Scalar sampling preserves the prepared RSA modulus and exposes both the
full output encoding and its public-width significant suffix. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem sampleSample_ok (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p) (bound : Prog isa)
    (law : SampleBoundLaw env layout bound) (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (h : Context p slots s) (environment : env.holds p s)
    (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) (odd : p.P % 2 = 1) (stable : stableSlots slots = true) (special : sampleSlots slots)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h40 : 40 ∈ slots) (h48 : 48 ∈ slots) (h60 : 60 ∈ slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr s.sp, 72⟩)
    (outputs : KeyOutputs p s)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩) :
    WP isa (VG.Impl.Ffdh.Arm.SampleScalar.code bound) s fun t =>
      SampleContext p (layout p) slots t ∧ ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 0 = p.P ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P ∧
      Octets p.base p.privateValue p.len ((layout p).encode rb) t ∧
      Octets p.base (layout p).start p.len (((layout p).encode rb).drop (layout p).lead) t ∧
      Frame (keyScalarWrites p s) s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (sampleScalar_ok env layout bound law s h environment normalized odd stable special h0 h24 h28 h32 h40 h48 h60 entropy size entropyStack
    outputs.privateBuffer outputs.privateDomain outputs.privateStack entropySep) ?_
  rintro t ⟨context, _, bytes, frame, rest⟩
  have workspaceSep (r : Region) (hr : r ∈ keyScalarWrites p s) :
      (⟨State.addr p.base, 8 * p.len⟩ : Region).Disjoint r := by
    simp only [keyScalarWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.locals.separate.symm.sub_right (Offset.sub_base _ (by decide))
    · exact h.locals.separate.symm.sub_right (Offset.sub_base _ (by decide))
    · exact h.locals.separate.symm.sub_right (Offset.sub_base _ (by decide))
    · exact outputs.privateWorkspace.symm
  have baseSep (r : Region) (hr : r ∈ keyScalarWrites p s) :
      (⟨State.addr s.sp, 4⟩ : Region).Disjoint r := by
    simp only [keyScalarWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (Offset.disjoint_base _ (by decide) (by decide)).symm
    · exact (Offset.disjoint_base _ (by decide) (by decide)).symm
    · exact (Offset.disjoint_base _ (by decide) (by decide)).symm
    · exact outputs.privateStack.sub_left (Region.sub_prefix (by decide))
  have readyT := ready.after_external frame workspaceSep baseSep rest context.ptr
  have fits : Proof.Rsa.Mont.arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
  have scalar : Octets p.base p.privateValue p.len ((layout p).encode rb) t := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [(layout p).encode_length size]; exact outputs.privateBuffer.fits
    · rw [(layout p).encode_length size, rest.rd, rest.wr]
      obtain ⟨r, hr, hc⟩ := outputs.privateBuffer.writable
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · rw [(layout p).encode_length size]; exact outputs.privateWorkspace
    · rw [(layout p).encode_length size]; exact bytes
  have significant := scalar.slice (d := (layout p).lead) (k := (layout p).width) (layout p).width_bounds.1
    (by rw [(layout p).encode_length size]; unfold ScalarLayout.width; have := (layout p).lead_lt; omega)
  rw [List.take_of_length_le (by rw [List.length_drop, (layout p).encode_length size]; rfl)] at significant
  exact ⟨context, readyT.1, (readyT.2.number fits (by decide : 0 < 8)).trans modulus,
    (readyT.2.number fits (by decide : 4 < 8)).trans r2, scalar, significant, frame, rest⟩

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SampleInstance.lean`, which only this module imported.
section

/-! A verified public width selection supplies the complete sampling law. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem sampleLaw (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p) (bound : Prog isa)
    (law : SampleBoundLaw env layout bound) : SampleLaw env layout (VG.Impl.Ffdh.Arm.SampleScalar.code bound) :=
  { correct := sampleSample_ok env layout bound law
    ct := by
      intro p slots rb1 rb2 stable special normalized odd _h0 h24 h28 h32 h40 h48 h60 size1 size2 separate
      exact sampleScalar_ct env bound layout law stable special normalized odd h24 h28 h32 h40 h48 h60 size1 size2 separate }

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedKeyGenerate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableConsts)

def sample : Prog isa := VG.Impl.Ffdh.Arm.SampleScalar.code VettedBound.code

def code (b : MontBackend) : Prog isa := b.caller.code (SampleKeyGenerate.code b sample)

theorem verified (b : MontBackend) : Verified target (code b)
    (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176) :=
  b.caller.verified (vettedKeyGenerate_verified (KeyGenerate.prepare b) sample (SampleKeyGenerate.tail b)
    VettedGroups.environment (normalizedPrepareLaw b)
    (sampleLaw _ _ _ VettedBound.law) (SampleKeyGenerate.tailLaw b)
    vettedKeyGenerate_environment (fun _ _ h => h))

theorem stack_ok (b : MontBackend) : FrameStack.armStack (code b) ≤ 176 :=
  Nat.le_trans (b.caller.stack_le _) (SampleKeyGenerate.stack_ok b sample (by rfl))

def backend (b : MontBackend) : KeyBackend .vetted where
  generateKey := code b
  generateKey_verified := verified b
  keyStack := stack_ok b
  suffix := b.suffix
  features := b.features

end VG.Proof.Ffdh.Arm.VettedKeyGenerate
