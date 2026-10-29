module

public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Impl.Ffdh.Arm.KeyGenerate
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrepareLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailLaw
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Arm.Isa

import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateCorrect
import VerifiedGarbage.Proof.Ffdh.Arm.KeyClassification
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeneratePre
import VerifiedGarbage.Proof.Ffdh.Arm.KeyMain
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateState
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateCalls
import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.FlagCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalarCT
import VerifiedGarbage.TCB.Code
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.Head
import VerifiedGarbage.Proof.Ffdh.Arm.HeadCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateFn
import VerifiedGarbage.Proof.Ffdh.Arm.KeyEntryCT
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Ffdh.Arm.Block
/-! Native key generation satisfies the shared timing policy for arbitrary
secret entropy tapes with the same public domain and disclosed attempt status. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/KeyGenerateMainCT.lean`, which only this module imported.
section

/-! The only secret-dependent key-generation branch is scalar acceptance,
whose classification is disclosed by the attempt's returned status. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem keyGenerateMain_ct (prepare tail : Prog isa) (prep : KeyPrepareLaw prepare) (law : KeyTailLaw tail) {p : Inputs} {slots : List Nat} {rb1 rb2 : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h48 : 48 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (size1 : rb1.length = p.k) (size2 : rb2.length = p.k)
    (classification : keyScalarValid p rb1 ↔ keyScalarValid p rb2)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (privateLength : p.privateLength = p.k) (outputY : p.output = p.publicValue)
    (large : 1 < p.P) (odd : p.P % 2 = 1) (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) :
    RelCT isa (fun s t => (KeyScalarInput p slots rb1 s ∧ KeyCallMemory p s) ∧ (KeyScalarInput p slots rb2 t ∧ KeyCallMemory p t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.KeyGenerate.main prepare tail) (fun _ _ => True) := by
  have stable' : stableSlots (16 :: 68 :: 20 :: slots) = true := by
    change (true && (true && (true && stableSlots slots))) = true
    rw [Bool.true_and, Bool.true_and, Bool.true_and, stable]
  have saved' : ∀ d ∈ 16 :: 68 :: 20 :: slots, d + 4 ≤ 64 ∨ 68 ≤ d := by
    intro d hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | rfl | rfl | hd
    · left; decide
    · right; decide
    · left; decide
    · exact saved d hd
  have prepareCT := (prep.ct (p := p) stable h0 h24 h32 large odd normalized).mono
    (P' := fun (s t : State) => (KeyScalarInput p slots rb1 s ∧ KeyCallMemory p s) ∧
      (KeyScalarInput p slots rb2 t ∧ KeyCallMemory p t) ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.1.context, h.1.2⟩, ⟨h.2.1.1.context, h.2.1.2⟩, h.2.2⟩) (fun _ _ h => h)
  have sample := (keyScalar_ct stable h24 h28 h32 h40 h48 h60 size1 size2 entropySep).mono
    (P' := fun (s t : State) => KeyPrepared p slots rb1 s ∧ KeyPrepared p slots rb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.toKeyScalarInput, h.2.1.toKeyScalarInput, h.2.2⟩) (fun _ _ h => h)
  have imports := (importAt_ct (p := p) (a := 1) (slot := 40) (countSlot := 44) (k := p.k) stable' (by simp [h40]) (by simp [h44])
    (by change BitVec.ofNat 32 p.privateLength = _; rw [privateLength]) (by decide)).mono
    (P' := fun (s t : State) => KeyReady p (16 :: 68 :: 20 :: slots) rb1 s ∧ KeyReady p (16 :: 68 :: 20 :: slots) rb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  have ranges := (scalarRange_ct stable' (by simp [h28]) (by simp [h32]) (by simp [h60]) odd).mono
    (P' := fun (s t : State) => KeyImported p (16 :: 68 :: 20 :: slots) rb1 s ∧ KeyImported p (16 :: 68 :: 20 :: slots) rb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready, h.1.modulus⟩, ⟨h.2.1.context, h.2.1.ready, h.2.1.modulus⟩, h.2.2⟩) (fun _ _ h => h)
  have sigSize {rb : List Byte} (size : rb.length = p.k) : ((scalarOctets p rb).drop p.scalarLead).length = p.scalarWidth := by
    rw [List.length_drop, scalarOctets_length size]
    rfl
  have branches : RelCT isa (fun s t => (KeyRanged p (16 :: 68 :: 20 :: slots) rb1 s ∧ KeyCallMemory p s) ∧ (KeyRanged p (16 :: 68 :: 20 :: slots) rb2 t ∧ KeyCallMemory p t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.ifFlag tail VG.Impl.Ffdh.Arm.Domain.GenerateKey.failScalar)
      (fun _ _ => True) := by
    apply ifFlag_pair_ct (decide (keyScalarValid p rb1))
      (fun s h => by
        have f := h.1.flag
        change s.gpr .r11 = (if keyScalarValid p rb1 then 1 else 0) at f
        simpa only [decide_eq_true_eq] using f)
      (fun s h => by
        have f := h.1.flag
        change s.gpr .r11 = (if keyScalarValid p rb2 then 1 else 0) at f
        simp only [← classification] at f
        simpa only [decide_eq_true_eq] using f)
      (fun _ _ h mem rest => ⟨h.1.after_mem mem rest, h.2.after rest⟩) (fun _ _ h mem rest => ⟨h.1.after_mem mem rest, h.2.after rest⟩)
    · intro _
      exact (law.ct stable' (by simp [h4]) (by simp) (by simp) (by simp [h32]) (by simp [h36])
        (by simp [h40]) (by simp [h56]) saved' (sigSize size1) (sigSize size2) odd outputY).mono
        (fun _ _ h => ⟨⟨⟨⟨h.1.1.context, h.1.1.ready, h.1.1.modulus, h.1.1.r2, h.1.1.context.gBytes, h.1.1.significant⟩, h.1.1.outputs⟩, h.1.2⟩,
          ⟨⟨⟨h.2.1.1.context, h.2.1.1.ready, h.2.1.1.modulus, h.2.1.1.r2, h.2.1.1.context.gBytes, h.2.1.1.significant⟩, h.2.1.1.outputs⟩, h.2.1.2⟩, h.2.2⟩)
        (fun _ _ h => h)
    · intro _
      exact (keyFail_ct (fun d hd => (stableSlots_at stable' hd).1) (by simp [h32]) (by simp [h36]) (by simp [h40])).mono
        (fun _ _ h => ⟨⟨h.1.1.context.toArgumentMemory, h.1.1.outputs⟩, ⟨h.2.1.1.context.toArgumentMemory, h.2.1.1.outputs⟩, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.KeyGenerate.main
  exact relCT_chain prepareCT
    (fun s h => keyGeneratePrepare_next prepare prep s stable h0 h24 h32 large odd normalized size1 h.1 h.2)
    (fun s h => keyGeneratePrepare_next prepare prep s stable h0 h24 h32 large odd normalized size2 h.1 h.2)
    (relCT_chain (keyGenerateCT_calls sample)
      (fun s h => keyGenerateWP_calls (keySample_next s stable h0 h24 h28 h32 h40 h48 h60 size1 entropySep h.1) h.2)
      (fun s h => keyGenerateWP_calls (keySample_next s stable h0 h24 h28 h32 h40 h48 h60 size2 entropySep h.1) h.2)
      (relCT_chain (keyGenerateCT_calls imports)
        (fun s h => keyGenerateWP_calls (keyImport_next s stable' (by simp [h40]) (by simp [h44]) size1 privateLength h.1) h.2)
        (fun s h => keyGenerateWP_calls (keyImport_next s stable' (by simp [h40]) (by simp [h44]) size2 privateLength h.1) h.2)
        (relCT_chain (keyGenerateCT_calls ranges)
          (fun s h => keyGenerateWP_calls (keyRange_scalar_next s stable' (by simp [h28]) (by simp [h32]) (by simp [h60]) odd h.1) h.2)
          (fun s h => keyGenerateWP_calls (keyRange_scalar_next s stable' (by simp [h28]) (by simp [h32]) (by simp [h60]) odd h.1) h.2)
          branches)))

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/KeyGenerateBodyCT.lean`, which only this module imported.
section

/-! Key generation's public modulus gate and documented retry-status class
account for every branch before native exponentiation. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem keyGenerateBody_ct (prepare tail : Prog isa) (prep : KeyPrepareLaw prepare) (law : KeyTailLaw tail) {p : Inputs} {slots : List Nat} {rb1 rb2 : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h48 : 48 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (size1 : rb1.length = p.k) (size2 : rb2.length = p.k)
    (classification : Spec.Rsa.modulusValid p.P p.k = true → (keyScalarValid p rb1 ↔ keyScalarValid p rb2))
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (privateLength : p.privateLength = p.k) (outputY : p.output = p.publicValue) :
    RelCT isa (fun s t => (KeyScalarInput p slots rb1 s ∧ KeyCallMemory p s) ∧ (KeyScalarInput p slots rb2 t ∧ KeyCallMemory p t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.head (VG.Impl.Ffdh.Arm.KeyGenerate.main prepare tail)) (fun _ _ => True) := by
  let Q := fun (rb : List Byte) (s : State) => (KeyScalarInput p (60 :: 56 :: slots) rb s ∧ KeyCallMemory p s) ∧ s.z = Spec.Rsa.modulusValid p.P p.k
  have head := (head_ct stable h0 h24 h32).mono
    (P' := fun (s t : State) => (KeyScalarInput p slots rb1 s ∧ KeyCallMemory p s) ∧ (KeyScalarInput p slots rb2 t ∧ KeyCallMemory p t) ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.1.context, h.2.1.1.context, h.2.2⟩) (fun _ _ h => h)
  have wp (s : State) {rb : List Byte} (size : rb.length = p.k) (h : KeyScalarInput p slots rb s ∧ KeyCallMemory p s) :
      WP isa (.seq (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24 ++ VG.Impl.Ffdh.Arm.Domain.domainPointers))
        (.block VG.Impl.Bignum.Arm.modulusCheck)) s (Q rb) := by
    refine WP.mono (head_ok s h.1.context stable h0 h24 h32) ?_
    rintro t ⟨context, zero, frame, rest⟩
    exact ⟨⟨⟨context, h.1.entropy.after_frame frame rest (by simpa [size] using h.1.entropyStack),
      h.1.outputs.after rest, by rw [rest.sp]; exact h.1.entropyStack⟩, h.2.after rest⟩, zero⟩
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
  have branches : RelCT isa (fun s t => Q rb1 s ∧ Q rb2 t ∧ s.sp = t.sp)
      (.ite .eq (VG.Impl.Ffdh.Arm.KeyGenerate.main prepare tail) (VG.Impl.Ffdh.Arm.Domain.ret 0)) (fun _ _ => True) := by
    apply RelCT.ite (fun s t h => by change some s.z = some t.z; rw [h.1.2, h.2.1.2])
    · intro s t tr1 tr2 u v h e1 e2
      have valid : Spec.Rsa.modulusValid p.P p.k = true := by
        have selected := h.2
        change some s.z = some true at selected
        rw [h.1.1.2] at selected
        exact Option.some.inj selected
      have facts := VG.Proof.Bignum.valid_facts valid p.minLength
      exact keyGenerateMain_ct prepare tail prep law stable' (by simp [h0]) (by simp [h4]) (by simp [h24]) (by simp [h28])
        (by simp [h32]) (by simp [h36]) (by simp [h40]) (by simp [h44]) (by simp [h48]) (by simp) (by simp)
        saved' size1 size2 (classification valid) entropySep privateLength outputY facts.2.1 facts.1 facts.2.2
        s t tr1 tr2 u v ⟨h.1.1.1, h.1.2.1.1, h.1.2.2⟩ e1 e2
    · exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply RelCT.assoc
  exact relCT_chain head (wp · size1) (wp · size2) branches

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/KeyGenerateFnCT.lean`, which only this module imported.
section

/-! The callable key-generation attempt reveals only its public domain and
buffer layout and the scalar-acceptance class documented by its status. -/

section
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
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem keyGenerate_contract_ct (prepare tail : Prog isa) (prep : KeyPrepareLaw prepare) (law : KeyTailLaw tail) : ConstantTime isa (Spec.Ffdh.generateKeyContract abi 176).pre
    (Spec.Ffdh.generateKeyContract abi 176).pub (VG.Impl.Ffdh.Arm.KeyGenerate.code prepare tail) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, rb, base, privateValue, publicValue, domain, count, capacity, entropy, domainBytes, entropyBytes, inputS⟩ := keyGenerate_data s hs
  have randLength (a : State) (h : (Spec.Ffdh.generateKeyContract abi 176).pre a) :
      (stackArg a 4).toNat = (stackArg a 2).toNat := by
    sig_pre [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, length, _⟩ := h
    exact length
  sig_pub [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
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
  have inputT := keyGenerate_input t ht (p := p) (rb := rb2)
    (p9.symm.trans base) (p0.symm.trans privateValue) (p2.symm.trans publicValue) (p4.symm.trans domain)
    (by rw [← p6]; exact count) (by rw [← p10]; exact capacity) (p7.symm.trans entropy) inputS.outputY inputS.privateLength ?_ rfl
  · have status := (List.cons.inj statusEq).1
    rw [← domEq] at status
    simp only [State.addr] at domainBytes entropyBytes
    simp only [count, domain, entropy, domainBytes, entropyBytes] at status
    have classification := keyScalarClass_same p rb rb2 inputS.size inputT.size status
    exact (keyGenerateFn_ct prepare tail prep law classification s t tr1 tr2 u v ⟨inputS, inputT, sp⟩ e1 e2).1
  · rw [← p5, ← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (stackArg s 0)) (stackArg s 1).toNat = p.dom
    rw [← domEq, domain]
    exact domainBytes

end VG.Proof.Ffdh.Arm
