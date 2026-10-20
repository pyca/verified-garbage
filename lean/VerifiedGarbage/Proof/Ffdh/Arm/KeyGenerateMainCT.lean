module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrepareLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyMain
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateMain
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateState
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

public import VerifiedGarbage.Impl.Ffdh.Arm.KeyGenerate

/-! The only secret-dependent key-generation branch is scalar acceptance,
whose classification is disclosed by the attempt's returned status. -/

@[expose] public section
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
    (large : 1 < p.P) (odd : p.P % 2 = 1) :
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
  have prepareCT := (prep.ct (p := p) stable h0 h24 h32 large odd).mono
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
    (fun s h => keyGeneratePrepare_next prepare prep s stable h0 h24 h32 large odd size1 h.1 h.2)
    (fun s h => keyGeneratePrepare_next prepare prep s stable h0 h24 h32 large odd size2 h.1 h.2)
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
