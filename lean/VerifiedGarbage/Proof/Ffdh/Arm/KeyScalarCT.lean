module

public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyOutputs
public import VerifiedGarbage.Proof.Ffdh.Arm.Context

import VerifiedGarbage.Proof.Ffdh.Arm.KeyBoundCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyArgsCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalarArgs
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyBound
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeometry
import VerifiedGarbage.Proof.Ffdh.Arm.KeyCut
import VerifiedGarbage.Proof.Ffdh.Arm.KeyByteCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyFirstRetained
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrefix
/-! The complete scalar sampler leaks only the public domain bound and buffer layout. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/KeyCutCT.lean`, which only this module imported.
section

/-! Entropy cutting uses the same public prefix and suffix lengths for different
secret tapes; no secret byte determines an address or loop count. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

structure KeyCutMemory (p : Inputs) (slots : List Nat) (rb : List Byte) (s : State) : Prop where
  context : ArgumentMemory p slots s
  entropy : Octets p.base p.entropy p.len rb s
  outputs : KeyOutputs p s

structure KeyCutStart (p : Inputs) (slots : List Nat) (rb : List Byte) (s : State) : Prop extends KeyCutMemory p slots rb s where
  dest : s.gpr .r0 = p.privateValue
  source : s.gpr .r1 = p.entropy
  count : s.gpr .lr = BitVec.ofNat 32 p.scalarLead
  zero : s.gpr .r2 = 0

structure KeyFirstStart (p : Inputs) (slots : List Nat) (rb : List Byte) (s : State) : Prop extends KeyCutMemory p slots rb s where
  dest : s.gpr .r0 = p.scalarStart
  source : s.gpr .r1 = p.entropy + BitVec.ofNat 32 p.scalarLead

structure KeyCopyStart (p : Inputs) (slots : List Nat) (rb : List Byte) (s : State) : Prop extends KeyCutMemory p slots rb s where
  dest : s.gpr .r0 = p.privateValue + BitVec.ofNat 32 (p.scalarLead + 1)
  source : s.gpr .r1 = p.entropy + BitVec.ofNat 32 (p.scalarLead + 1)
  count : s.gpr .lr = BitVec.ofNat 32 (p.scalarWidth - 1)

theorem keyPrefix_next (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (saved : ∀ d ∈ slots, d + 4 ≤ 72) (size : rb.length = p.k)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (h : KeyCutStart p slots rb s) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.GenerateKey.unlessZero .lr
      (.loop (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.prefixStep) .ne)) s (KeyFirstStart p slots rb) := by
  refine WP.mono (keyPrefix_ok s h.context saved h.outputs.privateBuffer h.outputs.privateDomain h.outputs.privateStack
    h.source h.dest h.count h.zero) ?_
  rintro t ⟨context, _, dest, source, frame, rest⟩
  have entropy := h.entropy.after_frame frame rest (by
    simpa [size] using entropySep.sub_right (Region.sub_prefix (by have := p.scalarLeadBound; omega)))
  exact ⟨⟨context, entropy, h.outputs.after rest⟩, dest, source⟩

theorem keyFirst_next (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (saved : ∀ d ∈ slots, d + 4 ≤ 72) (h20 : 20 ∈ slots) (h68 : 68 ∈ slots) (size : rb.length = p.k)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (h : KeyFirstStart p slots rb s) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.first) s (KeyCopyStart p slots rb) := by
  refine WP.mono (keyFirst_retained s h.context saved h20 h68 h.entropy size h.outputs.privateBuffer
    h.outputs.privateDomain h.outputs.privateStack entropySep h.source h.dest) ?_
  rintro t ⟨context, entropy, _, dest, source, count, _, rest⟩
  exact ⟨⟨context, entropy, h.outputs.after rest⟩, dest, source, count⟩

theorem keyCut_ct {p : Inputs} {slots : List Nat} {rb1 rb2 : List Byte}
    (saved : ∀ d ∈ slots, d + 4 ≤ 72) (h20 : 20 ∈ slots) (h68 : 68 ∈ slots)
    (size1 : rb1.length = p.k) (size2 : rb2.length = p.k)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩) :
    RelCT isa (fun s t => KeyCutStart p slots rb1 s ∧ KeyCutStart p slots rb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.GenerateKey.cutEntropy (fun _ _ => True) := by
  have leading := keyPrefix_ct.mono
    (P' := fun (s t : State) => KeyCutStart p slots rb1 s ∧ KeyCutStart p slots rb2 t ∧ s.sp = t.sp)
    (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1.dest.trans h.2.1.dest.symm
      · exact h.1.count.trans h.2.1.count.symm) (fun _ _ h => h)
  have first := keyFirst_ct.mono
    (P' := fun (s t : State) => KeyFirstStart p slots rb1 s ∧ KeyFirstStart p slots rb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1.dest.trans h.2.1.dest.symm
      · exact h.1.source.trans h.2.1.source.symm, h.2.2⟩) (fun _ _ h => h)
  have copy := keyCopy_ct.mono
    (P' := fun (s t : State) => KeyCopyStart p slots rb1 s ∧ KeyCopyStart p slots rb2 t ∧ s.sp = t.sp)
    (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.1.dest.trans h.2.1.dest.symm
      · exact h.1.source.trans h.2.1.source.symm
      · exact h.1.count.trans h.2.1.count.symm) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.cutEntropy
  exact relCT_chain leading (keyPrefix_next · saved size1 entropySep) (keyPrefix_next · saved size2 entropySep)
    (relCT_chain first (keyFirst_next · saved h20 h68 size1 entropySep) (keyFirst_next · saved h20 h68 size2 entropySep) copy)

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

structure KeyScalarInput (p : Inputs) (slots : List Nat) (rb : List Byte) (s : State) : Prop where
  context : Context p slots s
  entropy : Octets p.base p.entropy p.len rb s
  outputs : KeyOutputs p s
  entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr s.sp, 72⟩

theorem keyBound_next (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (stable : stableSlots slots = true) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots)
    (size : rb.length = p.k) (h : KeyScalarInput p slots rb s) :
    WP isa VG.Impl.Ffdh.Arm.Domain.GenerateKey.bound s (KeyScalarInput p (68 :: 20 :: slots) rb) := by
  refine WP.mono (keyBound_ok s h.context stable h24 h28 h32 h60) ?_
  rintro t ⟨⟨context, frame⟩, rest⟩
  have entropy := h.entropy.after_frame frame rest (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [size]
    rcases hr with rfl | rfl <;> exact h.entropyStack.sub_right (Offset.sub_base _ (by decide)))
  exact ⟨context, entropy, h.outputs.after rest, by rw [rest.sp]; exact h.entropyStack⟩

theorem keyScalarArgs_next (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (stable : stableSlots slots = true) (h20 : 20 ∈ slots) (h32 : 32 ∈ slots) (h40 : 40 ∈ slots) (h48 : 48 ∈ slots)
    (size : rb.length = p.k) (h : KeyScalarInput p slots rb s) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.scalarArgs) s (KeyCutStart p (16 :: slots) rb) := by
  refine WP.mono (keyScalarArgs_retained s h.context stable h20 h32 h40 h48) ?_
  rintro t ⟨context, dest, source, count, zero, frame, rest⟩
  have entropy := h.entropy.after_frame frame rest (by
    intro r hr
    rw [List.mem_singleton] at hr; subst r
    rw [size]
    exact h.entropyStack.sub_right (Offset.sub_base _ (by decide)))
  exact ⟨⟨context, entropy, h.outputs.after rest⟩, dest, source, count, zero⟩

theorem keyScalar_ct {p : Inputs} {slots : List Nat} {rb1 rb2 : List Byte}
    (stable : stableSlots slots = true) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h40 : 40 ∈ slots) (h48 : 48 ∈ slots) (h60 : 60 ∈ slots)
    (size1 : rb1.length = p.k) (size2 : rb2.length = p.k)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩) :
    RelCT isa (fun s t => KeyScalarInput p slots rb1 s ∧ KeyScalarInput p slots rb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.GenerateKey.scalar (fun _ _ => True) := by
  have stableB : stableSlots (68 :: 20 :: slots) = true := by
    change (true && (true && stableSlots slots)) = true
    rw [Bool.true_and, Bool.true_and, stable]
  have stableA : stableSlots (16 :: 68 :: 20 :: slots) = true := by
    change (true && stableSlots (68 :: 20 :: slots)) = true
    rw [Bool.true_and, stableB]
  have bound := (keyBound_ct h24 h28 h32 h60).mono
    (P' := fun (s t : State) => KeyScalarInput p slots rb1 s ∧ KeyScalarInput p slots rb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.context, h.2.1.context, h.2.2⟩) (fun _ _ h => h)
  have args := keyScalarArgs_ct.mono
    (P' := fun (s t : State) => KeyScalarInput p (68 :: 20 :: slots) rb1 s ∧ KeyScalarInput p (68 :: 20 :: slots) rb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  have cut := keyCut_ct (fun d hd => (stableSlots_at stableA hd).1) (by simp) (by simp) size1 size2 entropySep
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.scalar
  exact relCT_chain bound (keyBound_next · stable h24 h28 h32 h60 size1) (keyBound_next · stable h24 h28 h32 h60 size2)
    (relCT_chain args (keyScalarArgs_next · stableB (by simp) (by simp [h32]) (by simp [h40]) (by simp [h48]) size1)
      (keyScalarArgs_next · stableB (by simp) (by simp [h32]) (by simp [h40]) (by simp [h48]) size2)
      (((relCT_keep_sp cut (fun _ _ h => h.2.2)).seq (loadStack_ct .r0 0)).mono (fun _ _ h => h) (fun _ _ _ => trivial)))

end VG.Proof.Ffdh.Arm
