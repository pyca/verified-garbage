module

public import VerifiedGarbage.Impl.Ffdh.Arm.SampleScalar
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleBoundLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalarCT
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleMemory
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyOutputs
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.TCB.Arm.Isa

import VerifiedGarbage.Proof.Ffdh.Arm.SampleScalarArgs
import VerifiedGarbage.Proof.Ffdh.Arm.KeyArgsCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.KeyByteCT
import VerifiedGarbage.Proof.Ffdh.Arm.SampleFirstRetained
import VerifiedGarbage.Proof.Ffdh.Arm.SamplePrefix
/-! Public scalar layouts determine sampling addresses and loop counts. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SampleCutCT.lean`, which only this module imported.
section

/-! Entropy cutting uses the same public prefix and suffix lengths for different
secret tapes; no secret byte determines an address or loop count. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

structure SampleCutMemory (p : Inputs) (l : ScalarLayout p) (slots : List Nat) (rb : List Byte) (s : State) : Prop where
  context : SampleMemory p l slots s
  entropy : Octets p.base p.entropy p.len rb s
  outputs : KeyOutputs p s

structure SampleCutStart (p : Inputs) (l : ScalarLayout p) (slots : List Nat) (rb : List Byte) (s : State) : Prop extends SampleCutMemory p l slots rb s where
  dest : s.gpr .r0 = p.privateValue
  source : s.gpr .r1 = p.entropy
  count : s.gpr .lr = BitVec.ofNat 32 l.lead
  zero : s.gpr .r2 = 0

structure SampleFirstStart (p : Inputs) (l : ScalarLayout p) (slots : List Nat) (rb : List Byte) (s : State) : Prop extends SampleCutMemory p l slots rb s where
  dest : s.gpr .r0 = l.start
  source : s.gpr .r1 = p.entropy + BitVec.ofNat 32 l.lead

structure SampleCopyStart (p : Inputs) (l : ScalarLayout p) (slots : List Nat) (rb : List Byte) (s : State) : Prop extends SampleCutMemory p l slots rb s where
  dest : s.gpr .r0 = p.privateValue + BitVec.ofNat 32 (l.lead + 1)
  source : s.gpr .r1 = p.entropy + BitVec.ofNat 32 (l.lead + 1)
  count : s.gpr .lr = BitVec.ofNat 32 (l.width - 1)

theorem samplePrefix_next (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {rb : List Byte}
    (saved : ∀ d ∈ slots, d + 4 ≤ 72) (size : rb.length = p.k)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (h : SampleCutStart p l slots rb s) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.GenerateKey.unlessZero .lr
      (.loop (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.prefixStep) .ne)) s (SampleFirstStart p l slots rb) := by
  refine WP.mono (samplePrefix_ok s h.context saved h.outputs.privateBuffer h.outputs.privateDomain h.outputs.privateStack
    h.source h.dest h.count h.zero) ?_
  rintro t ⟨context, _, dest, source, frame, rest⟩
  have entropy := h.entropy.after_frame frame rest (by
    simpa [size] using entropySep.sub_right (Region.sub_prefix (by have := l.lead_lt; omega)))
  exact ⟨⟨context, entropy, h.outputs.after rest⟩, dest, source⟩

theorem sampleFirst_next (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {rb : List Byte}
    (saved : ∀ d ∈ slots, d + 4 ≤ 72) (size : rb.length = p.k)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (h : SampleFirstStart p l slots rb s) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.first) s (SampleCopyStart p l slots rb) := by
  refine WP.mono (sampleFirst_retained s h.context saved h.entropy size h.outputs.privateBuffer
    h.outputs.privateDomain h.outputs.privateStack entropySep h.source h.dest) ?_
  rintro t ⟨context, entropy, _, dest, source, count, _, rest⟩
  exact ⟨⟨context, entropy, h.outputs.after rest⟩, dest, source, count⟩

theorem sampleCut_ct {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {rb1 rb2 : List Byte}
    (saved : ∀ d ∈ slots, d + 4 ≤ 72)
    (size1 : rb1.length = p.k) (size2 : rb2.length = p.k)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩) :
    RelCT isa (fun s t => SampleCutStart p l slots rb1 s ∧ SampleCutStart p l slots rb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.GenerateKey.cutEntropy (fun _ _ => True) := by
  have leading := keyPrefix_ct.mono
    (P' := fun (s t : State) => SampleCutStart p l slots rb1 s ∧ SampleCutStart p l slots rb2 t ∧ s.sp = t.sp)
    (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1.dest.trans h.2.1.dest.symm
      · exact h.1.count.trans h.2.1.count.symm) (fun _ _ h => h)
  have first := keyFirst_ct.mono
    (P' := fun (s t : State) => SampleFirstStart p l slots rb1 s ∧ SampleFirstStart p l slots rb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1.dest.trans h.2.1.dest.symm
      · exact h.1.source.trans h.2.1.source.symm, h.2.2⟩) (fun _ _ h => h)
  have copy := keyCopy_ct.mono
    (P' := fun (s t : State) => SampleCopyStart p l slots rb1 s ∧ SampleCopyStart p l slots rb2 t ∧ s.sp = t.sp)
    (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.1.dest.trans h.2.1.dest.symm
      · exact h.1.source.trans h.2.1.source.symm
      · exact h.1.count.trans h.2.1.count.symm) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.cutEntropy
  exact relCT_chain leading (samplePrefix_next · saved size1 entropySep) (samplePrefix_next · saved size2 entropySep)
    (relCT_chain first (sampleFirst_next · saved size1 entropySep) (sampleFirst_next · saved size2 entropySep) copy)

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

structure SampleBoundReady (p : Inputs) (l : ScalarLayout p) (slots : List Nat)
    (rb : List Byte) (s : State) : Prop extends KeyScalarInput p slots rb s where
  width : s.mem.readW (off (State.addr s.sp) 20) 32 = BitVec.ofNat 32 l.width
  mask : s.mem.readW (off (State.addr s.sp) 68) 32 = l.mask

theorem sampleBound_next (env : SampleEnvironment) (bound : Prog isa) (layout : (p : Inputs) → ScalarLayout p)
    (law : SampleBoundLaw env layout bound) (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (stable : stableSlots slots = true) (special : sampleSlots slots)
    (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) (odd : p.P % 2 = 1)
    (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots)
    (size : rb.length = p.k) (h : KeyScalarInput p slots rb s) (environment : env.holds p s) :
    WP isa bound s (SampleBoundReady p (layout p) slots rb) := by
  refine WP.mono (law.correct s h.context environment normalized odd stable special h24 h28 h32 h60) ?_
  rintro t ⟨context, width, mask, frame, rest⟩
  have entropy := h.entropy.after_frame frame rest (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [size]
    rcases hr with rfl | rfl <;> exact h.entropyStack.sub_right (Offset.sub_base _ (by decide)))
  exact ⟨⟨context, entropy, h.outputs.after rest, by rw [rest.sp]; exact h.entropyStack⟩, width, mask⟩

theorem sampleScalarArgs_next (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {rb : List Byte}
    (stable : stableSlots slots = true) (special : sampleSlots slots)
    (h32 : 32 ∈ slots) (h40 : 40 ∈ slots) (h48 : 48 ∈ slots)
    (size : rb.length = p.k) (h : SampleBoundReady p l slots rb s) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.scalarArgs) s (SampleCutStart p l slots rb) := by
  refine WP.mono (sampleScalarArgs_retained s h.context stable special h.width h.mask h32 h40 h48) ?_
  rintro t ⟨context, dest, source, count, zero, frame, rest⟩
  have entropy := h.entropy.after_frame frame rest (by
    intro r hr
    rw [List.mem_singleton] at hr; subst r
    rw [size]
    exact h.entropyStack.sub_right (Offset.sub_base _ (by decide)))
  exact ⟨⟨context, entropy, h.outputs.after rest⟩, dest, source, count, zero⟩

theorem sampleScalar_ct (env : SampleEnvironment) (bound : Prog isa) (layout : (p : Inputs) → ScalarLayout p)
    (law : SampleBoundLaw env layout bound) {p : Inputs} {slots : List Nat} {rb1 rb2 : List Byte}
    (stable : stableSlots slots = true) (special : sampleSlots slots)
    (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) (odd : p.P % 2 = 1)
    (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h40 : 40 ∈ slots) (h48 : 48 ∈ slots) (h60 : 60 ∈ slots)
    (size1 : rb1.length = p.k) (size2 : rb2.length = p.k)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩) :
    RelCT isa (fun s t => (KeyScalarInput p slots rb1 s ∧ env.holds p s) ∧ (KeyScalarInput p slots rb2 t ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SampleScalar.code bound) (fun _ _ => True) := by
  have boundCT := (law.ct stable special normalized odd h24 h28 h32 h60).mono
    (P' := fun (s t : State) => (KeyScalarInput p slots rb1 s ∧ env.holds p s) ∧ (KeyScalarInput p slots rb2 t ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.1.context, h.1.2⟩, ⟨h.2.1.1.context, h.2.1.2⟩, h.2.2⟩) (fun _ _ h => h)
  have args := keyScalarArgs_ct.mono
    (P' := fun (s t : State) => SampleBoundReady p (layout p) slots rb1 s ∧ SampleBoundReady p (layout p) slots rb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  have cut := sampleCut_ct (l := layout p) (fun d hd => (stableSlots_at stable hd).1) size1 size2 entropySep
  unfold VG.Impl.Ffdh.Arm.SampleScalar.code
  have bounded := (relCT_keep_sp boundCT (fun _ _ h => h.2.2.2)).wp
    (fun s t h => ⟨sampleBound_next env bound layout law s stable special normalized odd h24 h28 h32 h60 size1 h.1.1 h.1.2,
      sampleBound_next env bound layout law t stable special normalized odd h24 h28 h32 h60 size2 h.2.1.1 h.2.1.2⟩)
  exact bounded.seq ((relCT_chain args
      (sampleScalarArgs_next · stable special h32 h40 h48 size1)
      (sampleScalarArgs_next · stable special h32 h40 h48 size2)
      (((relCT_keep_sp cut (fun _ _ h => h.2.2)).seq (loadStack_ct .r0 0)).mono
        (fun _ _ h => h) (fun _ _ _ => trivial))).mono
      (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h))

end VG.Proof.Ffdh.Arm
