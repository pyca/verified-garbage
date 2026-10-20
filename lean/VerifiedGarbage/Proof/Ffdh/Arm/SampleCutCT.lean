module

public import VerifiedGarbage.Proof.Ffdh.Arm.SampleMemory
import VerifiedGarbage.Proof.Ffdh.Arm.SampleCut
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyOutputs
import VerifiedGarbage.Proof.Ffdh.Arm.KeyByteCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
import VerifiedGarbage.Proof.Ffdh.Arm.SampleFirstRetained
import VerifiedGarbage.Proof.Ffdh.Arm.SamplePrefix
public import VerifiedGarbage.TCB.Arm.Isa

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
