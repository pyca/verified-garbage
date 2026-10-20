module

public import VerifiedGarbage.Impl.Ffdh.Arm.SampleScalar
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleBoundLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleCutCT
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalarCT
import VerifiedGarbage.Proof.Ffdh.Arm.SampleScalarArgs
import VerifiedGarbage.Proof.Ffdh.Arm.KeyArgsCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.Offset

/-! Public scalar layouts determine sampling addresses and loop counts. -/

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
