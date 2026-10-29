module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTShapeCopy

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeCopy
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeMasks
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeTop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeOdd
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPieces
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
/-! Complete candidate shaping leaks only the public source, destination and bit width. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTShapeMask.lean`, which only this module imported.
section

/-! Candidate mask construction uses the public bit count, including partial octets. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_taint)

private def MaskLoaded (p : ShapeData) (s : State) : Prop := s.gpr .r6 = BitVec.ofNat 32 p.bits
private def MaskCount (p : ShapeData) (s : State) : Prop := s.gpr .r6 = BitVec.ofNat 32 ((p.bits - 1) % 8 + 1)

private theorem maskHead_ct : RelCT isa (Two ShapeStart)
    (.block VG.Impl.Ffdh.Arm.ParameterCandidate.shapeMaskHead) (fun _ _ => True) := by
  have load : RelCT isa (Two ShapeStart) (.block [.ldrSp .r6 24]) (Two MaskLoaded) :=
    two_post ((loadStack_ct .r6 24).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h => by
      refine wp_loadStack (a := State.addr (s.sp + 24#32)) (by decide) rfl (h.frame.read (by decide)) fun t loaded => WP.block_nil ?_
      exact loaded.gpr.trans (h.frame.saved 24 (by decide)))
  obtain ⟨hint, checked⟩ := maskHeadTail_taint
  have tail : RelCT isa (Two MaskLoaded) (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.shapeMaskHead.drop 1))
      (fun _ _ => True) := by
    refine two_taint [.r6] ?_ checked
    intro p s t a b r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact a.trans b.symm
  exact RelCT.block_append (load.seq tail)

theorem shapeMasks_ct : RelCT isa (Two ShapeStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.shapeMasks (fun _ _ => True) := by
  have head : RelCT isa (Two ShapeStart) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.shapeMaskHead) (Two MaskCount) :=
    two_post maskHead_ct (fun p s h => WP.mono (shapeMaskHead_ok s
      (by have := h.minBits; omega) (by have := h.maxBits; omega)
      (h.frame.read (by decide)) (h.frame.saved 24 (by decide))) (fun _ ⟨⟨count, _, _⟩, _⟩ => count))
  obtain ⟨hint, checked⟩ := maskLoop_taint
  have body : RelCT isa (Two MaskCount) (.loop (.block VG.Impl.Ffdh.Arm.ParameterCandidate.maskStep) .ne)
      (fun _ _ => True) := by
    refine two_taint [.r6] ?_ checked
    intro p s t a b r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact a.trans b.symm
  exact head.seq body

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTShapeEnds.lean`, which only this module imported.
section

/-! The first/last-octet stores have public addresses, independent of their byte values. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_taint)

private def FirstPointer (p : ShapeData) (s : State) : Prop := s.gpr .r4 = p.dst

def ShapeDest (p : ShapeData) (s : State) : Prop := ShapeStart p s ∧ s.gpr .r4 = p.dst

private def LastPointers (p : ShapeData) (s : State) : Prop :=
  s.gpr .r4 = p.dst ∧ s.gpr .r5 = BitVec.ofNat 32 p.bytes.length

theorem shapeFirst_ct : RelCT isa (Two ShapeStart)
    (.block VG.Impl.Ffdh.Arm.ParameterCandidate.shapeFirst) (fun _ _ => True) := by
  have load : RelCT isa (Two ShapeStart) (.block [.ldrSp .r4 4]) (Two FirstPointer) :=
    two_post ((loadStack_ct .r4 4).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h => by
      refine wp_loadStack (a := State.addr (s.sp + 4#32)) (by decide) rfl (h.frame.read (by decide)) fun t loaded => WP.block_nil ?_
      exact loaded.gpr.trans (h.frame.saved 4 (by decide)))
  obtain ⟨hint, checked⟩ := shapeFirstTail_taint
  have tail : RelCT isa (Two FirstPointer) (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.shapeFirst.drop 1))
      (fun _ _ => True) := by
    refine two_taint [.r4] ?_ checked
    intro p s t a b r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact a.trans b.symm
  exact RelCT.block_append (load.seq tail)

theorem shapeLast_ct : RelCT isa (Two ShapeDest)
    (.block VG.Impl.Ffdh.Arm.ParameterCandidate.shapeLast) (fun _ _ => True) := by
  have load : RelCT isa (Two ShapeDest) (.block [.ldrSp .r5 12]) (Two LastPointers) :=
    two_post ((loadStack_ct .r5 12).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h => by
      refine wp_loadStack (a := State.addr (s.sp + 12#32)) (by decide) rfl (h.1.frame.read (by decide)) fun t loaded => WP.block_nil ?_
      exact ⟨(loaded.other .r4 (by decide)).trans h.2, loaded.gpr.trans (h.1.frame.saved 12 (by decide))⟩)
  obtain ⟨hint, checked⟩ := shapeLastTail_taint
  have tail : RelCT isa (Two LastPointers) (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.shapeLast.drop 1))
      (fun _ _ => True) := by
    refine two_taint [.r4, .r5] ?_ checked
    intro p s t a b r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact a.1.trans b.1.symm
    · exact a.2.trans b.2.symm
  exact RelCT.block_append (load.seq tail)

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_mono)

private def ShapeCopied (p : ShapeData) (s : State) : Prop := ShapeStart p s ∧
  ∀ i < p.bytes.length, s.mem (State.addr (p.dst + BitVec.ofNat 32 i)) = p.bytes[i]?.getD 0

private def ShapeMasked (p : ShapeData) (s : State) : Prop := ShapeCopied p s ∧
  s.gpr .r7 = BitVec.ofNat 32 (2 ^ ((p.bits - 1) % 8 + 1) - 1)

private def ShapeTopped (p : ShapeData) (s : State) : Prop := ShapeDest p s ∧
  ∀ i < p.bytes.length, s.mem (State.addr (p.dst + BitVec.ofNat 32 i)) =
    (VG.Proof.Ffdh.ParameterCandidate.topCut p.bytes ((p.bits - 1) % 8)).getD i 0

theorem shapeP_ct : RelCT isa (Two ShapeStart) VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP (fun _ _ => True) := by
  have copy : RelCT isa (Two ShapeStart) VG.Impl.Ffdh.Arm.ParameterCandidate.shapeCopy (Two ShapeCopied) :=
    two_post shapeCopy_ct (fun _ s h => WP.mono (shapeCopy_ok s h)
      (fun _ ⟨context, bytes, _, _⟩ => ⟨context, bytes⟩))
  have mask : RelCT isa (Two ShapeCopied) VG.Impl.Ffdh.Arm.ParameterCandidate.shapeMasks (Two ShapeMasked) :=
    two_post (shapeMasks_ct.mono (fun _ _ h => two_mono (fun _ _ h => h.1) h) (fun _ _ h => h)) (fun p s h => by
      refine WP.mono (shapeMasks_ok s (by have := h.1.minBits; omega) (by have := h.1.maxBits; omega)
        (h.1.frame.read (by decide)) (h.1.frame.saved 24 (by decide))) ?_
      rintro t ⟨mask, memory, rest⟩
      exact ⟨⟨h.1.after_memory memory rest, by rw [memory]; exact h.2⟩, mask⟩)
  have top : RelCT isa (Two ShapeMasked) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.shapeFirst) (Two ShapeTopped) :=
    two_post (shapeFirst_ct.mono (fun _ _ h => two_mono (fun _ _ h => h.1.1) h) (fun _ _ h => h)) (fun p s h => by
      refine WP.mono (shapeTop_ok s h.1.1 (Nat.mod_lt _ (by decide : 0 < 8)) h.1.2 h.2) ?_
      rintro t ⟨context, ptr, bytes, _, _⟩
      exact ⟨⟨context, ptr⟩, bytes⟩)
  have last : RelCT isa (Two ShapeTopped) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.shapeLast) (fun _ _ => True) :=
    shapeLast_ct.mono (fun _ _ h => two_mono (fun _ _ h => h.1) h) (fun _ _ h => h)
  exact copy.seq (mask.seq (top.seq (last.seq (RelCT.block_nil (fun _ _ h => h)))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
