module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTShapeCopy
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPieces
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! The first/last-octet stores have public addresses, independent of their byte values. -/

@[expose] public section
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
