module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTShapeCopy
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPieces
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeMasks
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega

/-! Candidate mask construction uses the public bit count, including partial octets. -/

@[expose] public section
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
