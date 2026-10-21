module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTShapeCopy
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTShapeMask
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTShapeEnds
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeCopy
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeMasks
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeTop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeOdd
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega

/-! Complete candidate shaping leaks only the public source, destination and bit width. -/

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
