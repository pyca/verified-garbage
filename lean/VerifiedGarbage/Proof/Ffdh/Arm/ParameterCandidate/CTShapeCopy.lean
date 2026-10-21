module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeContext
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPieces
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeCopyHead
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! The initial candidate copy uses only public buffer pointers and byte count. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_taint)

structure ShapeData where
  dst : BitVec 32
  src : BitVec 32
  bytes : List Byte
  bits : Nat

def ShapeStart (p : ShapeData) (s : State) : Prop := ShapeContext p.dst p.src p.bytes p.bits s

def CopyPointers (p : ShapeData) (s : State) : Prop :=
  s.gpr .r0 = p.dst ∧ s.gpr .r1 = p.src ∧ s.gpr .lr = BitVec.ofNat 32 p.bytes.length

theorem shapeCopy_ct : RelCT isa (Two ShapeStart) VG.Impl.Ffdh.Arm.ParameterCandidate.shapeCopy (fun _ _ => True) := by
  have headTrace : RelCT isa (Two ShapeStart) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.shapeCopyHead)
      (fun _ _ => True) :=
    (stackLoads_ct [(.r0, 4), (.r1, 16), (.lr, 12)]).mono
      (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)
  have head := two_post headTrace (Ψ := CopyPointers) (fun p s h =>
    WP.mono (shapeCopyHead_ok s h) (fun _ ⟨⟨dst, src, count, _⟩, _⟩ => ⟨dst, src, count⟩))
  obtain ⟨hint, checked⟩ := copyLoop_taint
  have body : RelCT isa (Two CopyPointers) VG.Impl.Bignum.Arm.copyBytes (fun _ _ => True) := by
    refine two_taint [.r0, .r1, .lr] ?_ checked
    intro p s t a b r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact a.1.trans b.1.symm
    · exact a.2.1.trans b.2.1.symm
    · exact a.2.2.trans b.2.2.symm
  exact head.seq body

end VG.Proof.Ffdh.Arm.ParameterCandidate
