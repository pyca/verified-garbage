module

public import VerifiedGarbage.Impl.Bignum.X86.ModulusCheck
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Combining modulus-rejection bits on i686 -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86

theorem modulusFinish_ok (s : State) :
    WP isa (.block modulusFinish) s fun t =>
      t.zf = some ((s.gpr .ebx ||| ((s.gpr .edx &&& 1) ^^^ 1) ||| s.gpr .ebp) == 0) ∧
      t.mem = s.mem ∧ Keeps [.edx, .ebx] s t := by
  unfold modulusFinish
  refine wp_logicS (.inl rfl) rfl fun s₁ u₁ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₂ u₂ => ?_
  refine wp_orS rfl fun s₃ u₃ => ?_
  refine wp_orS rfl fun s₄ u₄ => ?_
  refine wp_cmpS rfl fun t ft zt => WP.block_nil ?_
  refine ⟨?_, ?_, ?_⟩
  · have subzero : s₄.gpr .ebx - (0 : BitVec 32) = s₄.gpr .ebx := BitVec.sub_zero _
    rw [zt, subzero, u₄.gpr, u₃.gpr, u₂.other .ebx (by decide), u₁.other .ebx (by decide),
      u₂.gpr, u₁.gpr, u₃.other .ebp (by decide), u₂.other .ebp (by decide), u₁.other .ebp (by decide)]
    rfl
  · rw [ft.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · exact ((((u₁.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps).widen u₄.keeps).trans (ft.keeps _)

end VG.Proof.Bignum.X86
