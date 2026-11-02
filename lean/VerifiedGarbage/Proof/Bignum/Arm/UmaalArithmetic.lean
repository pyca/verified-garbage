module

public import VerifiedGarbage.Impl.Bignum.Arm.UmaalArithmetic
import VerifiedGarbage.Proof.Bignum.Arm.DownRowUmaal
public import VerifiedGarbage.Impl.Bignum.Arm.DownRowUmaal
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Framework.Subst
public import VerifiedGarbage.Impl.Bignum.Arm.DownRow

/-! Both row substitutions preserve the exact execution and require no stack. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem umaalArithmetic_sim (c : Prog isa) : Sim c (umaalArithmetic c) := by
  intro s tr t h
  exact Exec.subst DownRowUmaal.code_sim (Exec.subst row_sim h)

theorem umaalArithmetic_verified {c : Prog isa} {k : Contract isa} (h : Verified target c k) :
    Verified target (umaalArithmetic c) k := h.of_sim (umaalArithmetic_sim c)

theorem armStack_downRows (c : Prog isa) :
    FrameStack.armStack (Code.subst DownRow.code DownRow.codeU c) ≤ FrameStack.armStack c := by
  induction c with
  | block _ => simp only [Code.subst]; split <;> simp [DownRowUmaal.codeU_stack, FrameStack.armStack]
  | seq a b iha ihb =>
    simp only [Code.subst]; split
    · simp [DownRowUmaal.codeU_stack]
    · simp only [FrameStack.armStack]; omega
  | ite _ t e iht ihe =>
    simp only [Code.subst]; split
    · simp [DownRowUmaal.codeU_stack]
    · simp only [FrameStack.armStack]; omega
  | loop b _ ih =>
    simp only [Code.subst]; split
    · simp [DownRowUmaal.codeU_stack]
    · simpa only [FrameStack.armStack] using ih
  | call _ b ih =>
    simp only [Code.subst]; split
    · simp [DownRowUmaal.codeU_stack]
    · simpa only [FrameStack.armStack] using ih
  | icall =>
    simp only [Code.subst]; split
    · simp [DownRowUmaal.codeU_stack]
    · exact Nat.le_refl _
  | frame i b j ih =>
    simp only [Code.subst]; split
    · simp [DownRowUmaal.codeU_stack]
    · cases i <;> simp only [FrameStack.armStack] <;> omega

theorem armStack_umaalArithmetic (c : Prog isa) :
    FrameStack.armStack (umaalArithmetic c) ≤ FrameStack.armStack c :=
  Nat.le_trans (armStack_downRows _) (armStack_umaalRows _)

end VG.Proof.Bignum.Arm
