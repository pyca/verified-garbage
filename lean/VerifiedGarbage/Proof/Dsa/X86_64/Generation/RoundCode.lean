module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeDepth
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeSafety
import VerifiedGarbage.Proof.Framework.Omega

/-! # Instruction safety and stack use of the shared Miller–Rabin backend -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

theorem roundCode_safe (v : RoundImpl) : generationSafe (Kernel.called v).run := by
  have h : generationSafe v.code := by
    rw [generationSafe, Code.allInstrs_eq]
    apply List.all_eq_true.mpr
    intro i hi
    have hm := v.no_mx_load i hi
    have hs := Code.all_instrs v.spSafe i hi
    simp only [hm, Bool.not_false, Bool.true_and]
    exact hs
  exact (show generationSafe (.block Impl.MillerRabin.X86_64.Caller.save) from rfl).seq
    ((h.call v.name).seq
      (show generationSafe (.block Impl.MillerRabin.X86_64.Caller.restore) from rfl))

theorem roundCode_depth (v : RoundImpl) : generationDepth (Kernel.called v).run := by
  change max 0 (max (v.code.x86_64Depth + 8) 0) ≤ 128
  simp only [Nat.zero_max, Nat.max_zero]
  have hd := v.depth
  change v.code.x86_64Depth ≤ 120 at hd
  omega

theorem roundMul_depth (v : RoundImpl) (o a b : Nat) : generationDepth (v.mont.mm o a b) := by
  unfold generationDepth
  rw [v.arithDepth]
  exact Nat.zero_le _

end VG.Proof.Dsa.X86_64.Generation
