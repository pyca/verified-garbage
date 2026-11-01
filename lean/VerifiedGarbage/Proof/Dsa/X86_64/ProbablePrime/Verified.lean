module

public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.CT
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeTest
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundCode
public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Params
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Impl.Dsa.X86_64.ProbablePrime
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeSafety
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeDepth

import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Correct
import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Satisfiable
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeSafety
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeDepth
/-! # `vg_dsa_probable_prime` on x86-64 is verified

For each Miller–Rabin round implementation: the test multiplies with the
round's inlined arithmetic and calls the shared round. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/ProbablePrime/Safety.lean`, which only this module imported.
section

/-! # The probable-prime test neither loads MXCSR nor writes `rsp` but in its frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.Impl.Dsa.X86_64.ProbablePrime
open VG.Proof.Dsa.X86_64.Generation (generationSafe generationDepth)

theorem code_safe (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationSafe (mul o a b)) (hr : generationSafe round) :
    generationSafe (code mul round) := by
  have hs : generationSafe setup := rfl
  have hb := hs.seq ((VG.Proof.Dsa.X86_64.Generation.primeBytes_safe mul round hm hr).seq
    ((show generationSafe (.block exit) from rfl).seq (show generationSafe (.block restoreRegisters) from rfl)))
  have hb' : generationSafe (.seq setup
      (Impl.Bignum.X86_64.seqs [Impl.Dsa.X86_64.Generation.primeBytes mul round,
        .block exit, .block restoreRegisters])) := hb
  unfold generationSafe at hb'
  change ((true && _) && true) = true
  rw [hb']; rfl

theorem code_depth (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationDepth (mul o a b)) (hr : generationDepth round) :
    (code mul round).x86_64Depth ≤ 184 := by
  have hp := VG.Proof.Dsa.X86_64.Generation.primeBytes_depth mul round hm hr
  unfold generationDepth at hp
  simp only [code, setup, Impl.Bignum.X86_64.seqs, sizedWorkspace, Code.x86_64Depth, Instr.frameBytes,
    Nat.zero_max, Nat.max_zero]
  exact Nat.add_le_add_right hp 56

end VG.Proof.Dsa.X86_64.ProbablePrime
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

/-- The test's code with the round implementation `v`. -/
abbrev testCode (v : RoundImpl) : Prog isa :=
  Impl.Dsa.X86_64.ProbablePrime.code v.inlineMont.mm (Kernel.called v).run

theorem testCode_safe (v : RoundImpl) :
    VG.Proof.Dsa.X86_64.Generation.generationSafe (testCode v) :=
  code_safe _ _ v.inlineSafe (VG.Proof.Dsa.X86_64.Generation.roundCode_safe v)

theorem verified (v : RoundImpl) : Verified target (testCode v) contract :=
  ⟨correct v.inlineMont (Kernel.called v) (testCode_safe v).mx, code_ct _ _, satisfiable⟩

/-- The test with the round implementation `v`, as parameter generation
calls it. -/
def primeTest (v : RoundImpl) : VG.Proof.Dsa.X86_64.Generation.PrimeTest where
  name := "vg_dsa_probable_prime" ++ v.suffix
  code := testCode v
  verified := verified v
  safe := testCode_safe v
  depth := code_depth _ _ (VG.Proof.Dsa.X86_64.Generation.inlineMul_depth v)
    (VG.Proof.Dsa.X86_64.Generation.roundCode_depth v)

end VG.Proof.Dsa.X86_64.ProbablePrime
