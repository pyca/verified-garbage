module

public import VerifiedGarbage.Impl.Dsa.X86_64.ProbablePrime
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeSafety
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeDepth
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeSafety
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeDepth

/-! # The probable-prime test neither loads MXCSR nor writes `rsp` but in its frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.Impl.Dsa.X86_64.ProbablePrime
open VG.Proof.Dsa.X86_64.Generation (generationSafe generationDepth)

theorem code_safe (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationSafe (mul o a b)) (hr : generationSafe round) (bits : Nat) :
    generationSafe (code bits mul round) := by
  have hs : generationSafe (setup bits) := rfl
  have hb := hs.seq ((VG.Proof.Dsa.X86_64.Generation.primeBytes_safe mul round hm hr (len bits) (draw bits)).seq
    ((show generationSafe (.block exit) from rfl).seq (show generationSafe (.block restoreRegisters) from rfl)))
  have hb' : generationSafe (.seq (setup bits)
      (Impl.Bignum.X86_64.seqs [Impl.Dsa.X86_64.Generation.primeBytes mul round (len bits) (draw bits),
        .block exit, .block restoreRegisters])) := hb
  unfold generationSafe at hb'
  change ((true && _) && true) = true
  rw [hb']; rfl

theorem code_depth (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationDepth (mul o a b)) (hr : generationDepth round) (bits : Nat) :
    (code bits mul round).x86_64Depth ≤ 184 := by
  have hp := VG.Proof.Dsa.X86_64.Generation.primeBytes_depth mul round hm hr (len bits) (draw bits)
  unfold generationDepth at hp
  simp only [code, setup, Impl.Bignum.X86_64.seqs, Impl.Dsa.X86_64.Generation.workspace, Code.x86_64Depth, Instr.frameBytes,
    Nat.zero_max, Nat.max_zero]
  exact Nat.add_le_add_right hp 56

end VG.Proof.Dsa.X86_64.ProbablePrime
