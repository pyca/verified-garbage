module

public import VerifiedGarbage.Impl.Dsa.AArch64.ProbablePrime
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
public import VerifiedGarbage.Proof.Framework.AArch64.Depth

/-! # The probable-prime test's frames: its own 272 bytes

The test itself has no frames (its arithmetic and the shared round have
none), so its stack is its frame. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.ProbablePrime
open VG VG.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem aarch64Depth_of_noFrames : ∀ (c : Prog isa), c.noFrames = true → c.aarch64Depth = 0
  | .block _, _ => rfl
  | .seq a b, h => by
    simp only [Code.noFrames, Bool.and_eq_true] at h
    simp only [Code.aarch64Depth, aarch64Depth_of_noFrames a h.1, aarch64Depth_of_noFrames b h.2, Nat.max_self]
  | .ite _ t e, h => by
    simp only [Code.noFrames, Bool.and_eq_true] at h
    simp only [Code.aarch64Depth, aarch64Depth_of_noFrames t h.1, aarch64Depth_of_noFrames e h.2, Nat.max_self]
  | .loop b _, h => by
    simp only [Code.noFrames] at h
    simp only [Code.aarch64Depth, aarch64Depth_of_noFrames b h]
  | .call _ b, h => by
    simp only [Code.noFrames] at h
    simp only [Code.aarch64Depth, aarch64Depth_of_noFrames b h]
  | .frame .., h => by simp [Code.noFrames] at h
  | .icall _ _ b n, h => by
    simp only [Code.noFrames, Bool.and_eq_true] at h
    simp only [Code.aarch64Depth, aarch64Depth_of_noFrames b h.1, aarch64Depth_of_noFrames n h.2, Nat.max_self]

theorem test_noFrames (v : RoundImpl) (bits : Nat) :
    (Impl.Dsa.AArch64.ProbablePrime.test bits v.mont.mm v.kernel.run).noFrames = true := by
  simp only [Impl.Dsa.AArch64.ProbablePrime.test, checkPrime, workspace, primeFromFrame, primeBytes,
    probablePrime, primeSetup, primeR2, primeConstants, millerRabin, drawRound, primeIteration, sampleRound,
    witnessRound, roundTail, sampleWitness, forceStoredWitness, testWitness, loadWitness, testRange, witnessRange,
    drawCopy, Impl.Dsa.AArch64.Arithmetic.constants, Impl.Rsa.AArch64.r2Steps,
    Impl.Rsa.AArch64.r2StepsOld, Impl.Rsa.AArch64.sqs, Impl.Bignum.AArch64.R2Div.choice, RoundImpl.kernel, MillerRabin.AArch64.Kernel.called, Impl.MillerRabin.AArch64.Caller.call,
    List.cons_append, List.nil_append, Impl.Bignum.AArch64.seqs, Code.noFrames, Bool.and_eq_true, v.mmNoFrames, true_and, and_true]
  and_intros
  all_goals first | exact v.noFrames | rfl

end VG.Proof.Dsa.AArch64.ProbablePrime
