module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PublicKernel
public import VerifiedGarbage.Impl.Dsa.AArch64.ProbablePrime
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
public import VerifiedGarbage.Proof.Framework.AArch64.Depth
import VerifiedGarbage.Proof.RsaKeyGen.Table

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
    (Impl.Dsa.AArch64.ProbablePrime.test bits v.mont.mm (VG.Proof.Dsa.AArch64.Generation.publicKernel v).run).noFrames = true := by
  simp only [Impl.Dsa.AArch64.ProbablePrime.test, checkPrime, workspace, primeFromFrame, primeBytes,
    probablePrime, primeSetup, primeR2, primeConstants, millerRabin, drawRound, primeIteration, sampleRound,
    witnessRound, roundTail, sampleWitness, forceStoredWitness, testWitness, loadWitness, testRange, witnessRange,
    drawCopy, Impl.Dsa.AArch64.Arithmetic.constants, Impl.Rsa.AArch64.r2Steps,
    Impl.Rsa.AArch64.r2StepsOld, Impl.Rsa.AArch64.sqs, Impl.Bignum.AArch64.R2Div.choice, VG.Proof.Dsa.AArch64.Generation.publicKernel, VG.Proof.Dsa.AArch64.Generation.PublicKernel.called, Impl.MillerRabin.AArch64.Caller.call,
    List.cons_append, List.nil_append, Impl.Bignum.AArch64.seqs, Code.noFrames, Bool.and_eq_true, v.mmNoFrames, true_and, and_true]
  and_intros
  all_goals first | rfl | exact VG.Proof.Dsa.AArch64.Generation.publicRound_noFrames v.noFrames

open VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
  VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.MillerRabin.AArch64 in
/-- The round for public candidates never touches PSTATE.DIT where the
shared round does not: they differ in the selection, which is blocks and a
loop without it. -/
theorem publicRound_noDit {mul : Nat → Nat → Nat → Prog isa}
    (h : (VG.Impl.MillerRabin.AArch64.round mul).all (fun i => !i.touchesDit) = true) :
    (publicRound mul).all (fun i => !i.touchesDit) = true := by
  simp only [VG.Impl.MillerRabin.AArch64.round, roundW, preparedRoundW, mrExpLoopW, mrWin, mrWinS, mrSq, mrLast,
    tabBuild, toEnt, eqMask, VG.Impl.Rsa.AArch64.Keys.eqA, mrSel, VG.Impl.Rsa.AArch64.Keys.copyA, copyWords,
    countLoop, VG.Impl.Rsa.AArch64.Crt.selLoop,
    List.cons_append, List.nil_append, List.append_assoc, seqs, Code.all, Bool.and_eq_true] at h
  simp only [publicRound, publicWin, roundW, preparedRoundW, mrExpLoopW, mrWinS, mrSq, mrLast,
    tabBuild, toEnt, eqMask, VG.Impl.Rsa.AArch64.Keys.eqA, publicSel, VG.Impl.Rsa.AArch64.Keys.copyA, copyWords,
    countLoop,
    List.cons_append, List.nil_append, List.append_assoc, seqs, Code.all, Bool.and_eq_true, h, and_true,
    true_and]
  decide

/-- The test never touches PSTATE.DIT: neither its own code (decided for each
size, `Supported`, whose instruction lists are long) nor the round's. -/
theorem test_noDit (v : RoundImpl) {bits : Nat}
    (hb : bits = 160 ∨ bits = 256 ∨ bits = 1024 ∨ bits = 2048 ∨ bits = 3072) :
    (Impl.Dsa.AArch64.ProbablePrime.test bits v.mont.mm (VG.Proof.Dsa.AArch64.Generation.publicKernel v).run).all
      (fun i => !i.touchesDit) = true := by
  rcases hb with rfl | rfl | rfl | rfl | rfl <;>
  simp only [Impl.Dsa.AArch64.ProbablePrime.test, checkPrime, workspace, primeFromFrame, primeBytes,
    probablePrime, primeSetup, primeR2, primeConstants, millerRabin, drawRound, primeIteration, sampleRound,
    witnessRound, roundTail, sampleWitness, forceStoredWitness, testWitness, loadWitness, testRange, witnessRange,
    drawCopy, Impl.Dsa.AArch64.Arithmetic.constants, Impl.Rsa.AArch64.r2Steps,
    Impl.Rsa.AArch64.r2StepsOld, Impl.Rsa.AArch64.sqs, Impl.Bignum.AArch64.R2Div.choice, VG.Proof.Dsa.AArch64.Generation.publicKernel, VG.Proof.Dsa.AArch64.Generation.PublicKernel.called, Impl.MillerRabin.AArch64.Caller.call,
    List.cons_append, List.nil_append, Impl.Bignum.AArch64.seqs, Code.all, Bool.and_eq_true, v.mmNoDit,
    true_and] <;>
  and_intros <;>
  first | with_reducible exact publicRound_noDit v.noDit | lit_decide

end VG.Proof.Dsa.AArch64.ProbablePrime
