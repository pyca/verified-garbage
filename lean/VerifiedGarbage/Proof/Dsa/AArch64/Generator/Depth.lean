module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generator
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
public import VerifiedGarbage.Proof.Framework.AArch64.Depth
import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Depth

/-! # The generator stage's frames: its own 272 bytes

The stage itself has no frames (its arithmetic has none), so its stack is
its frame. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem stage_noFrames (v : RoundImpl) (pLen : Nat) :
    (Impl.Dsa.AArch64.Generator.stage v.mont.mm pLen).noFrames = true := by
  simp only [Impl.Dsa.AArch64.Generator.stage, generatorSearch, tapeLoop, tapeIteration, generatorStep, generatorRangeFromFrame, generatorEvaluate, onSuccess, finishDomain, pack, packPart, validate, Code.noFrames, Impl.Bignum.AArch64.seqs, workspace, generatorRange, generatorResult, generatorPowerFresh, generatorModulus, generatorPower, generatorLoadPair, Impl.Dsa.AArch64.Random.copyRest, Impl.Dsa.AArch64.Generate.checkParameters, Impl.Dsa.AArch64.Core.publicPow, Impl.Dsa.AArch64.Checks.signingKey, Impl.Dsa.AArch64.Checks.publicPrefix, Impl.Dsa.AArch64.PublicPower.power, Impl.Dsa.AArch64.Core.reduce, Impl.Dsa.AArch64.Arithmetic.constants, Impl.Dsa.AArch64.PublicPower.powerCore, Impl.Dsa.AArch64.Arithmetic.load, Impl.Dsa.AArch64.Core.finish, Impl.Rsa.AArch64.r2Steps, Impl.Dsa.AArch64.Arithmetic.encodePower, Impl.Dsa.AArch64.PublicPower.encodedPower, Impl.Dsa.AArch64.Arithmetic.reduce, Impl.Bignum.AArch64.R2Div.choice, Impl.Rsa.AArch64.r2StepsOld, Impl.Rsa.AArch64.sqs, Impl.Dsa.AArch64.PublicPower.expLoop, Impl.Dsa.AArch64.Arithmetic.reduceSetup, Impl.Dsa.AArch64.Arithmetic.reduceByte, Impl.Rsa.AArch64.Crt.tabBuild, Impl.Rsa.AArch64.Crt.toEnt, Impl.Rsa.AArch64.Crt.copyArr, Impl.Rsa.AArch64.Crt.nextEnt, Impl.Dsa.AArch64.PublicPower.window, Impl.Dsa.AArch64.PublicPower.applyWindow, Impl.Dsa.AArch64.Arithmetic.reduceStep, List.append_assoc, v.mmNoFrames, Bool.and_eq_true, List.cons_append, List.nil_append]
  and_intros
  all_goals decide +kernel

/-- The stage's frames: its own 272 bytes. -/
theorem code_depth (v : RoundImpl) (pLen : Nat) :
    16 * (Impl.Dsa.AArch64.Generator.code v.mont.mm pLen).aarch64Depth ≤ 272 := by
  have h := ProbablePrime.aarch64Depth_of_noFrames _ (stage_noFrames v pLen)
  simp only [Impl.Dsa.AArch64.Generator.code, Impl.Bignum.AArch64.seqs, Code.aarch64Depth, h,
    AArch64.Instr.frameUnits]
  decide

end VG.Proof.Dsa.AArch64.Generator
