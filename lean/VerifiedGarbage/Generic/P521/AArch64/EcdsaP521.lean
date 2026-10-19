module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.P521.Comb7
import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified
public import VerifiedGarbage.Impl.Ecdsa.Verify.P521.AArch64
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.AArch64Instrs
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Spec.Ecdsa.Verify.P521
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointVerified
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointVerified
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Impl.Ecdsa.P521.AArch64
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Verified
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Impl.Ecdh.P256.AArch64
public import VerifiedGarbage.Impl.Ecdh.P521.AArch64
public import VerifiedGarbage.Impl.Ecdsa.Verify.P256.AArch64
public import VerifiedGarbage.Impl.P256.VerifyRegisters
public import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombJ
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Finish
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Middle
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Padd
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Scalar
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
public import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
public import VerifiedGarbage.Proof.Ecdsa.Projective
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacChecks
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPoints
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafWindowTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Checks
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointAbi
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointBoundaryTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointChecks
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointContract
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointDigitsTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixed
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedBridge
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedChecks
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedPoint
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedSignTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedTable
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointLoopTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointMain
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointPoints
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointPointsTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointPrep
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointPrepTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointTopTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointWindow
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointWindowTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.PackedMul
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafMul
public import VerifiedGarbage.Proof.P521.Point
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
public import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafArith
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafState
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CT
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombOut
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombSum
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedAddB
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTimingB
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTree
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowFinishTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoop
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoopTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSum
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSumTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointEntry
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedDigit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedLookupTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoad
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafArithmeticTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafFinish
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafFinishTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafLoop
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafLoopTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafSum
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTable
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableCopy
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableInit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableStep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableTimingStep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafWindow
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Add
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddC
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.CacheBuild
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Copy
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.JointFinish
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.TableCoZ
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Wide
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WideInit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WidePrep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WideStep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Window
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowEntry
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowSum
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowTable
public import VerifiedGarbage.Proof.Weierstrass.BytesLen
public import VerifiedGarbage.Proof.Weierstrass.CoZTable
public import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
public import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Impl.Ecdh.P256.AArch64
import VerifiedGarbage.Impl.Ecdh.P521.AArch64
import VerifiedGarbage.Impl.Ecdsa.Verify.P256.AArch64
import VerifiedGarbage.Impl.P256.VerifyRegisters
import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombJ
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdsa.AArch64.Finish
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.AArch64.Middle
import VerifiedGarbage.Proof.Ecdsa.AArch64.Padd
import VerifiedGarbage.Proof.Ecdsa.AArch64.Scalar
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.Projective
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafWindowTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Checks
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointAbi
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointBoundaryTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointContract
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointDigitsTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixed
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedBridge
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedPoint
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedSignTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedTable
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointLoopTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointMain
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointPointsTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointPrep
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointPrepTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointTopTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointWindow
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointWindowTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.PackedMul
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafMul
import VerifiedGarbage.Proof.P521.Point
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafArith
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafState
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CT
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombOut
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedAddB
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTimingB
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTree
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowFinishTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoop
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoopTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSumTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointEntry
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedLookupTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafArithmeticTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafFinish
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafFinishTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafLoop
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafLoopTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTable
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableCopy
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableInit
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableTimingStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafWindow
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Add
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddC
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.CacheBuild
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.JointFinish
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.TableCoZ
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Wide
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WideInit
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WidePrep
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WideStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowEntry
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowTable
import VerifiedGarbage.Proof.Weierstrass.BytesLen
import VerifiedGarbage.Proof.Weierstrass.CoZTable
import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
import VerifiedGarbage.Proof.Weierstrass.WinJacMath

/-!
# ECDSA over P-521 (FIPS 186-5) on AArch64

A generic file (see `TCB/Emit.lean`) over P-521's group law `h`, the variant
`Variants/P521/AArch64/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P521.AArch64.EcdsaP521

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvOrd Spec.P521.curve) : List Artifact := [
  Spec.Ecdsa.P521.signApi.artifact AArch64.target {
    notes := ["The function saves the callee-saved registers \
      `x19`–`x25` in `scratch`. Field elements and scalars are nine 64-bit words in \
      Montgomery form, field elements multiplied by calls of `vg_p521_mul_mod_p` (word-by-word \
      Montgomery multiplication with all of `[b]` in registers, whose reductions are shifts, \
      P-521's `p` being friendly, and a final conditional subtraction), and scalars multiplied by \
      calls of `vg_p521_mul_mod_n` (word-by-word Montgomery multiplication, CIOS, with a final \
      conditional subtraction). `[k]G` is a fixed-base comb of 7-bit signed digits: the 83 windows \
      `k_j` of \
      `k`'s bits as digits `k_j - 64` from `-64` to `63`, `[k]G = [64 Σ 2^(7j)]G + Σ [(k_j - 64) \
      2^(7j)]G`, from 83 tables of `[m 2^(7j)]G` (`m = 1 … 64`, affine, in Montgomery form) in the \
      static `VG_P521_COMB` (747 KB), with no doublings: each entry is selected in constant time by \
      loading every entry of its table and keeping, with `csel`, the one of the digit's magnitude \
      (or the point at infinity for a zero digit), its `x` in one pass over the table and its `y` \
      in another, negated by a mask of its sign, and added by the complete addition formulas of \
      Renes, Costello and Batina for `a = -3` (Algorithm 4: 12 products and 2 by `b`); the \
      inversions modulo `p` and `n` are \
      by divsteps (Bernstein and Yang's safegcd, half-delta form): 23 batches of 59 \
      divsteps on the low 64-bit words of `f` and `g` (from `f = p`, `g = Z`, or `n` and `k`), each giving a matrix of \
      64-bit entries that updates `f`, `g` (divided by 2⁵⁹) and the coefficients `a`, `b` \
      (divided by 2⁶⁴ modulo `p` or `n`, as in Montgomery reduction), 1357 divsteps in all, enough for \
      576-bit moduli by Bernstein and Yang's bound (which the proof checks); then `f = ±1`, and `Z⁻¹` is `a` times a \
      constant or its negation by `f`'s sign. The number of steps is fixed, so the time does not \
      depend on `Z` or `k`. The signature \
      (or zeros) is selected by a mask, so the time depends only on the pointers."]
    consts := Impl.Ecdsa.AArch64.p521.combConsts
    code := Impl.Ecdsa.AArch64.signP521
    verified := Proof.Ecdsa.AArch64.P521.sign_verified h.law h.inv (Proof.P521.combOk7 h.law) },
  Spec.Ecdsa.P521.verifyApi.artifact AArch64.target {
    notes := ["The function validates the public key and signature and computes \
      `[u]G + [v]Q` with one interleaved Jacobian doubling chain. Public width-seven NAF \
      digits select affine generator multiples from the first row of `VG_P521_COMB`; \
      public width-five NAF digits select eight odd peer multiples built with co-Z \
      arithmetic, with cached `Z²` and `Z³` packed into the existing scratch space. \
      Both recodings cover 577 positions. Nonzero generator digits use mixed Jacobian \
      addition; peer digits use the cached Jacobian addition, including exceptional cases. \
      Nine-word field products use Montgomery multiplication, and field squares use the \
      dedicated symmetric P-521 square with Mersenne reduction. The scalar inverse uses \
      fixed-count divsteps. Invalid keys are replaced with the generator for arithmetic, \
      while the final mask retains all original validity checks. Projective comparisons \
      test `X = rZ` and, when applicable, `X = (r+n)Z` without a final inversion. \
      The function preserves the original verification contract and scratch size; \
      branches and table addresses depend only on the public key, digest and signature."]
    consts := Impl.Ecdsa.AArch64.p521.combConsts
    code := Impl.Ecdsa.Verify.AArch64.verifyP521
    verified := Proof.Ecdsa.Verify.AArch64.P521.verify_verified h.law h.prime h.inv (Proof.P521.combOk7 h.law) }]

end VG.Generic.P521.AArch64.EcdsaP521
