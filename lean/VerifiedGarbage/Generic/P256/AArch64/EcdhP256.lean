module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
import VerifiedGarbage.Proof.P256.EcdhJac.Verified
public import VerifiedGarbage.Proof.P256.EcdhDouble.Certificate
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Data.BitVec
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.Ecdh.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.P256.EcdhInverse.Update
public import VerifiedGarbage.Proof.P256.EcdhJac.DbluCertificate
public import VerifiedGarbage.Proof.P256.EcdhJac.Lit
public import VerifiedGarbage.Proof.P256.EcdhJac.OutCertificate
public import VerifiedGarbage.Proof.P256.EcdhTable.Dblu
public import VerifiedGarbage.Proof.P256.EcdhTable.Zaddu
public import VerifiedGarbage.Proof.P256.Linear.WeakCertificate
public import VerifiedGarbage.Proof.P256.VerifyAllocated.CachedHead
public import VerifiedGarbage.Proof.P256.VerifyAllocated.JacTail
public import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedHead
public import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticCachedHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticRR
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Spec.Ecdh.P256
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.ClearExcept
import Mathlib.Data.Finset.Card
public import VerifiedGarbage.Proof.P256.EcdhJac.Verified
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Divstep.Bound
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowEntryTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSumTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafArithmeticTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafEntryTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Front
import VerifiedGarbage.Proof.P256.Prime
public import VerifiedGarbage.Proof.Divstep.Tc
public import VerifiedGarbage.Proof.Divstep.Word
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
public import VerifiedGarbage.Proof.Ecdh.AArch64.Verified
public import VerifiedGarbage.Proof.Ecdh.Exchange
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
public import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedArithmetic
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.P256.EcdhDouble.Field
public import VerifiedGarbage.Proof.P256.EcdhDouble.LinearField
public import VerifiedGarbage.Proof.P256.EcdhDouble.Verified
public import VerifiedGarbage.Proof.P256.EcdhInverse.Extra
public import VerifiedGarbage.Proof.P256.EcdhInverse.Extract
public import VerifiedGarbage.Proof.P256.EcdhInverse.Finish
public import VerifiedGarbage.Proof.P256.EcdhInverse.Inverse
public import VerifiedGarbage.Proof.P256.EcdhInverse.Packed
public import VerifiedGarbage.Proof.P256.EcdhInverse.RawUpdate
public import VerifiedGarbage.Proof.P256.EcdhInverse.Shift
public import VerifiedGarbage.Proof.P256.EcdhJac.BuildDblu
public import VerifiedGarbage.Proof.P256.EcdhJac.Dblu
public import VerifiedGarbage.Proof.P256.EcdhJac.Frame
public import VerifiedGarbage.Proof.P256.EcdhJac.Prefix
public import VerifiedGarbage.Proof.P256.EcdhJac.Select
public import VerifiedGarbage.Proof.P256.EcdhJac.Timing
public import VerifiedGarbage.Proof.P256.EcdhJac.Window
public import VerifiedGarbage.Proof.P256.EcdhTable.DbluRaw
public import VerifiedGarbage.Proof.P256.EcdhTable.Transfer
public import VerifiedGarbage.Proof.P256.Linear.WeakAdd
public import VerifiedGarbage.Proof.P256.VerifyAllocated.Timing
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedJointDigits
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedState
public import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedLoad
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticProduction
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyFinish
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvMain
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvRed
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvStep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvWords
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTableTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointEntry
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoad
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafEntry
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJDigit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Proof.Divstep.Incl
import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Divstep.Word
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdh.AArch64.Verified
import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedArithmetic
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.P256.EcdhDouble.Field
import VerifiedGarbage.Proof.P256.EcdhDouble.LinearField
import VerifiedGarbage.Proof.P256.EcdhDouble.Verified
import VerifiedGarbage.Proof.P256.EcdhInverse.Extra
import VerifiedGarbage.Proof.P256.EcdhInverse.Extract
import VerifiedGarbage.Proof.P256.EcdhInverse.Finish
import VerifiedGarbage.Proof.P256.EcdhInverse.Inverse
import VerifiedGarbage.Proof.P256.EcdhInverse.Packed
import VerifiedGarbage.Proof.P256.EcdhInverse.RawUpdate
import VerifiedGarbage.Proof.P256.EcdhInverse.Shift
import VerifiedGarbage.Proof.P256.EcdhJac.BuildDblu
import VerifiedGarbage.Proof.P256.EcdhJac.Dblu
import VerifiedGarbage.Proof.P256.EcdhJac.Frame
import VerifiedGarbage.Proof.P256.EcdhJac.Prefix
import VerifiedGarbage.Proof.P256.EcdhJac.Select
import VerifiedGarbage.Proof.P256.EcdhJac.Timing
import VerifiedGarbage.Proof.P256.EcdhJac.Window
import VerifiedGarbage.Proof.P256.EcdhTable.DbluRaw
import VerifiedGarbage.Proof.P256.EcdhTable.Transfer
import VerifiedGarbage.Proof.P256.Linear.WeakAdd
import VerifiedGarbage.Proof.P256.VerifyAllocated.Timing
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedJointDigits
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedState
import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticProduction
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyFinish
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvMain
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvRed
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvWords
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointEntry
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad

/-!
# ECDH over P-256 (SP 800-56A) on AArch64

A generic file (see `TCB/Emit.lean`) over P-256's group law `h`, the variant
`Variants/P256/AArch64/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P256.AArch64.EcdhP256

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvToMOrd Spec.P256.curve) : List Artifact := [
  Spec.Ecdh.P256.exchangeApi.artifact AArch64.target {
    notes := ["The peer's encoding and coordinates are checked \
      without branches. Scalar multiplication uses the peer's point when it is valid and the \
      generator otherwise. Field elements are four 64-bit Montgomery words. Signed 5-bit \
      windows recode the scalar as `d + 16 Σ_{j<52} 32^j`; a 16-entry Jacobian table is built \
      with co-Z doubling and additions and stores each point's `Z²` and `Z³`. The first digit \
      initializes the accumulator, followed by 51 iterations of five Jacobian doublings and \
      one cached Jacobian addition. Each selection scans all 16 entries with NEON masks, \
      interleaved with the window's fifth doubling, which uses only general registers, and \
      digit signs, zero digits and infinity accumulators are handled without secret branches \
      or secret addresses. Prime-order bounds establish the nonexceptional additions for \
      valid private scalars; invalid scalars still execute safely and are rejected by the \
      existing final range check. Register-allocated point arithmetic uses explicit scratch \
      spills and restores the additional ABI registers and live output pointer. Inversion \
      retains the fixed 590-divstep schedule. The result or zeros is selected by the input \
      checks, `d` in `[1, n-1]`, and a nonzero projective denominator. Time depends only on \
      the pointers; the public contract and 8192-byte scratch requirement are unchanged."]
    code := Impl.P256.EcdhJac.exchange
    verified := Proof.P256.EcdhJac.verified h.law h.inv h.prime h.invToMP }]

end VG.Generic.P256.AArch64.EcdhP256
