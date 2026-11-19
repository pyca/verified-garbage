module

public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.P256.EcdhJac.Verified
public import VerifiedGarbage.Proof.P256.EcdhDouble.Certificate
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
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
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Divstep.Incl
import VerifiedGarbage.Proof.Framework.Pratt
public import VerifiedGarbage.Proof.P256.AArch64.Law

/-! # ECDH over P-256 (SP 800-56A) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.EcdhP256.AArch64

open VG.Proof.P256.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P256.exchangeApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    code := Impl.P256.EcdhJac.exchange
    verified := Proof.P256.EcdhJac.verified hasLaw.law hasLaw.inv hasLaw.prime hasLaw.invToMP }
      ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
       [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
       .v26, .v27, .v28, .v29, .v30, .v31],
       []⟩ (Proof.EcKey.AArch64.Scrub.exchangeOk _))]

end VG.Artifacts.EcdhP256.AArch64
