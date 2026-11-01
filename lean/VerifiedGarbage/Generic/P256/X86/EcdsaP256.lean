module
import VerifiedGarbage.Proof.Ecdsa.X86.CombLit

public import VerifiedGarbage.Proof.Ecdsa.X86.CombVerified
import VerifiedGarbage.Proof.Ecdsa.X86.Lit
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombVerified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombContract
public import VerifiedGarbage.Spec.Ecdsa.Verify.P256
public import VerifiedGarbage.Proof.Ecdsa.X86.CombContract
import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.X86.Peer
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombBodyCT
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombMain
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombStagesCT
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Final
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafCallerCT
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafLayout
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafMulTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.WindowPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.WindowPrep
import VerifiedGarbage.Proof.Ecdsa.X86.CombCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombMain
import VerifiedGarbage.Proof.Ecdsa.X86.Finish
import VerifiedGarbage.Proof.Ecdsa.X86.Inv
import VerifiedGarbage.Proof.Ecdsa.X86.Lays
import VerifiedGarbage.Proof.Ecdsa.X86.Middle
import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
import VerifiedGarbage.Proof.Ecdsa.X86.Scalar
import VerifiedGarbage.Proof.Ecdsa.X86.Setup
import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.NativeTaint
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Mont.Words128
import VerifiedGarbage.Proof.Mont.X86.Csub
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.P256Red
import VerifiedGarbage.Proof.Mont.X86.RedRow
import VerifiedGarbage.Proof.Mont.X86.Row
import VerifiedGarbage.Proof.Mont.X86.SparseShift
import VerifiedGarbage.Proof.Mont.X86.SparseStep
import VerifiedGarbage.Proof.Mont.X86.Step
import VerifiedGarbage.Proof.P256.Order
import VerifiedGarbage.Proof.P256.Prime
import VerifiedGarbage.Proof.Rc2.Memory32
import VerifiedGarbage.Proof.Weierstrass.BytesLen
import VerifiedGarbage.Proof.Weierstrass.InvToM
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Weierstrass.Window5
import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.FprogJ
import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
import VerifiedGarbage.Proof.Weierstrass.X86.JacAdd
import VerifiedGarbage.Proof.Weierstrass.X86.JacState
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareArithmetic
import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareRed
import VerifiedGarbage.Proof.Weierstrass.X86.NafArithmeticTiming
import VerifiedGarbage.Proof.Weierstrass.X86.NafPoint
import VerifiedGarbage.Proof.Weierstrass.X86.NafPublicFields
import VerifiedGarbage.Proof.Weierstrass.X86.NafTableFields
import VerifiedGarbage.Proof.Weierstrass.X86.P256Power
import VerifiedGarbage.Proof.Weierstrass.X86.PointFieldTiming
import VerifiedGarbage.Proof.Weierstrass.X86.Rep
import VerifiedGarbage.Proof.Weierstrass.X86.ScalarPower
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJ
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJEntry
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJSelect
import VerifiedGarbage.Proof.Weierstrass.X86.TCombOne
import VerifiedGarbage.Proof.Weierstrass.X86.WinEntry
import VerifiedGarbage.Proof.Weierstrass.X86.WinLoop
import VerifiedGarbage.Proof.Weierstrass.X86.WinSelect
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.X25519.X86.Arith
import VerifiedGarbage.Proof.X25519.X86.Fold
public import VerifiedGarbage.Proof.Weierstrass.X86.InvInterface
import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P256.X86
import VerifiedGarbage.Proof.X25519.X86.Column
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.X86.Peer
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombBodyCT
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombMain
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombPoints
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombStagesCT
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Final
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafCallerCT
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafLayout
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafMulTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.WindowPoints
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.WindowPrep
public import VerifiedGarbage.Proof.Ecdsa.X86.CombCT
public import VerifiedGarbage.Proof.Ecdsa.X86.CombMain
public import VerifiedGarbage.Proof.Ecdsa.X86.Finish
public import VerifiedGarbage.Proof.Ecdsa.X86.Inv
public import VerifiedGarbage.Proof.Ecdsa.X86.Lays
public import VerifiedGarbage.Proof.Ecdsa.X86.Middle
public import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
public import VerifiedGarbage.Proof.Ecdsa.X86.Scalar
public import VerifiedGarbage.Proof.Ecdsa.X86.Setup
public import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.BitByte
public import VerifiedGarbage.Proof.Framework.NativeTaint
public import VerifiedGarbage.Proof.Framework.NativeTaintCore
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Pratt
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Proof.Framework.X86.Mmx
public import VerifiedGarbage.Proof.Framework.X86.RegUpd
public import VerifiedGarbage.Proof.Framework.X86.Sse
public import VerifiedGarbage.Proof.Mont.Words128
public import VerifiedGarbage.Proof.Mont.X86.Csub
public import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Mont.X86.P256Red
public import VerifiedGarbage.Proof.Mont.X86.RedRow
public import VerifiedGarbage.Proof.Mont.X86.Row
public import VerifiedGarbage.Proof.Mont.X86.SparseShift
public import VerifiedGarbage.Proof.Mont.X86.SparseStep
public import VerifiedGarbage.Proof.Mont.X86.Step
public import VerifiedGarbage.Proof.P256.Order
public import VerifiedGarbage.Proof.P256.Prime
public import VerifiedGarbage.Proof.Rc2.Memory32
public import VerifiedGarbage.Proof.Weierstrass.BytesLen
public import VerifiedGarbage.Proof.Weierstrass.InvToM
public import VerifiedGarbage.Proof.Weierstrass.TCombWords
public import VerifiedGarbage.Proof.Weierstrass.Window5
public import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
public import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
public import VerifiedGarbage.Proof.Weierstrass.X86.FprogJ
public import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
public import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
public import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
public import VerifiedGarbage.Proof.Weierstrass.X86.JacAdd
public import VerifiedGarbage.Proof.Weierstrass.X86.JacState
public import VerifiedGarbage.Proof.Weierstrass.X86.Loop
public import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
public import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareArithmetic
public import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareRed
public import VerifiedGarbage.Proof.Weierstrass.X86.NafArithmeticTiming
public import VerifiedGarbage.Proof.Weierstrass.X86.NafPoint
public import VerifiedGarbage.Proof.Weierstrass.X86.NafPublicFields
public import VerifiedGarbage.Proof.Weierstrass.X86.NafTableFields
public import VerifiedGarbage.Proof.Weierstrass.X86.P256Power
public import VerifiedGarbage.Proof.Weierstrass.X86.PointFieldTiming
public import VerifiedGarbage.Proof.Weierstrass.X86.Rep
public import VerifiedGarbage.Proof.Weierstrass.X86.ScalarPower
public import VerifiedGarbage.Proof.Weierstrass.X86.TCombJ
public import VerifiedGarbage.Proof.Weierstrass.X86.TCombJDigit
public import VerifiedGarbage.Proof.Weierstrass.X86.TCombJEntry
public import VerifiedGarbage.Proof.Weierstrass.X86.TCombJSelect
public import VerifiedGarbage.Proof.Weierstrass.X86.TCombOne
public import VerifiedGarbage.Proof.Weierstrass.X86.WinEntry
public import VerifiedGarbage.Proof.Weierstrass.X86.WinLoop
public import VerifiedGarbage.Proof.Weierstrass.X86.WinSelect
public import VerifiedGarbage.Proof.X25519.Field
public import VerifiedGarbage.Proof.X25519.X86.Arith
public import VerifiedGarbage.Proof.X25519.X86.Fold

/-! # ECDSA over P-256 (FIPS 186-5) on x86 (32-bit) -/

@[expose] public section

namespace VG.Generic.P256.X86.EcdsaP256

def artifacts (h : Proof.Weierstrass.X86.Inv.HasLawInvOrd Spec.P256.curve) : List Artifact := [
  Spec.Ecdsa.P256.verifyApi.artifact X86.target {
    code := Proof.Ecdsa.Verify.X86.vCombCode
    consts := Impl.Ecdsa.X86.p256Comb.combConsts
    stack := 20
    verified := Proof.Ecdsa.Verify.X86.vComb_verified h.law h.inv }]

end VG.Generic.P256.X86.EcdsaP256
