module
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P224.Lit

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.X86.P224.Verified
import VerifiedGarbage.Proof.Ecdsa.X86.P224.Lit
public import VerifiedGarbage.Impl.Ecdsa.Verify.P224.X86
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P224.Verified
import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.P224
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.X86.Peer
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Final
public import VerifiedGarbage.Proof.Ecdsa.X86.Inv
public import VerifiedGarbage.Proof.Ecdsa.X86.Lays
public import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
public import VerifiedGarbage.Proof.Ecdsa.X86.Setup
public import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.BitByte
public import VerifiedGarbage.Proof.Framework.NativeTaint
public import VerifiedGarbage.Proof.Framework.NativeTaintCore
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Proof.Framework.X86.Mmx
public import VerifiedGarbage.Proof.Framework.X86.RegUpd
public import VerifiedGarbage.Proof.Mont.X86.Csub
public import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Mont.X86.RedRow
public import VerifiedGarbage.Proof.Mont.X86.Row
public import VerifiedGarbage.Proof.Mont.X86.Step
public import VerifiedGarbage.Proof.P224.Point
public import VerifiedGarbage.Proof.Rc2.Memory32
public import VerifiedGarbage.Proof.Weierstrass.InvToM
import VerifiedGarbage.Proof.Weierstrass.Words32
public import VerifiedGarbage.Proof.Weierstrass.X86.Bits
public import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
public import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
public import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
public import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
public import VerifiedGarbage.Proof.Weierstrass.X86.Loop
public import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
public import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareArithmetic
public import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareRed
public import VerifiedGarbage.Proof.Weierstrass.X86.P256Power
public import VerifiedGarbage.Proof.Weierstrass.X86.Rep
public import VerifiedGarbage.Proof.Weierstrass.X86.ScalarPower
public import VerifiedGarbage.Proof.X25519.Field
public import VerifiedGarbage.Proof.X25519.X86.Arith
public import VerifiedGarbage.Proof.X25519.X86.Fold
import VerifiedGarbage.Impl.Ecdsa.P224.X86
import VerifiedGarbage.Proof.X25519.X86.Column
import VerifiedGarbage.Proof.Framework.X86.TaintMono
public import VerifiedGarbage.Impl.Ecdsa.X86.VerifyHash
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.P224.X86.Law

/-! # ECDSA over P-224 (FIPS 186-5) on x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.EcdsaP224.X86

open VG.Proof.P224.X86 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P224.verifyHashApi.artifact X86.target {
    code := Impl.Ecdsa.X86.VerifyHash.verifyHash Spec.Ecdsa.P224.inst.curve.len false
      Impl.Ecdsa.Verify.X86.verifyP224
    stack := 136
    verified := Proof.Ecdsa.Verify.X86.P224.verifyHash_verified hasLaw.law }]

end VG.Artifacts.EcdsaP224.X86
