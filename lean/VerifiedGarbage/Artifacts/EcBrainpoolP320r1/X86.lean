module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.BrainpoolP320r1.X86
public import VerifiedGarbage.Proof.EcKey.X86.BrainpoolP320r1.Verified
public import VerifiedGarbage.Proof.EcKey.X86.BrainpoolP320r1.Lit
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Spec.EcKey.BrainpoolP320r1
import VerifiedGarbage.Proof.X25519.X86.Column
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.EcKey.X86.Finish
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.X86.Finish
public import VerifiedGarbage.Proof.Ecdsa.X86.Lays
public import VerifiedGarbage.Proof.Ecdsa.X86.Main
public import VerifiedGarbage.Proof.Ecdsa.X86.Middle
public import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
public import VerifiedGarbage.Proof.Ecdsa.X86.Scalar
public import VerifiedGarbage.Proof.Ecdsa.X86.Setup
public import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
public import VerifiedGarbage.Proof.Framework.BitByte
public import VerifiedGarbage.Proof.Framework.NativeTaint
public import VerifiedGarbage.Proof.Framework.NativeTaintCore
public import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Proof.Rc2.Memory32
public import VerifiedGarbage.Proof.Weierstrass.InvToM
public import VerifiedGarbage.Proof.Weierstrass.X86.Bits
public import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
public import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
public import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
public import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
public import VerifiedGarbage.Proof.Weierstrass.X86.Loop
public import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareArithmetic
public import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareRed
public import VerifiedGarbage.Proof.Weierstrass.X86.Rep
public import VerifiedGarbage.Proof.X25519.Field
public import VerifiedGarbage.Proof.X25519.X86.Arith
public import VerifiedGarbage.Proof.X25519.X86.Fold
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.BrainpoolP320r1.X86.Law
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.BrainpoolP320r1
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.BrainpoolP320r1Decompress
public import VerifiedGarbage.Proof.EcKey.X86.BrainpoolP320r1.Scrub

/-! # brainpoolP320r1 public keys (FIPS 186-5 §A.2) on x86 -/

@[expose] public section

namespace VG.Artifacts.EcBrainpoolP320r1.X86

open VG.Proof.BrainpoolP320r1.X86 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP320r1.publicKeyApi.artifact X86.target (Proof.EcKey.X86.BrainpoolP320r1.Scrub.publicKeyReg hasLaw.law),
  Spec.EcKey.BrainpoolP320r1.inst.compressPublicKeyApi.artifact X86.target Proof.EcKey.X86.BrainpoolP320r1.Scrub.compressReg,
  Spec.EcKey.BrainpoolP320r1.inst.decompressPublicKeyApi.artifact X86.target (Proof.EcKey.X86.BrainpoolP320r1.Scrub.decompressReg hasLaw.law)]

end VG.Artifacts.EcBrainpoolP320r1.X86
