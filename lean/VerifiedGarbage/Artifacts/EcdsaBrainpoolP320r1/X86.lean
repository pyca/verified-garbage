module

import VerifiedGarbage.Proof.Ecdsa.Verify.X86.BrainpoolP320r1.Lit
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP320r1.Verified
import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP320r1.CombLit
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP320r1.X86
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.BrainpoolP320r1.Verified
import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP320r1
public import VerifiedGarbage.Proof.BrainpoolP320r1.Point
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
import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.X86
import VerifiedGarbage.Proof.X25519.X86.Column
import VerifiedGarbage.Proof.Framework.X86.TaintMono
public import VerifiedGarbage.Impl.Ecdsa.X86.VerifyHash
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.BrainpoolP320r1.X86.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.BrainpoolP320r1
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Variants.Sha256.X86

public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.EcKey.X86.Scrub
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Scrub

/-! # ECDSA over brainpoolP320r1 (FIPS 186-5) on x86 -/

@[expose] public section

-- Deterministic ECDSA (RFC 6979) over brainpoolP320r1 on x86 (32-bit), with HMAC as a table
namespace VG.Artifacts.EcdsaBrainpoolP320r1.X86.Rfc6979

open VG.Proof.BrainpoolP320r1.X86 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.X86 (signCodeT OK brainpoolp320r1 brainpoolp320r1T_verified signCode_sp stackT
  brainpoolp320r1T_scrub)
open VG.Proof.HmacTable.X86 (tables names vars)

def artifacts : List Artifact :=
  if hv : OK (vars VG.Proof.Variants.Sha1.X86.variants VG.Proof.Variants.Sha256.X86.variants) ∧
      "VG_BRAINPOOLP320R1_COMB" ∉ names (vars VG.Proof.Variants.Sha1.X86.variants VG.Proof.Variants.Sha256.X86.variants) then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1SignApi.artifact X86.target (X86.Scrub.scrubFOf {
      tables := [("hmac", tables (vars VG.Proof.Variants.Sha1.X86.variants VG.Proof.Variants.Sha256.X86.variants))]
      code := signCodeT (brainpoolp320r1 hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1.tries
        (vars VG.Proof.Variants.Sha1.X86.variants VG.Proof.Variants.Sha256.X86.variants)
      verified := brainpoolp320r1T_verified hasLaw.law
        (vars VG.Proof.Variants.Sha1.X86.variants VG.Proof.Variants.Sha256.X86.variants) hv
      spSafe := signCode_sp _ _ _ }
      (Proof.Ecdsa.Rfc6979.X86.Scrub.signOut Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1
        Impl.Ecdsa.X86.brainpoolp320r1Comb.combConsts _)
      stackT (brainpoolp320r1T_scrub hasLaw.law))]
  else []

end VG.Artifacts.EcdsaBrainpoolP320r1.X86.Rfc6979

namespace VG.Artifacts.EcdsaBrainpoolP320r1.X86

open VG.Proof.BrainpoolP320r1.X86 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.BrainpoolP320r1.verifyHashApi.artifact X86.target (X86.Scrub.scrubFOf {
    code := Impl.Ecdsa.X86.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP320r1.inst.curve.len false
      Impl.Ecdsa.Verify.X86.verifyBrainpoolP320r1
    verified := Proof.Ecdsa.Verify.X86.BrainpoolP320r1.verifyHash_verified hasLaw.law }
    (Proof.EcKey.X86.Scrub.verifyHashOut (20 + Impl.Ecdsa.X86.VerifyHash.frameBytes)
      Impl.Ecdsa.X86.brainpoolp320r1Comb.combConsts Spec.Ecdsa.BrainpoolP320r1.inst))] ++
  Rfc6979.artifacts

end VG.Artifacts.EcdsaBrainpoolP320r1.X86
