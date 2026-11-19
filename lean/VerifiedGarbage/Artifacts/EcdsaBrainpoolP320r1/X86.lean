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
open VG.Proof.Ecdsa.Rfc6979.X86 (OK brainpoolp320r1SignReg)
open VG.Proof.HmacTable.X86 (names vars)

def artifacts : List Artifact :=
  if hv : OK (vars VG.Proof.Variants.Sha1.X86.variants VG.Proof.Variants.Sha256.X86.variants) ∧
      "VG_BRAINPOOLP320R1_COMB" ∉ names (vars VG.Proof.Variants.Sha1.X86.variants VG.Proof.Variants.Sha256.X86.variants) then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1SignApi.artifact X86.target (brainpoolp320r1SignReg hasLaw.law hv)]
  else []

end VG.Artifacts.EcdsaBrainpoolP320r1.X86.Rfc6979

namespace VG.Artifacts.EcdsaBrainpoolP320r1.X86

open VG.Proof.BrainpoolP320r1.X86 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.BrainpoolP320r1.verifyHashApi.artifact X86.target
    (Proof.Ecdsa.Verify.X86.BrainpoolP320r1.verifyReg hasLaw.law)] ++
  Rfc6979.artifacts

end VG.Artifacts.EcdsaBrainpoolP320r1.X86
