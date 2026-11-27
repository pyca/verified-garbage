module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP320r1
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.BrainpoolP320r1.Lit
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP320r1.Verified
import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP320r1.CombLit
import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP320r1.X86
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.BrainpoolP320r1.Verified
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.BrainpoolP320r1.Point
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.X86.Peer
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Final
import VerifiedGarbage.Proof.Ecdsa.X86.Inv
import VerifiedGarbage.Proof.Ecdsa.X86.Lays
import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
import VerifiedGarbage.Proof.Ecdsa.X86.Setup
import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.NativeTaint
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Mont.X86.Csub
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.Row
import VerifiedGarbage.Proof.Mont.X86.Step
import VerifiedGarbage.Proof.Rc2.Memory32
import VerifiedGarbage.Proof.Weierstrass.InvToM
import VerifiedGarbage.Proof.Weierstrass.Words32
import VerifiedGarbage.Proof.Weierstrass.X86.Bits
import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
import VerifiedGarbage.Proof.Weierstrass.X86.P256Power
import VerifiedGarbage.Proof.Weierstrass.X86.Rep
import VerifiedGarbage.Proof.Weierstrass.X86.ScalarPower
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.X25519.X86.Arith
import VerifiedGarbage.Proof.X25519.X86.Fold
import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.X86
import VerifiedGarbage.Proof.X25519.X86.Column
import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Impl.Ecdsa.X86.VerifyHash
import VerifiedGarbage.Proof.BrainpoolP320r1.X86.Law
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.BrainpoolP320r1
import VerifiedGarbage.Proof.Variants.Sha1.X86
import VerifiedGarbage.Proof.Variants.Sha256.X86
import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.X86Fn
import VerifiedGarbage.Proof.EcKey.X86.Scrub
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Scrub
import VerifiedGarbage.Proof.Framework.SpecApis


/-! # ECDSA over brainpoolP320r1 (FIPS 186-5) on x86 -/

-- Deterministic ECDSA (RFC 6979) over brainpoolP320r1 on x86 (32-bit), with HMAC as a table
namespace VG.Artifacts.EcdsaBrainpoolP320r1.X86.Rfc6979

open VG.Proof.BrainpoolP320r1.X86 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.X86 (OK brainpoolp320r1Sign_scrubbed)
open VG.Proof.HmacTable.X86 (names vars tables fnsOf)

def artifacts : List (Artifact X86.target) :=
  if hv : OK (vars VG.Proof.Variants.Sha1.X86.variants VG.Proof.Variants.Sha256.X86.variants) ∧
      "VG_BRAINPOOLP320R1_COMB" ∉ names (vars VG.Proof.Variants.Sha1.X86.variants VG.Proof.Variants.Sha256.X86.variants) then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1SignApi.artifact X86.target {
      tables := [("hmac", tables (vars VG.Proof.Variants.Sha1.X86.variants VG.Proof.Variants.Sha256.X86.variants))]
      code := Impl.Ecdsa.X86.Fn.signBrainpoolP320r1 (fnsOf (vars VG.Proof.Variants.Sha1.X86.variants VG.Proof.Variants.Sha256.X86.variants))
      verified := Proof.Ecdsa.Rfc6979.X86.brainpoolp320r1Sign_scrubbed hasLaw.law hv }]
  else []

end VG.Artifacts.EcdsaBrainpoolP320r1.X86.Rfc6979

namespace VG.Artifacts.EcdsaBrainpoolP320r1.X86

open VG.Proof.BrainpoolP320r1.X86 (hasLaw)

public def artifacts : List (Artifact X86.target) := [
  Spec.Ecdsa.BrainpoolP320r1.verifyHashApi.artifact X86.target {
    code := Impl.Ecdsa.X86.Fn.verifyBrainpoolP320r1
    verified := Proof.Ecdsa.Verify.X86.BrainpoolP320r1.verify_scrubbed hasLaw.law }] ++
  Rfc6979.artifacts

spec_apis artifacts

end VG.Artifacts.EcdsaBrainpoolP320r1.X86
