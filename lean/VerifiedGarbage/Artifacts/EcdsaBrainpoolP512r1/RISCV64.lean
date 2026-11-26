module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP512r1
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP512r1.SignVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.RISCV64.Ecdsa
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP512r1.VerifyVerified
import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP512r1.SignLit
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP512r1.VerifyLit
import VerifiedGarbage.Proof.BrainpoolP512r1.RISCV64.Law
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP512r1
import VerifiedGarbage.Proof.Variants.MdHash.RISCV64
import VerifiedGarbage.Impl.Ecdsa.Rfc6979.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDSA over brainpoolP512r1 (FIPS 186-5) on RISC-V -/

-- Deterministic ECDSA (RFC 6979) over brainpoolP512r1 on RISC-V, with HMAC as a table
namespace VG.Artifacts.EcdsaBrainpoolP512r1.RISCV64.Rfc6979

open VG.Proof.BrainpoolP512r1.RISCV64 (hasLaw)
open VG.Proof.HmacTable.RISCV64 (tables)
open VG.Proof.Variants.MdHash.RISCV64 (variants fns)

def artifacts : List (Artifact RISCV64.target) := [
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1SignApi.artifact RISCV64.target {
    tables := [("hmac", tables variants)]
    code := Impl.Ecdsa.Rfc6979.RISCV64.Fn.brainpoolp512r1 fns
    verified := Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP512r1.sign_scrubbed hasLaw.law }]

end VG.Artifacts.EcdsaBrainpoolP512r1.RISCV64.Rfc6979

namespace VG.Artifacts.EcdsaBrainpoolP512r1.RISCV64

open VG.Proof.BrainpoolP512r1.RISCV64 (hasLaw)

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Ecdsa.BrainpoolP512r1.verifyHashApi.artifact RISCV64.target {
    code := Impl.Ecdsa.RISCV64.Fn.verifyBrainpoolP512r1
    verified := Proof.Ecdsa.RISCV64.BrainpoolP512r1.verifyHash_scrubbed hasLaw.law }] ++
  Rfc6979.artifacts

spec_apis artifacts

end VG.Artifacts.EcdsaBrainpoolP512r1.RISCV64
