module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.P224
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdsa.RISCV64.P224
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.VerifyVerified
import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.VerifyLit
import VerifiedGarbage.Proof.P224.RISCV64.Law
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.P224
import VerifiedGarbage.Proof.Variants.MdHash.RISCV64
import VerifiedGarbage.Impl.Ecdsa.Rfc6979.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDSA over P-224 (FIPS 186-5) on RISC-V -/

-- Deterministic ECDSA (RFC 6979) over P-224 on RISC-V, with HMAC as a table
namespace VG.Artifacts.EcdsaP224.RISCV64.Rfc6979

open VG.Proof.P224.RISCV64 (hasLaw)
open VG.Proof.HmacTable.RISCV64 (tables)
open VG.Proof.Variants.MdHash.RISCV64 (variants fns)

def artifacts : List (Artifact RISCV64.target) := [
  Spec.Ecdsa.Rfc6979.Curves.p224SignApi.artifact RISCV64.target {
    tables := [("hmac", tables variants)]
    code := Impl.Ecdsa.Rfc6979.RISCV64.Fn.p224 fns
    verified := Proof.Ecdsa.Rfc6979.RISCV64.P224.sign_scrubbed hasLaw.law }]

end VG.Artifacts.EcdsaP224.RISCV64.Rfc6979

namespace VG.Artifacts.EcdsaP224.RISCV64

open VG.Proof.P224.RISCV64 (hasLaw)

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Ecdsa.P224.verifyHashApi.artifact RISCV64.target {
    code := Impl.Ecdsa.RISCV64.Fn.verifyP224
    verified := Proof.Ecdsa.RISCV64.P224.verifyHash_scrubbed hasLaw.law }] ++
  Rfc6979.artifacts

spec_apis artifacts

end VG.Artifacts.EcdsaP224.RISCV64
