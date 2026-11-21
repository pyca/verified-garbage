module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.P192
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.VerifyVerified
public import VerifiedGarbage.Spec.Ecdsa.Verify.P192
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.VerifyLit
public import VerifiedGarbage.Proof.P192.RISCV64.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.P192
public import VerifiedGarbage.Proof.Variants.MdHash.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.RISCV64.Fn

/-! # ECDSA over P-192 (FIPS 186-5) on RISC-V -/

@[expose] public section

-- Deterministic ECDSA (RFC 6979) over P-192 on RISC-V, with HMAC as a table
namespace VG.Artifacts.EcdsaP192.RISCV64.Rfc6979

open VG.Proof.P192.RISCV64 (hasLaw)
open VG.Proof.HmacTable.RISCV64 (tables)
open VG.Proof.Variants.MdHash.RISCV64 (variants fns)

def artifacts : List Artifact := [
  Spec.Ecdsa.Rfc6979.Curves.p192SignApi.artifact RISCV64.target {
    tables := [("hmac", tables variants)]
    code := Impl.Ecdsa.Rfc6979.RISCV64.Fn.p192 fns
    verified := Proof.Ecdsa.Rfc6979.RISCV64.P192.sign_scrubbed hasLaw.law }]

end VG.Artifacts.EcdsaP192.RISCV64.Rfc6979

namespace VG.Artifacts.EcdsaP192.RISCV64

open VG.Proof.P192.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P192.verifyHashApi.artifact RISCV64.target {
    code := Impl.Ecdsa.RISCV64.Fn.verifyP192
    verified := Proof.Ecdsa.RISCV64.P192.verifyHash_scrubbed hasLaw.law }] ++
  Rfc6979.artifacts

end VG.Artifacts.EcdsaP192.RISCV64
