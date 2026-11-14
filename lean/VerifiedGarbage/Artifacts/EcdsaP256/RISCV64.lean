module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Sign
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.SignVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyComb
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.VerifyVerified
public import VerifiedGarbage.Spec.Ecdsa.Verify.P256
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.SignLit
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.VerifyLit
public import VerifiedGarbage.Proof.P256.RISCV64.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.P256
public import VerifiedGarbage.Proof.Variants.MdHash.RISCV64

/-! # ECDSA over P-256 (FIPS 186-5) on RISC-V -/

@[expose] public section

-- Deterministic ECDSA (RFC 6979) over P-256 on RISC-V, with HMAC as a table
namespace VG.Artifacts.EcdsaP256.RISCV64.Rfc6979

open VG.Proof.P256.RISCV64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.RISCV64 (signCodeT stackT OK)
open VG.Proof.Ecdsa.Rfc6979.RISCV64.P256 (curveT verifiedT)
open VG.Proof.HmacTable.RISCV64 (tables names)

def artifactsFor (vs : List Proof.HmacTable.RISCV64.HVar) : List Artifact :=
  if hv : OK vs ∧ Impl.Ecdsa.RISCV64.Comb.p256Sym ∉ names vs then [
    Spec.Ecdsa.Rfc6979.Curves.p256SignApi.artifact RISCV64.target {
      tables := [("hmac", tables vs)]
      code := signCodeT (curveT hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.p256.tries vs
      stack := stackT
      verified := verifiedT hasLaw.law vs hv }]
  else []

def artifacts : List Artifact :=
  artifactsFor VG.Proof.Variants.MdHash.RISCV64.variants

end VG.Artifacts.EcdsaP256.RISCV64.Rfc6979

namespace VG.Artifacts.EcdsaP256.RISCV64

open VG.Proof.P256.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P256.verifyHashApi.artifact RISCV64.target {
    code := Impl.Ecdsa.RISCV64.VerifyHash.verifyHash Spec.Ecdsa.P256.inst.curve.len false
      Impl.Ecdsa.RISCV64.VerifyComb.verifyP256
    stack := 80
    verified := Proof.Ecdsa.RISCV64.P256.verifyHash_verified hasLaw.law }] ++
  Rfc6979.artifacts

end VG.Artifacts.EcdsaP256.RISCV64
