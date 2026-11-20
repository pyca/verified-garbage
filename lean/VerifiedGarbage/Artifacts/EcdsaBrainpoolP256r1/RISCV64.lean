module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP256r1.SignVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP256r1
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.RISCV64.Ecdsa
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP256r1.VerifyVerified
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP256r1
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP256r1.SignLit
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP256r1.VerifyLit
public import VerifiedGarbage.Proof.BrainpoolP256r1.RISCV64.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP256r1
public import VerifiedGarbage.Proof.Variants.MdHash.RISCV64

/-! # ECDSA over brainpoolP256r1 (FIPS 186-5) on RISC-V -/

@[expose] public section

-- Deterministic ECDSA (RFC 6979) over brainpoolP256r1 on RISC-V, with HMAC as a table
namespace VG.Artifacts.EcdsaBrainpoolP256r1.RISCV64.Rfc6979

open VG.Proof.BrainpoolP256r1.RISCV64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.RISCV64 (signCodeT OK)
open VG.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP256r1 (curveT verifiedT)
open VG.Proof.HmacTable.RISCV64 (tables names)

def artifacts : List Artifact :=
  if hv : OK VG.Proof.Variants.MdHash.RISCV64.variants ∧ Impl.Ecdsa.RISCV64.Comb.brainpoolP256r1Sym ∉ names VG.Proof.Variants.MdHash.RISCV64.variants then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1SignApi.artifact RISCV64.target (Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP256r1.signReg hasLaw.law hv)]
  else []

end VG.Artifacts.EcdsaBrainpoolP256r1.RISCV64.Rfc6979

namespace VG.Artifacts.EcdsaBrainpoolP256r1.RISCV64

open VG.Proof.BrainpoolP256r1.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.BrainpoolP256r1.verifyHashApi.artifact RISCV64.target {
    code := Impl.Ecdsa.RISCV64.Fn.verifyBrainpoolP256r1
    verified := .scrubbed (Proof.Ecdsa.RISCV64.BrainpoolP256r1.verifyHash_scrubbed hasLaw.law) }] ++
  Rfc6979.artifacts

end VG.Artifacts.EcdsaBrainpoolP256r1.RISCV64
