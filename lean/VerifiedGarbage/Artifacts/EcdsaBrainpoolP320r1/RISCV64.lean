module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP320r1.SignVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP320r1
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.RISCV64.Ecdsa
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP320r1.VerifyVerified
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP320r1
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP320r1.SignLit
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP320r1.VerifyLit
public import VerifiedGarbage.Proof.BrainpoolP320r1.RISCV64.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP320r1
public import VerifiedGarbage.Proof.Variants.MdHash.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.RISCV64.Fn

/-! # ECDSA over brainpoolP320r1 (FIPS 186-5) on RISC-V -/

@[expose] public section

-- Deterministic ECDSA (RFC 6979) over brainpoolP320r1 on RISC-V, with HMAC as a table
namespace VG.Artifacts.EcdsaBrainpoolP320r1.RISCV64.Rfc6979

open VG.Proof.BrainpoolP320r1.RISCV64 (hasLaw)
open VG.Proof.HmacTable.RISCV64 (tables)
open VG.Proof.Variants.MdHash.RISCV64 (variants fns)

def artifacts : List Artifact := [
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp320r1SignApi.artifact RISCV64.target {
    tables := [("hmac", tables variants)]
    code := Impl.Ecdsa.Rfc6979.RISCV64.Fn.brainpoolp320r1 fns
    verified := Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP320r1.sign_scrubbed hasLaw.law }]

end VG.Artifacts.EcdsaBrainpoolP320r1.RISCV64.Rfc6979

namespace VG.Artifacts.EcdsaBrainpoolP320r1.RISCV64

open VG.Proof.BrainpoolP320r1.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.BrainpoolP320r1.verifyHashApi.artifact RISCV64.target {
    code := Impl.Ecdsa.RISCV64.Fn.verifyBrainpoolP320r1
    verified := Proof.Ecdsa.RISCV64.BrainpoolP320r1.verifyHash_scrubbed hasLaw.law }] ++
  Rfc6979.artifacts

end VG.Artifacts.EcdsaBrainpoolP320r1.RISCV64
