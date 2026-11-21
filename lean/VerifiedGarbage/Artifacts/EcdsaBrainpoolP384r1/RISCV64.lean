module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP384r1.SignVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP384r1
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.RISCV64.Ecdsa
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP384r1.VerifyVerified
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP384r1
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP384r1.SignLit
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP384r1.VerifyLit
public import VerifiedGarbage.Proof.BrainpoolP384r1.RISCV64.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP384r1
public import VerifiedGarbage.Proof.Variants.MdHash.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.RISCV64.Fn

/-! # ECDSA over brainpoolP384r1 (FIPS 186-5) on RISC-V -/

@[expose] public section

-- Deterministic ECDSA (RFC 6979) over brainpoolP384r1 on RISC-V, with HMAC as a table
namespace VG.Artifacts.EcdsaBrainpoolP384r1.RISCV64.Rfc6979

open VG.Proof.BrainpoolP384r1.RISCV64 (hasLaw)
open VG.Proof.HmacTable.RISCV64 (tables)
open VG.Proof.Variants.MdHash.RISCV64 (variants fns)

def artifacts : List Artifact := [
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1SignApi.artifact RISCV64.target {
    tables := [("hmac", tables variants)]
    code := Impl.Ecdsa.Rfc6979.RISCV64.Fn.brainpoolp384r1 fns
    verified := .scrubbed (Proof.Ecdsa.Rfc6979.RISCV64.BrainpoolP384r1.sign_scrubbed hasLaw.law) }]

end VG.Artifacts.EcdsaBrainpoolP384r1.RISCV64.Rfc6979

namespace VG.Artifacts.EcdsaBrainpoolP384r1.RISCV64

open VG.Proof.BrainpoolP384r1.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.BrainpoolP384r1.verifyHashApi.artifact RISCV64.target {
    code := Impl.Ecdsa.RISCV64.Fn.verifyBrainpoolP384r1
    verified := .scrubbed (Proof.Ecdsa.RISCV64.BrainpoolP384r1.verifyHash_scrubbed hasLaw.law) }] ++
  Rfc6979.artifacts

end VG.Artifacts.EcdsaBrainpoolP384r1.RISCV64
