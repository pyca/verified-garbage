module

public import VerifiedGarbage.Proof.Bignum.RISCV64.PreVerified
public import VerifiedGarbage.Proof.Bignum.RISCV64.PrivPreVerified
public import VerifiedGarbage.Proof.Rsa.RISCV64.CrtValVerified
public import VerifiedGarbage.Proof.Rsa.RISCV64.IbInverse
public import VerifiedGarbage.Proof.Divstep.TcSBounds
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyChkCkV
public import VerifiedGarbage.Proof.Rsa.RISCV64.RdVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rsa.RISCV64.Scrub
public import VerifiedGarbage.TCB.RISCV64.Print
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved

/-! # RSA (RFC 8017) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Rsa.RISCV64

def artifacts : List Artifact := [
  Spec.Rsa.publicPrecomputeApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.Bignum.RISCV64.Precompute.precompute
    verified := Proof.Bignum.RISCV64.Pre.precompute_verified }
    (Proof.Rsa.RISCV64.Scrub.publicPrecomputeOut 0)),
  Spec.Rsa.privatePrecomputeApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.Bignum.RISCV64.PrivPre.code
    verified := Proof.Bignum.RISCV64.PrivPre.pp_verified }
    (Proof.Rsa.RISCV64.Scrub.privatePrecomputeOut 0)),
  Spec.Rsa.crtValuesApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.Rsa.RISCV64.CrtValues.code
    verified := Proof.Rsa.RISCV64.CrtValues.crtValues_verified }
    (Proof.Rsa.RISCV64.Scrub.crtValuesOut 0)),
  Spec.Rsa.checkKeyApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.Rsa.RISCV64.CheckKey.code
    verified := Proof.Rsa.RISCV64.KeyCheck.ck_verified }
    (Proof.Rsa.RISCV64.Scrub.checkKeyOut 0)),
  Spec.Rsa.recoverPrimesDetApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.Rsa.RISCV64.RecoverDet.code
    verified := Proof.Rsa.RISCV64.RecDet.rd_verified }
    (Proof.Rsa.RISCV64.Scrub.recoverPrimesDetOut 0))]

end VG.Artifacts.Rsa.RISCV64
