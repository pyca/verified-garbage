module

public import VerifiedGarbage.Proof.RsaPss.RISCV64.Verified
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Sg.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSASSA-PSS with SHA-224 on RISC-V: verification and signing -/

@[expose] public section

namespace VG.Artifacts.RsaPssSha224.RISCV64

def artifacts : List Artifact := [
  (Spec.RsaPss.verifyPrecomputedApi Spec.Mgf1.sha224 Spec.Mgf1.sha224).artifact RISCV64.target {
    code := Impl.RsaPss.RISCV64.verifyPrecomputed Proof.Hmac.Stream.RISCV64.Sha256Family.hash224
    stack := 336
    verified := Proof.RsaPss.RISCV64.link_verified Proof.RsaPss.RISCV64.sha224L },
  (Spec.RsaPss.signApi Spec.Mgf1.sha224 Spec.Mgf1.sha224).artifact RISCV64.target {
    code := Impl.RsaPss.RISCV64.Sign.sign Proof.Hmac.Stream.RISCV64.Sha256Family.hash224
    stack := 3472
    verified := Proof.RsaPss.RISCV64.Sg.sign_link_verified Proof.RsaPss.RISCV64.sha224L }]

end VG.Artifacts.RsaPssSha224.RISCV64
