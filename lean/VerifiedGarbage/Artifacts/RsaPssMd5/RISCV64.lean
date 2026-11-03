module

public import VerifiedGarbage.Proof.RsaPss.RISCV64.Verified
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Sg.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSASSA-PSS with MD5 on RISC-V: verification and signing -/

@[expose] public section

namespace VG.Artifacts.RsaPssMd5.RISCV64

def artifacts : List Artifact := [
  (Spec.RsaPss.verifyPrecomputedApi Spec.Mgf1.md5 Spec.Mgf1.md5).artifact RISCV64.target {
    code := Impl.RsaPss.RISCV64.verifyPrecomputed Proof.Hmac.Stream.RISCV64.Md5.hash
    stack := 336
    verified := Proof.RsaPss.RISCV64.link_verified Proof.RsaPss.RISCV64.md5L },
  (Spec.RsaPss.signApi Spec.Mgf1.md5 Spec.Mgf1.md5).artifact RISCV64.target {
    code := Impl.RsaPss.RISCV64.Sign.sign Proof.Hmac.Stream.RISCV64.Md5.hash
    stack := 3472
    verified := Proof.RsaPss.RISCV64.Sg.sign_link_verified Proof.RsaPss.RISCV64.md5L }]

end VG.Artifacts.RsaPssMd5.RISCV64
