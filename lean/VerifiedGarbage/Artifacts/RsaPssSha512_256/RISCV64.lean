module

public import VerifiedGarbage.Proof.RsaPss.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSASSA-PSS with SHA-512/256 on RISC-V: verification -/

@[expose] public section

namespace VG.Artifacts.RsaPssSha512_256.RISCV64

def artifacts : List Artifact := [
  (Spec.RsaPss.verifyPrecomputedApi Spec.Mgf1.sha512_256 Spec.Mgf1.sha512_256).artifact RISCV64.target {
    code := Impl.RsaPss.RISCV64.verifyPrecomputed Proof.Hmac.Stream.RISCV64.Sha512_256.hash
    stack := 336
    verified := Proof.RsaPss.RISCV64.link_verified Proof.RsaPss.RISCV64.sha512_256L }]

end VG.Artifacts.RsaPssSha512_256.RISCV64
