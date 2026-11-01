module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.CheckVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.CheckLit

/-! # The check of a public point on RISC-V -/

@[expose] public section

namespace VG.Artifacts.WeierstrassCheckPoint.RISCV64

def artifacts : List Artifact := [
  Spec.Weierstrass.CheckPoint.p256.checkApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.checkP256
    verified := Proof.Ecdh.RISCV64.P256.check_verified }]

end VG.Artifacts.WeierstrassCheckPoint.RISCV64
