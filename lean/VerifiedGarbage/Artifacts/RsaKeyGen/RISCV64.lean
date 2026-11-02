module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSA key generation (FIPS 186-5 A.1.3) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.RsaKeyGen.RISCV64

def artifacts : List Artifact := [
  Spec.RsaKeyGen.keyApi.artifact RISCV64.target {
    code := Impl.RsaKeyGen.RISCV64.Key.code
    verified := Proof.RsaKeyGen.RISCV64.Key.key_verified }]

end VG.Artifacts.RsaKeyGen.RISCV64
