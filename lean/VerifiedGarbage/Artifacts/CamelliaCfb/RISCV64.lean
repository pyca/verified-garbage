module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Cfb
public import VerifiedGarbage.Spec.Camellia.CfbFinal
import VerifiedGarbage.Proof.Camellia.RISCV64.Scrub
import VerifiedGarbage.Impl.Camellia.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit
import VerifiedGarbage.Proof.Camellia.RISCV64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia-CFB128 on RISC-V -/

namespace VG.Artifacts.CamelliaCfb.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Camellia.cfbEncryptApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.Fn.cfbEncrypt
    verified := Proof.Camellia.RISCV64.Scrub.cfbEncrypt_scrubbed },
  Spec.Camellia.cfbDecryptApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.Fn.cfbDecrypt
    verified := Proof.Camellia.RISCV64.Scrub.cfbDecrypt_scrubbed },
  Spec.Camellia.cfbEncryptFinalApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.Fn.cfbEncryptFinal
    verified := Proof.Camellia.RISCV64.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Camellia.cfbDecryptFinalApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.Fn.cfbDecryptFinal
    verified := Proof.Camellia.RISCV64.Scrub.cfbDecryptFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.CamelliaCfb.RISCV64
