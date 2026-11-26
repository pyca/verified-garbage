module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blowfish.Cfb
public import VerifiedGarbage.Spec.Blowfish.CfbFinal
import VerifiedGarbage.Proof.Blowfish.RISCV64.Scrub
import VerifiedGarbage.Impl.Blowfish.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blowfish.RISCV64.ModesLit
import VerifiedGarbage.Proof.Blowfish.RISCV64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Blowfish-CFB64 on RISC-V -/

namespace VG.Artifacts.BlowfishCfb.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Blowfish.cfbEncryptApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.Fn.cfbEncrypt
    verified := Proof.Blowfish.RISCV64.Scrub.cfbEncrypt_scrubbed },
  Spec.Blowfish.cfbDecryptApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.Fn.cfbDecrypt
    verified := Proof.Blowfish.RISCV64.Scrub.cfbDecrypt_scrubbed },
  Spec.Blowfish.cfbEncryptFinalApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.Fn.cfbEncryptFinal
    verified := Proof.Blowfish.RISCV64.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Blowfish.cfbDecryptFinalApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.Fn.cfbDecryptFinal
    verified := Proof.Blowfish.RISCV64.Scrub.cfbDecryptFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.BlowfishCfb.RISCV64
