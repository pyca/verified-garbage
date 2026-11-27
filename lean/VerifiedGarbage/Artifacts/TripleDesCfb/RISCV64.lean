module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Cfb
public import VerifiedGarbage.Spec.TripleDes.CfbFinal
import VerifiedGarbage.Proof.TripleDes.RISCV64.Scrub
import VerifiedGarbage.Impl.TripleDes.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit
import VerifiedGarbage.Proof.TripleDes.RISCV64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES-CFB64 on RISC-V -/

namespace VG.Artifacts.TripleDesCfb.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.TripleDes.cfbEncryptApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Fn.cfbEncrypt
    verified := Proof.TripleDes.RISCV64.Scrub.cfbEncrypt_scrubbed },
  Spec.TripleDes.cfbDecryptApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Fn.cfbDecrypt
    verified := Proof.TripleDes.RISCV64.Scrub.cfbDecrypt_scrubbed },
  Spec.TripleDes.cfbEncryptFinalApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Fn.cfbEncryptFinal
    verified := Proof.TripleDes.RISCV64.Scrub.cfbEncryptFinal_scrubbed },
  Spec.TripleDes.cfbDecryptFinalApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Fn.cfbDecryptFinal
    verified := Proof.TripleDes.RISCV64.Scrub.cfbDecryptFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.TripleDesCfb.RISCV64
