module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Gcm.Contract
import VerifiedGarbage.Proof.Gcm.RISCV64.Law
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.RISCV64.Lit
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit
import VerifiedGarbage.Proof.Gcm.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.SpecApis


/-! # SM4-GCM (NIST SP 800-38D, RFC 8998) on RISC-V -/

namespace VG.Artifacts.Sm4Gcm.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Sm4.Gcm.initApi.artifact RISCV64.target {
    code := Impl.Sm4Gcm.RISCV64.Fn.init
    verified := Proof.Sm4Gcm.RISCV64.Scrub.init_scrubbed },
  Spec.Sm4.Gcm.sealApi.artifact RISCV64.target {
    code := Impl.Sm4Gcm.RISCV64.Fn.«seal»
    verified := Proof.Sm4Gcm.RISCV64.Scrub.seal_scrubbed },
  Spec.Sm4.Gcm.openApi.artifact RISCV64.target {
    code := Impl.Sm4Gcm.RISCV64.Fn.«open»
    verified := Proof.Sm4Gcm.RISCV64.Scrub.open_scrubbed },
  Spec.Sm4.Gcm.streamInitApi.artifact RISCV64.target {
    code := Impl.Sm4Gcm.RISCV64.Fn.streamInit
    verified := Proof.Sm4Gcm.RISCV64.Scrub.streamInit_scrubbed },
  Spec.Sm4.Gcm.streamAadApi.artifact RISCV64.target {
    code := Impl.Sm4Gcm.RISCV64.Fn.streamAad
    verified := Proof.Sm4Gcm.RISCV64.Scrub.streamAad_scrubbed },
  Spec.Sm4.Gcm.streamEncryptApi.artifact RISCV64.target {
    code := Impl.Sm4Gcm.RISCV64.Fn.streamEncrypt
    verified := Proof.Sm4Gcm.RISCV64.Scrub.streamEncrypt_scrubbed },
  Spec.Sm4.Gcm.streamDecryptApi.artifact RISCV64.target {
    code := Impl.Sm4Gcm.RISCV64.Fn.streamDecrypt
    verified := Proof.Sm4Gcm.RISCV64.Scrub.streamDecrypt_scrubbed },
  Spec.Sm4.Gcm.streamFinishApi.artifact RISCV64.target {
    code := Impl.Sm4Gcm.RISCV64.Fn.streamFinish
    verified := Proof.Sm4Gcm.RISCV64.Scrub.streamFinish_scrubbed },
  Spec.Sm4.Gcm.streamVerifyApi.artifact RISCV64.target {
    code := Impl.Sm4Gcm.RISCV64.Fn.streamVerify
    verified := Proof.Sm4Gcm.RISCV64.Scrub.streamVerify_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Sm4Gcm.RISCV64
