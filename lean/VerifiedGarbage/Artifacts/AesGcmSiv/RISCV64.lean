module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.GcmSiv.Contract
import VerifiedGarbage.Proof.Gcm.RISCV64.Law
import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Verified
import VerifiedGarbage.Proof.GcmSiv.Polyval
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
import VerifiedGarbage.Proof.Gcm.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.SpecApis


/-! # AES-GCM-SIV (RFC 8452) on RISC-V -/

namespace VG.Artifacts.AesGcmSiv.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.GcmSiv.sealApi.artifact RISCV64.target {
    code := Impl.AesGcmSiv.RISCV64.Fn.«seal»
    verified :=
      (Proof.AesGcmSiv.RISCV64.Scrub.seal_scrubbed
        Proof.GcmSiv.Polyval.tagInput_eq_tagInputG) },
  Spec.GcmSiv.openApi.artifact RISCV64.target {
    code := Impl.AesGcmSiv.RISCV64.Fn.«open»
    verified :=
      (Proof.AesGcmSiv.RISCV64.Scrub.open_scrubbed
        Proof.GcmSiv.Polyval.tagInput_eq_tagInputG) }]

spec_apis artifacts

end VG.Artifacts.AesGcmSiv.RISCV64
