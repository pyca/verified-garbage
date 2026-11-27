module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Spec.Gcm.Bitsliced
public import VerifiedGarbage.Spec.Gcm.Contiguous
import VerifiedGarbage.Proof.Gcm.RISCV64.Law
import VerifiedGarbage.Proof.AesGcm.RISCV64.Bitslice
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamBs
import VerifiedGarbage.Proof.AesGcm.RISCV64.OneBs
import VerifiedGarbage.Proof.AesGcm.RISCV64.OpenBs
import VerifiedGarbage.Proof.AesGcm.RISCV64.OpenToBs
import VerifiedGarbage.Proof.AesGcm.RISCV64.DirectGather.Body
import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.PreparedLaw
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
import VerifiedGarbage.Proof.Gcm.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.SpecApis


/-! # AES-GCM (NIST SP 800-38D) on RISC-V -/

namespace VG.Artifacts.AesGcm.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Gcm.initApi.artifact RISCV64.target {
    code := Impl.AesGcm.RISCV64.Fn.init
    verified := Proof.AesGcm.RISCV64.init_scrubbed },
  Spec.Gcm.streamInitApi.artifact RISCV64.target {
    code := Impl.AesGcm.RISCV64.Fn.streamInit
    verified := Proof.AesGcm.RISCV64.streamInit_scrubbed },
  Spec.Gcm.streamAadApi.artifact RISCV64.target {
    code := Impl.AesGcm.RISCV64.Fn.streamAad
    verified := Proof.AesGcm.RISCV64.streamAad_scrubbed },
  Spec.Gcm.bitsliceApi.artifact RISCV64.target {
    code := Impl.AesGcm.RISCV64.Fn.bitslice
    verified := Proof.AesGcm.RISCV64.Bitslice.bitslice_scrubbed },
  Spec.Gcm.streamEncryptBitslicedApi.artifact RISCV64.target {
    code := Impl.AesGcm.RISCV64.Fn.streamEncryptBs
    verified := Proof.AesGcm.RISCV64.streamEncryptBs_scrubbed },
  Spec.Gcm.streamDecryptBitslicedApi.artifact RISCV64.target {
    code := Impl.AesGcm.RISCV64.Fn.streamDecryptBs
    verified := Proof.AesGcm.RISCV64.streamDecryptBs_scrubbed },
  Spec.Gcm.streamFinishBitslicedApi.artifact RISCV64.target {
    code := Impl.AesGcm.RISCV64.Fn.streamFinishBs
    verified := Proof.AesGcm.RISCV64.streamFinishBs_scrubbed },
  Spec.Gcm.streamVerifyBitslicedApi.artifact RISCV64.target {
    code := Impl.AesGcm.RISCV64.Fn.streamVerifyBs
    verified := Proof.AesGcm.RISCV64.streamVerifyBs_scrubbed },
  Spec.Gcm.sealBitslicedApi.artifact RISCV64.target {
    code := Impl.AesGcm.RISCV64.Fn.sealBs
    verified := Proof.AesGcm.RISCV64.sealBs_scrubbed },
  Spec.Gcm.openBitslicedApi.artifact RISCV64.target {
    code := Impl.AesGcm.RISCV64.Fn.openBs
    verified := Proof.AesGcm.RISCV64.openBs_scrubbed },
  Spec.Gcm.openToBitslicedApi.artifact RISCV64.target {
    code := Impl.AesGcm.RISCV64.Fn.openToBs
    verified := Proof.AesGcm.RISCV64.openToBs_scrubbed },
  Spec.Gcm.sealGatherBitslicedApi.artifact RISCV64.target {
    code := Impl.AesGcm.RISCV64.Fn.sealGatherBs
    verified := Proof.AesGcm.RISCV64.DirectGather.sealGather_scrubbed },
  Spec.Gcm.sealContiguousBitslicedApi.artifact RISCV64.target {
    code := Impl.AesGcm.RISCV64.Contiguous.code
    verified := Proof.AesGcm.RISCV64.Contiguous.scrubbed
      Proof.AesGcm.RISCV64.preparedInvocation_wp }]

spec_apis artifacts

end VG.Artifacts.AesGcm.RISCV64
