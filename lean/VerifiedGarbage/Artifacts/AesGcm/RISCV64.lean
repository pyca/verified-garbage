module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Law
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Bitslice
public import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamBs
public import VerifiedGarbage.Proof.AesGcm.RISCV64.OneBs
public import VerifiedGarbage.Proof.AesGcm.RISCV64.OpenBs
public import VerifiedGarbage.Proof.AesGcm.RISCV64.OpenToBs
public import VerifiedGarbage.Proof.AesGcm.RISCV64.GatherBs
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
import VerifiedGarbage.Proof.Gcm.RISCV64.Lit

/-! # AES-GCM (NIST SP 800-38D) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesGcm.RISCV64

open VG.Proof.AesGcm.RISCV64

def artifacts : List Artifact := [
  Spec.Gcm.initApi.artifact RISCV64.target {
    code := Impl.AesGcm.RISCV64.Fn.init
    verified := .scrubbed init_scrubbed },
  Spec.Gcm.streamInitApi.artifact RISCV64.target {
    code := Impl.AesGcm.RISCV64.Fn.streamInit
    verified := .scrubbed streamInit_scrubbed },
  Spec.Gcm.streamAadApi.artifact RISCV64.target {
    code := Impl.AesGcm.RISCV64.Fn.streamAad
    verified := .scrubbed streamAad_scrubbed },
  Spec.Gcm.bitsliceApi.artifact RISCV64.target {
    code := Impl.AesGcm.RISCV64.Fn.bitslice
    verified := .scrubbed Bitslice.bitslice_scrubbed },
  Spec.Gcm.streamEncryptBitslicedApi.artifact RISCV64.target {
    code := Impl.AesGcm.RISCV64.Fn.streamEncryptBs
    verified := .scrubbed streamEncryptBs_scrubbed },
  Spec.Gcm.streamDecryptBitslicedApi.artifact RISCV64.target {
    code := Impl.AesGcm.RISCV64.Fn.streamDecryptBs
    verified := .scrubbed streamDecryptBs_scrubbed },
  Spec.Gcm.streamFinishBitslicedApi.artifact RISCV64.target {
    code := Impl.AesGcm.RISCV64.Fn.streamFinishBs
    verified := .scrubbed streamFinishBs_scrubbed },
  Spec.Gcm.streamVerifyBitslicedApi.artifact RISCV64.target {
    code := Impl.AesGcm.RISCV64.Fn.streamVerifyBs
    verified := .scrubbed streamVerifyBs_scrubbed },
  Spec.Gcm.sealBitslicedApi.artifact RISCV64.target {
    code := Impl.AesGcm.RISCV64.Fn.sealBs
    verified := .scrubbed sealBs_scrubbed },
  Spec.Gcm.openBitslicedApi.artifact RISCV64.target {
    code := Impl.AesGcm.RISCV64.Fn.openBs
    verified := .scrubbed openBs_scrubbed },
  Spec.Gcm.openToBitslicedApi.artifact RISCV64.target {
    code := Impl.AesGcm.RISCV64.Fn.openToBs
    verified := .scrubbed openToBs_scrubbed },
  Spec.Gcm.sealGatherBitslicedApi.artifact RISCV64.target {
    code := Impl.AesGcm.RISCV64.Fn.sealGatherBs
    verified := .scrubbed GatherBs.sealGatherBs_scrubbed }]

end VG.Artifacts.AesGcm.RISCV64
