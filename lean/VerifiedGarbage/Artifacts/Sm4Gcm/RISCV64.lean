module

public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Verified
public import VerifiedGarbage.Proof.Sm4.RISCV64.Ctr32Verified
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

import VerifiedGarbage.Proof.Sm4.RISCV64.Lit
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit
import VerifiedGarbage.Proof.Gcm.RISCV64.Lit

/-! # SM4-GCM (NIST SP 800-38D, RFC 8998) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sm4Gcm.RISCV64

open VG.Proof.Sm4Gcm.RISCV64

def artifacts : List Artifact := [
  Spec.Sm4.ctr32Api.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.ctr32
    stack := 3232
    verified := Proof.Sm4.RISCV64.Modes.ctr32_verified },
  Spec.Sm4.Gcm.initApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a2 Impl.Sm4Gcm.RISCV64.init
    stack := 5792
    verified := init_framed },
  Spec.Sm4.Gcm.sealApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchArgs 2576 0 Impl.Sm4Gcm.RISCV64.«seal»
    stack := 5808
    verified := seal_framed },
  Spec.Sm4.Gcm.openApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchArgs 2576 1 Impl.Sm4Gcm.RISCV64.«open»
    stack := 5808
    verified := open_framed },
  Spec.Sm4.Gcm.streamInitApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a4 Impl.AesGcm.RISCV64.streamInit
    stack := 4608
    verified := Proof.AesGcm.RISCV64.streamInit_framed },
  Spec.Sm4.Gcm.streamAadApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a5 Impl.AesGcm.RISCV64.streamAad
    stack := 4608
    verified := Proof.AesGcm.RISCV64.streamAad_framed },
  Spec.Sm4.Gcm.streamEncryptApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a6 Impl.Sm4Gcm.RISCV64.streamEncrypt
    stack := 5792
    verified := streamEncrypt_framed },
  Spec.Sm4.Gcm.streamDecryptApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a6 Impl.Sm4Gcm.RISCV64.streamDecrypt
    stack := 5792
    verified := streamDecrypt_framed },
  Spec.Sm4.Gcm.streamFinishApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a5 Impl.Sm4Gcm.RISCV64.streamFinish
    stack := 5792
    verified := streamFinish_framed },
  Spec.Sm4.Gcm.streamVerifyApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a6 Impl.Sm4Gcm.RISCV64.streamVerify
    stack := 5792
    verified := streamVerify_framed }]

end VG.Artifacts.Sm4Gcm.RISCV64
