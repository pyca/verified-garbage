module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Law
public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Verified
public import VerifiedGarbage.Proof.GcmSiv.Polyval
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
import VerifiedGarbage.Proof.Gcm.RISCV64.Lit

/-! # AES-GCM-SIV (RFC 8452) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesGcmSiv.RISCV64

open VG.Proof.AesGcmSiv.RISCV64

def artifacts : List Artifact := [
  Spec.GcmSiv.sealApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchArgs 3856 0 Impl.AesGcmSiv.RISCV64.«seal»
    stack := 5904
    verified := Proof.AesGcmSiv.seal_keyed (seal_framed Proof.GcmSiv.Polyval.tagInput_eq_tagInputG) },
  Spec.GcmSiv.openApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchArgs 3856 0 Impl.AesGcmSiv.RISCV64.«open»
    stack := 5904
    verified := Proof.AesGcmSiv.open_keyed (open_framed Proof.GcmSiv.Polyval.tagInput_eq_tagInputG) }]

end VG.Artifacts.AesGcmSiv.RISCV64
