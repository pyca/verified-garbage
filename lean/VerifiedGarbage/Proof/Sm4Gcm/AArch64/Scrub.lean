module

-- separate module: it imports `GhashImpls`, whose names clash with those `Frame.lean` opens
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Frame
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.AesGcm.AArch64.Scrub
public import VerifiedGarbage.Proof.AesGcm.AArch64.GhashImpls
public import VerifiedGarbage.Proof.AesGcm.AArch64.Verified
public import VerifiedGarbage.Proof.Variants.Sm4Gcm.AArch64
public import VerifiedGarbage.Spec.Sm4.Gcm.Contract
import VerifiedGarbage.Proof.Sm4Gcm.Scratch
import VerifiedGarbage.Proof.Gcm.AArch64.Lit
import VerifiedGarbage.Proof.Sm4.AArch64.Lit
import VerifiedGarbage.Proof.Sm4.AArch64.Ctr32Lit
import VerifiedGarbage.Proof.Framework.Lit

/-! # SM4-GCM on AArch64: returning without secret residue

Untrusted: everything here is checked by Lean. -/

@[expose] public section

/-! ## Without secret residue

The postconditions read the memory on return only within the buffers
(`Proof.Sm4Gcm.*PostOut_local`), and the code of each variant, in its frame,
leaves no secret in the registers it does not clear (`*Side`). -/

namespace VG.Proof.Sm4Gcm.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll

theorem initOk (stack : Nat) (hW : 0 < stack) :
    ScrubAllOk (Spec.Sm4.Gcm.initContract abi stack) stack (Spec.Sm4.Gcm.initSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Sm4.Gcm.initSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Sm4Gcm.initPostOut_local _)

theorem sealOk (stack : Nat) (hW : 0 < stack) :
    ScrubAllOk (Spec.Sm4.Gcm.sealContract abi stack) stack (Spec.Sm4.Gcm.sealSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Sm4.Gcm.sealSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Sm4Gcm.sealPostOut_local _)

theorem openOk (stack : Nat) :
    ScrubAllOk (Spec.Sm4.Gcm.openContract abi stack) stack (Spec.Sm4.Gcm.openSig.retBits abi.ptrBits) :=
  scrubAllOk_args_any (sig := Spec.Sm4.Gcm.openSig) (Proof.Sm4Gcm.openPostOut_local _)

theorem streamEncryptOk (stack : Nat) (hW : 0 < stack) :
    ScrubAllOk (Spec.Sm4.Gcm.streamEncryptContract abi stack) stack (Spec.Sm4.Gcm.streamCryptSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Sm4.Gcm.streamCryptSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Sm4Gcm.streamEncryptPostOut_local _)

theorem streamDecryptOk (stack : Nat) (hW : 0 < stack) :
    ScrubAllOk (Spec.Sm4.Gcm.streamDecryptContract abi stack) stack (Spec.Sm4.Gcm.streamCryptSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Sm4.Gcm.streamCryptSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Sm4Gcm.streamDecryptPostOut_local _)

theorem streamFinishOk (stack : Nat) (hW : 0 < stack) :
    ScrubAllOk (Spec.Sm4.Gcm.streamFinishContract abi stack) stack (Spec.Sm4.Gcm.streamFinishSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Sm4.Gcm.streamFinishSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Sm4Gcm.streamFinishPostOut_local _)

theorem streamVerifyOk (stack : Nat) (hW : 0 < stack) :
    ScrubAllOk (Spec.Sm4.Gcm.streamVerifyContract abi stack) stack (Spec.Sm4.Gcm.streamVerifySig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Sm4.Gcm.streamVerifySig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Sm4Gcm.streamVerifyPostOut_local _)

/-- The stacks of the stream functions and of `init`, of 4032 bytes: their
frames of 768 and their callees'. -/
theorem pos4032 : 0 < 4032 := by decide

/-- `init` of the variant `v` returns without secret residue in its frame. -/
theorem initSide (v : Proof.Sm4Gcm.AArch64.GcmVariant) (hv : v ∈ Proof.Variants.Sm4Gcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch 768 .x2 (Impl.Sm4Gcm.AArch64.init (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
      4032 (Spec.Sm4.Gcm.initSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear [] = true := by
  have h : (Proof.Variants.Sm4Gcm.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratch 768 .x2 (Impl.Sm4Gcm.AArch64.init (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
        4032 (Spec.Sm4.Gcm.initSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear []) = true := by lit_decide
  exact List.all_eq_true.mp h v hv

/-- `seal` of the variant `v` returns without secret residue in its frame. -/
theorem sealSide (v : Proof.Sm4Gcm.AArch64.GcmVariant) (hv : v ∈ Proof.Variants.Sm4Gcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackArgScratch 784 0 (Impl.Sm4Gcm.AArch64.«seal» (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
      4048 (Spec.Sm4.Gcm.sealSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear [] = true := by
  have h : (Proof.Variants.Sm4Gcm.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackArgScratch 784 0 (Impl.Sm4Gcm.AArch64.«seal» (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
        4048 (Spec.Sm4.Gcm.sealSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear []) = true := by lit_decide
  exact List.all_eq_true.mp h v hv

/-- `open` of the variant `v` returns without secret residue in its frame. -/
theorem openSide (v : Proof.Sm4Gcm.AArch64.GcmVariant) (hv : v ∈ Proof.Variants.Sm4Gcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackArgScratch 784 1 (Impl.Sm4Gcm.AArch64.«open» (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
      4048 (Spec.Sm4.Gcm.openSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear [] = true := by
  have h : (Proof.Variants.Sm4Gcm.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackArgScratch 784 1 (Impl.Sm4Gcm.AArch64.«open» (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
        4048 (Spec.Sm4.Gcm.openSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear []) = true := by lit_decide
  exact List.all_eq_true.mp h v hv

/-- `streamEncrypt` of the variant `v` returns without secret residue in its frame. -/
theorem streamEncryptSide (v : Proof.Sm4Gcm.AArch64.GcmVariant) (hv : v ∈ Proof.Variants.Sm4Gcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch 768 .x6 (Impl.Sm4Gcm.AArch64.streamEncrypt (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
      4032 (Spec.Sm4.Gcm.streamCryptSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear [] = true := by
  have h : (Proof.Variants.Sm4Gcm.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratch 768 .x6 (Impl.Sm4Gcm.AArch64.streamEncrypt (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
        4032 (Spec.Sm4.Gcm.streamCryptSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear []) = true := by lit_decide
  exact List.all_eq_true.mp h v hv

/-- `streamDecrypt` of the variant `v` returns without secret residue in its frame. -/
theorem streamDecryptSide (v : Proof.Sm4Gcm.AArch64.GcmVariant) (hv : v ∈ Proof.Variants.Sm4Gcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch 768 .x6 (Impl.Sm4Gcm.AArch64.streamDecrypt (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
      4032 (Spec.Sm4.Gcm.streamCryptSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear [] = true := by
  have h : (Proof.Variants.Sm4Gcm.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratch 768 .x6 (Impl.Sm4Gcm.AArch64.streamDecrypt (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
        4032 (Spec.Sm4.Gcm.streamCryptSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear []) = true := by lit_decide
  exact List.all_eq_true.mp h v hv

/-- `streamFinish` of the variant `v` returns without secret residue in its frame. -/
theorem streamFinishSide (v : Proof.Sm4Gcm.AArch64.GcmVariant) (hv : v ∈ Proof.Variants.Sm4Gcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch 768 .x5 (Impl.Sm4Gcm.AArch64.streamFinish (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
      4032 (Spec.Sm4.Gcm.streamFinishSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear [] = true := by
  have h : (Proof.Variants.Sm4Gcm.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratch 768 .x5 (Impl.Sm4Gcm.AArch64.streamFinish (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
        4032 (Spec.Sm4.Gcm.streamFinishSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear []) = true := by lit_decide
  exact List.all_eq_true.mp h v hv

/-- `streamVerify` of the variant `v` returns without secret residue in its frame. -/
theorem streamVerifySide (v : Proof.Sm4Gcm.AArch64.GcmVariant) (hv : v ∈ Proof.Variants.Sm4Gcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch 768 .x6 (Impl.Sm4Gcm.AArch64.streamVerify (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
      4032 (Spec.Sm4.Gcm.streamVerifySig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear [] = true := by
  have h : (Proof.Variants.Sm4Gcm.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratch 768 .x6 (Impl.Sm4Gcm.AArch64.streamVerify (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
        4032 (Spec.Sm4.Gcm.streamVerifySig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear []) = true := by lit_decide
  exact List.all_eq_true.mp h v hv

/-- `streamInit` of the variant `v` returns without secret residue in its frame. -/
theorem streamInitSide (v : Proof.Sm4Gcm.AArch64.GcmVariant) (hv : v ∈ Proof.Variants.Sm4Gcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch (Proof.AesGcm.AArch64.gcmWn (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩)) .x4 (Impl.AesGcm.AArch64.streamInit (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩).callees))
      (Proof.AesGcm.AArch64.gcmWn (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩)) (Spec.Gcm.streamInitSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear [] = true := by
  have h : (Proof.Variants.Sm4Gcm.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratch (Proof.AesGcm.AArch64.gcmWn (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩)) .x4 (Impl.AesGcm.AArch64.streamInit (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩).callees))
        (Proof.AesGcm.AArch64.gcmWn (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩)) (Spec.Gcm.streamInitSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear []) = true := by lit_decide
  exact List.all_eq_true.mp h v hv

/-- `streamAad` of the variant `v` returns without secret residue in its frame. -/
theorem streamAadSide (v : Proof.Sm4Gcm.AArch64.GcmVariant) (hv : v ∈ Proof.Variants.Sm4Gcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch (Proof.AesGcm.AArch64.gcmWn (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩)) .x5 (Impl.AesGcm.AArch64.streamAad (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩).callees))
      (Proof.AesGcm.AArch64.gcmWn (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩)) (Spec.Gcm.streamAadSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear [] = true := by
  have h : (Proof.Variants.Sm4Gcm.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratch (Proof.AesGcm.AArch64.gcmWn (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩)) .x5 (Impl.AesGcm.AArch64.streamAad (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩).callees))
        (Proof.AesGcm.AArch64.gcmWn (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩)) (Spec.Gcm.streamAadSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear []) = true := by lit_decide
  exact List.all_eq_true.mp h v hv

end VG.Proof.Sm4Gcm.AArch64.Scrub
