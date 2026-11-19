module

public import VerifiedGarbage.Spec.Ctr.Final
public import VerifiedGarbage.Spec.Ofb.Final
public import VerifiedGarbage.Spec.Cfb.Final
public import VerifiedGarbage.Spec.Cfb8.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Variants.AesBlocks.AArch64
public import VerifiedGarbage.Proof.Variants.AesCtr32.AArch64
public import VerifiedGarbage.Proof.AesCfb.AArch64.Final
public import VerifiedGarbage.Impl.AesCfb.AArch64
public import VerifiedGarbage.Impl.AesCfb8.AArch64
public import VerifiedGarbage.Impl.AesOfb.AArch64
public import VerifiedGarbage.Impl.AesOfb.AArch64.Final
public import VerifiedGarbage.Impl.AesCtr.AArch64
public import VerifiedGarbage.Impl.AesCtr.AArch64.Final
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.AesEcb.Wipe
import VerifiedGarbage.Proof.AesCbc.Wipe
public import VerifiedGarbage.Spec.Ctr.Contract
public import VerifiedGarbage.Spec.Ofb.Contract
public import VerifiedGarbage.Spec.Cfb.Contract

/-!
# AES's streaming modes on AArch64, without secret residue

The postconditions of `vg_aes_ctr_final`, `vg_aes_ofb_final`,
`vg_aes_cfb128_encrypt_final`, `vg_aes_cfb128_decrypt_final`,
`vg_aes_cfb8_encrypt` and `vg_aes_cfb8_decrypt` read the memory on return
only within the block at `iv` (or `ctr`) and the data
(`ScrubAll.ScrubAllOk`): each implementation, generic over the AES
implementation it calls, returns with every register it may leave secret
cleared, and its whole stack zeroed, if it has one (`ScrubAll.scrubAllOf`,
with the `…Own` registers and `…Side` theorems below; CFB128's decryption,
whose own code differs with the implementation, by `ScrubAll.withScrubAll`
and `withScrubAllW` still).

So do the whole-block functions of CTR, OFB and CFB128, `vg_aes_ctr`,
`vg_aes_ofb`, `vg_aes_cfb128_encrypt` and `vg_aes_cfb128_decrypt`, which
have no frames: each returns with the registers it may write cleared. The
final functions call the code as it was, an internal function of its own
(`vg_aes_ctr_core`, …), whose registers they clear themselves.
-/

@[expose] public section

namespace VG.Proof.Aes.AArch64.ModesScrub

open VG.AArch64 VG.AArch64.ScrubAll
open VG.Proof.AesEcb (agree_of bytesAt_congr)

theorem ctrFinalOk : ScrubAllOk (Spec.Ctr.aesFinalContract abi 80) 80 (Spec.Ctr.aesFinalSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Ctr.aesFinalSig) (by decide) (W := 80) (by decide) (Nat.le_refl _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [_, _, _, _, n, _], _ =>
      simp only [Spec.Ctr.aesFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk
      have h' := h key hk
      dsimp only [ArgWord.ofRaw, Spec.Ctr.CryptFinal] at h' ⊢
      have hd := agree_of hb.2.2.1
      rw [bytesAt_congr fun i hi => hd i (by have := AesEcb.n_le (pb := abi.ptrBits) n; omega_using [hi, this]), bytesAt_congr (agree_of hb.2.1)]
      exact h'

theorem ofbFinalOk : ScrubAllOk (Spec.Ofb.aesFinalContract abi 64) 64 (Spec.Ofb.aesFinalSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Ofb.aesFinalSig) (by decide) (W := 64) (by decide) (Nat.le_refl _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [_, _, _, _, n, _], _ =>
      simp only [Spec.Ofb.aesFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk
      have h' := h key hk
      dsimp only [ArgWord.ofRaw, Spec.Ofb.CryptFinal] at h' ⊢
      have hd := agree_of hb.2.2.1
      rw [bytesAt_congr fun i hi => hd i (by have := AesEcb.n_le (pb := abi.ptrBits) n; omega_using [hi, this]), bytesAt_congr (agree_of hb.2.1)]
      exact h'

theorem cfbEncryptFinalOk : ScrubAllOk (Spec.Cfb.aesEncryptFinalContract abi 64) 64 (Spec.Cfb.aesFinalSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Cfb.aesFinalSig) (by decide) (W := 64) (by decide) (Nat.le_refl _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [_, _, _, _, n, _], _ =>
      simp only [Spec.Cfb.aesFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk
      have h' := h key hk
      dsimp only [ArgWord.ofRaw, Spec.Cfb.EncryptFinal] at h' ⊢
      have hd := agree_of hb.2.2.1
      rw [bytesAt_congr fun i hi => hd i (by have := AesEcb.n_le (pb := abi.ptrBits) n; omega_using [hi, this]), bytesAt_congr (agree_of hb.2.1)]
      exact h'

theorem cfbDecryptFinalOk : ScrubAllOk (Spec.Cfb.aesDecryptFinalContract abi 64) 64 (Spec.Cfb.aesFinalSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Cfb.aesFinalSig) (by decide) (W := 64) (by decide) (Nat.le_refl _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [_, _, _, _, n, _], _ =>
      simp only [Spec.Cfb.aesFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk
      have h' := h key hk
      dsimp only [ArgWord.ofRaw, Spec.Cfb.DecryptFinal] at h' ⊢
      have hd := agree_of hb.2.2.1
      rw [bytesAt_congr fun i hi => hd i (by have := AesEcb.n_le (pb := abi.ptrBits) n; omega_using [hi, this]), bytesAt_congr (agree_of hb.2.1)]
      exact h'

theorem cfb8EncryptOk : ScrubAllOk (Spec.Cfb8.aesEncryptContract abi 0) 0 (Spec.Cfb8.aesSig.retBits abi.ptrBits) :=
  scrubAllOk_regs0 (sig := Spec.Cfb8.aesSig) (by decide) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [_, _, _, _, n, _], _ =>
      simp only [Spec.Cfb8.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk
      have h' := h key hk
      dsimp only [ArgWord.ofRaw] at h' ⊢
      have hd := agree_of hb.2.2.1
      rw [bytesAt_congr fun i hi => hd i (by have := AesEcb.n_le (pb := abi.ptrBits) n; omega_using [hi, this]), bytesAt_congr (agree_of hb.2.1)]
      exact h'

theorem cfb8DecryptOk : ScrubAllOk (Spec.Cfb8.aesDecryptContract abi 0) 0 (Spec.Cfb8.aesSig.retBits abi.ptrBits) :=
  scrubAllOk_regs0 (sig := Spec.Cfb8.aesSig) (by decide) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [_, _, _, _, n, _], _ =>
      simp only [Spec.Cfb8.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk
      have h' := h key hk
      dsimp only [ArgWord.ofRaw] at h' ⊢
      have hd := agree_of hb.2.2.1
      rw [bytesAt_congr fun i hi => hd i (by have := AesEcb.n_le (pb := abi.ptrBits) n; omega_using [hi, this]), bytesAt_congr (agree_of hb.2.1)]
      exact h'

theorem ctrOk : ScrubAllOk (Spec.Ctr.aesContract abi) 0 (Spec.Ctr.aesSig.retBits abi.ptrBits) :=
  scrubAllOk_regs0 (sig := Spec.Ctr.aesSig) (by decide) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [_, _, _, _, n, _], _ =>
      simp only [Spec.Ctr.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk
      have h' := h key hk
      dsimp only [ArgWord.ofRaw] at h' ⊢
      have hd := agree_of hb.2.2.1
      rw [AesCbc.Wipe.blocksAt_congr fun i hi => hd i (by have := AesEcb.n_le (pb := abi.ptrBits) n; omega_using [hi, this]),
        bytesAt_congr (agree_of hb.2.1)]
      exact h'

theorem ofbOk : ScrubAllOk (Spec.Ofb.aesContract abi) 0 (Spec.Ofb.aesSig.retBits abi.ptrBits) :=
  scrubAllOk_regs0 (sig := Spec.Ofb.aesSig) (by decide) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [_, _, _, _, n, _], _ =>
      simp only [Spec.Ofb.aesSig, Spec.Cbc.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk
      have h' := h key hk
      dsimp only [ArgWord.ofRaw] at h' ⊢
      have hd := agree_of hb.2.2.1
      rw [AesCbc.Wipe.blocksAt_congr fun i hi => hd i (by have := AesEcb.n_le (pb := abi.ptrBits) n; omega_using [hi, this]),
        bytesAt_congr (agree_of hb.2.1)]
      exact h'

theorem cfbEncryptOk : ScrubAllOk (Spec.Cfb.aesEncryptContract abi) 0 (Spec.Cfb.aesSig.retBits abi.ptrBits) :=
  scrubAllOk_regs0 (sig := Spec.Cfb.aesSig) (by decide) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [_, _, _, _, n, _], _ =>
      simp only [Spec.Cfb.aesSig, Spec.Cbc.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk
      have h' := h key hk
      dsimp only [ArgWord.ofRaw] at h' ⊢
      have hd := agree_of hb.2.2.1
      rw [AesCbc.Wipe.blocksAt_congr fun i hi => hd i (by have := AesEcb.n_le (pb := abi.ptrBits) n; omega_using [hi, this]),
        bytesAt_congr (agree_of hb.2.1)]
      exact h'

theorem cfbDecryptOk : ScrubAllOk (Spec.Cfb.aesDecryptContract abi) 0 (Spec.Cfb.aesSig.retBits abi.ptrBits) :=
  scrubAllOk_regs0 (sig := Spec.Cfb.aesSig) (by decide) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [_, _, _, _, n, _], _ =>
      simp only [Spec.Cfb.aesSig, Spec.Cbc.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk
      have h' := h key hk
      dsimp only [ArgWord.ofRaw] at h' ⊢
      have hd := agree_of hb.2.2.1
      rw [AesCbc.Wipe.blocksAt_congr fun i hi => hd i (by have := AesEcb.n_le (pb := abi.ptrBits) n; omega_using [hi, this]),
        bytesAt_congr (agree_of hb.2.1)]
      exact h'

/-! ## What the tails clear

Each function's tail clears the registers its own code writes with those its
block or counter function writes (`BlocksImpl.encClear`, `Ctr32Impl.clear`);
`scrubAllOf` needs `scrubSide` of each, evaluated here with each variant. -/

/-- The registers `vg_aes_cfb128_encrypt` writes itself. -/
def cfbEncryptOwn : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x6, .x9, .x10, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
    .v26, .v27, .v28, .v29, .v30],
   []⟩

/-- Of `vg_aes_cfb128_encrypt`. -/
theorem cfbEncryptSide (v : Proof.Aes.AArch64.BlocksImpl) (hv : v ∈ Proof.Variants.AesBlocks.AArch64.variants) :
    scrubSide (Impl.AesCfb.AArch64.encrypt v.enc) 0
      (Spec.Cfb.aesSig.retBits abi.ptrBits) (clearUnion cfbEncryptOwn v.encClear) [] = true := by
  have e : (Proof.Variants.AesBlocks.AArch64.variants.all fun v =>
      scrubSide (Impl.AesCfb.AArch64.encrypt v.enc) 0
        (Spec.Cfb.aesSig.retBits abi.ptrBits) (clearUnion cfbEncryptOwn v.encClear) []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

/-- The registers `vg_aes_cfb128_encrypt_final` writes itself. -/
def cfbEncryptFinalOwn : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x6, .x7, .x9, .x10, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
    .v26, .v27, .v28, .v29, .v30],
   []⟩

/-- Of `vg_aes_cfb128_encrypt_final`. -/
theorem cfbEncryptFinalSide (v : Proof.Aes.AArch64.BlocksImpl) (hv : v ∈ Proof.Variants.AesBlocks.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratchWiped 64 .x6 8 (Proof.AesCfb.AArch64.Final.encryptCode v)) 64
      (Spec.Cfb.aesFinalSig.retBits abi.ptrBits) (clearUnion cfbEncryptFinalOwn v.encClear) [] = true := by
  have e : (Proof.Variants.AesBlocks.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratchWiped 64 .x6 8 (Proof.AesCfb.AArch64.Final.encryptCode v)) 64
        (Spec.Cfb.aesFinalSig.retBits abi.ptrBits) (clearUnion cfbEncryptFinalOwn v.encClear) []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

/-- The registers `vg_aes_cfb8_encrypt` writes itself. -/
def cfb8EncryptOwn : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x6, .x9, .x10, .x11, .x12, .x13, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
    .v26, .v27, .v28, .v29, .v30],
   []⟩

/-- Of `vg_aes_cfb8_encrypt`. -/
theorem cfb8EncryptSide (v : Proof.Aes.AArch64.BlocksImpl) (hv : v ∈ Proof.Variants.AesBlocks.AArch64.variants) :
    scrubSide (Impl.AesCfb8.AArch64.encrypt v.enc) 0
      (Spec.Cfb8.aesSig.retBits abi.ptrBits) (clearUnion cfb8EncryptOwn v.encClear) [] = true := by
  have e : (Proof.Variants.AesBlocks.AArch64.variants.all fun v =>
      scrubSide (Impl.AesCfb8.AArch64.encrypt v.enc) 0
        (Spec.Cfb8.aesSig.retBits abi.ptrBits) (clearUnion cfb8EncryptOwn v.encClear) []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

/-- The registers `vg_aes_cfb8_decrypt` writes itself. -/
def cfb8DecryptOwn : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x6, .x9, .x10, .x11, .x12, .x13, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
    .v26, .v27, .v28, .v29, .v30],
   []⟩

/-- Of `vg_aes_cfb8_decrypt`. -/
theorem cfb8DecryptSide (v : Proof.Aes.AArch64.BlocksImpl) (hv : v ∈ Proof.Variants.AesBlocks.AArch64.variants) :
    scrubSide (Impl.AesCfb8.AArch64.decrypt v.enc) 0
      (Spec.Cfb8.aesSig.retBits abi.ptrBits) (clearUnion cfb8DecryptOwn v.encClear) [] = true := by
  have e : (Proof.Variants.AesBlocks.AArch64.variants.all fun v =>
      scrubSide (Impl.AesCfb8.AArch64.decrypt v.enc) 0
        (Spec.Cfb8.aesSig.retBits abi.ptrBits) (clearUnion cfb8DecryptOwn v.encClear) []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

/-- The registers `vg_aes_ofb` writes itself. -/
def ofbOwn : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x6, .x9, .x10, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
    .v26, .v27, .v28, .v29, .v30],
   []⟩

/-- Of `vg_aes_ofb`. -/
theorem ofbSide (v : Proof.Aes.AArch64.BlocksImpl) (hv : v ∈ Proof.Variants.AesBlocks.AArch64.variants) :
    scrubSide (Impl.AesOfb.AArch64.crypt v.enc) 0
      (Spec.Ofb.aesSig.retBits abi.ptrBits) (clearUnion ofbOwn v.encClear) [] = true := by
  have e : (Proof.Variants.AesBlocks.AArch64.variants.all fun v =>
      scrubSide (Impl.AesOfb.AArch64.crypt v.enc) 0
        (Spec.Ofb.aesSig.retBits abi.ptrBits) (clearUnion ofbOwn v.encClear) []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

/-- The registers `vg_aes_ofb_final` writes itself. -/
def ofbFinalOwn : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x6, .x7, .x9, .x10, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
    .v26, .v27, .v28, .v29, .v30],
   []⟩

/-- Of `vg_aes_ofb_final`. -/
theorem ofbFinalSide (v : Proof.Aes.AArch64.BlocksImpl) (hv : v ∈ Proof.Variants.AesBlocks.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratchWiped 64 .x6 8 (Impl.AesOfb.AArch64.cryptFinal v.enc v.suffix)) 64
      (Spec.Ofb.aesFinalSig.retBits abi.ptrBits) (clearUnion ofbFinalOwn v.encClear) [] = true := by
  have e : (Proof.Variants.AesBlocks.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratchWiped 64 .x6 8 (Impl.AesOfb.AArch64.cryptFinal v.enc v.suffix)) 64
        (Spec.Ofb.aesFinalSig.retBits abi.ptrBits) (clearUnion ofbFinalOwn v.encClear) []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

/-- The registers `vg_aes_ctr` writes itself. -/
def ctrOwn : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x9, .x10, .x11, .x12, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
    .v26, .v27, .v28, .v29, .v30, .v31],
   []⟩

/-- Of `vg_aes_ctr`. -/
theorem ctrSide (v : Proof.Aes.AArch64.Ctr32Impl) (hv : v ∈ Proof.Variants.AesCtr32.AArch64.variants) :
    scrubSide (Impl.AesCtr.AArch64.crypt v.callee) 0
      (Spec.Ctr.aesSig.retBits abi.ptrBits) (clearUnion ctrOwn v.clear) [] = true := by
  have e : (Proof.Variants.AesCtr32.AArch64.variants.all fun v =>
      scrubSide (Impl.AesCtr.AArch64.crypt v.callee) 0
        (Spec.Ctr.aesSig.retBits abi.ptrBits) (clearUnion ctrOwn v.clear) []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

/-- The registers `vg_aes_ctr_final` writes itself. -/
def ctrFinalOwn : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x9, .x10, .x11, .x12, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
    .v26, .v27, .v28, .v29, .v30, .v31],
   []⟩

/-- Of `vg_aes_ctr_final`. -/
theorem ctrFinalSide (v : Proof.Aes.AArch64.Ctr32Impl) (hv : v ∈ Proof.Variants.AesCtr32.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratchWiped 80 .x6 10
        (Impl.AesCtr.AArch64.cryptFinal v.callee v.suffix)) 80
      (Spec.Ctr.aesFinalSig.retBits abi.ptrBits) (clearUnion ctrFinalOwn v.clear) [] = true := by
  have e : (Proof.Variants.AesCtr32.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratchWiped 80 .x6 10
        (Impl.AesCtr.AArch64.cryptFinal v.callee v.suffix)) 80
        (Spec.Ctr.aesFinalSig.retBits abi.ptrBits) (clearUnion ctrFinalOwn v.clear) []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

end VG.Proof.Aes.AArch64.ModesScrub
