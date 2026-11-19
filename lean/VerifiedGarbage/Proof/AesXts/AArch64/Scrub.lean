module

public import VerifiedGarbage.Spec.Xts.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Variants.AesXts.AArch64
public import VerifiedGarbage.Impl.AesXts.AArch64Unit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.AesEcb.Wipe

/-!
# XTS-AES on AArch64, without secret residue

The postconditions of `vg_aes_xts_encrypt_unit` and
`vg_aes_xts_decrypt_unit` read the memory on return only within the data
(`ScrubAll.ScrubAllOk`): each implementation, generic over the XTS
implementation it calls and without frames, returns with every register it
may leave secret cleared (`ScrubAll.scrubAllOf`).
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll
open VG.Proof.AesEcb (agree_of bytesAt_congr)

theorem encryptOk : ScrubAllOk (Spec.Xts.aesEncryptUnitContract abi 0) 0
    (Spec.Xts.aesUnitSig.retBits abi.ptrBits) :=
  scrubAllOk_regs0 (sig := Spec.Xts.aesUnitSig) (by decide) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [_, _, _, _, _, n, _], _ =>
      simp only [Spec.Xts.aesUnitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk
      have h' := h key hk
      dsimp only [ArgWord.ofRaw] at h' ⊢
      have hd := agree_of hb.2.2.2.1
      rw [bytesAt_congr fun i hi => hd i (by have := AesEcb.n_le (pb := abi.ptrBits) n; omega_using [hi, this])]
      exact h'

theorem decryptOk : ScrubAllOk (Spec.Xts.aesDecryptUnitContract abi 0) 0
    (Spec.Xts.aesUnitSig.retBits abi.ptrBits) :=
  scrubAllOk_regs0 (sig := Spec.Xts.aesUnitSig) (by decide) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [_, _, _, _, _, n, _], _ =>
      simp only [Spec.Xts.aesUnitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk
      have h' := h key hk
      dsimp only [ArgWord.ofRaw] at h' ⊢
      have hd := agree_of hb.2.2.2.1
      rw [bytesAt_congr fun i hi => hd i (by have := AesEcb.n_le (pb := abi.ptrBits) n; omega_using [hi, this])]
      exact h'

/-- The registers `vg_aes_xts_encrypt_unit`'s code writes itself: its tail clears
them with those its `vg_aes_xts_*` functions write. -/
def encryptOwn : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
    .v26, .v27, .v28, .v29, .v30, .v31],
   []⟩

/-- What `scrubAllOf` needs of it with each implementation: evaluated here. -/
theorem encryptSide (v : Proof.AesXts.AArch64.XtsImpl) (hv : v ∈ Proof.Variants.AesXts.AArch64.variants) :
    scrubSide (Impl.AesXts.AArch64Unit.encrypt v.enc) 0 (Spec.Xts.aesUnitSig.retBits abi.ptrBits)
      (clearUnion encryptOwn v.encClear) [] = true := by
  have e : (Proof.Variants.AesXts.AArch64.variants.all fun v =>
      scrubSide (Impl.AesXts.AArch64Unit.encrypt v.enc) 0 (Spec.Xts.aesUnitSig.retBits abi.ptrBits)
        (clearUnion encryptOwn v.encClear) []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

/-- The registers `vg_aes_xts_decrypt_unit`'s code writes itself: its tail clears
them with those its `vg_aes_xts_*` functions write. -/
def decryptOwn : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
    .v26, .v27, .v28, .v29, .v30, .v31],
   []⟩

/-- What `scrubAllOf` needs of it with each implementation: evaluated here. -/
theorem decryptSide (v : Proof.AesXts.AArch64.XtsImpl) (hv : v ∈ Proof.Variants.AesXts.AArch64.variants) :
    scrubSide (Impl.AesXts.AArch64Unit.decrypt v.enc v.dec) 0 (Spec.Xts.aesUnitSig.retBits abi.ptrBits)
      (clearUnion (clearUnion decryptOwn v.encClear) v.decClear) [] = true := by
  have e : (Proof.Variants.AesXts.AArch64.variants.all fun v =>
      scrubSide (Impl.AesXts.AArch64Unit.decrypt v.enc v.dec) 0 (Spec.Xts.aesUnitSig.retBits abi.ptrBits)
        (clearUnion (clearUnion decryptOwn v.encClear) v.decClear) []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

end VG.Proof.AesXts.AArch64.Scrub
