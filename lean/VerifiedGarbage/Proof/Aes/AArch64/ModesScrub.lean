module

public import VerifiedGarbage.Spec.Ctr.Final
public import VerifiedGarbage.Spec.Ofb.Final
public import VerifiedGarbage.Spec.Cfb.Final
public import VerifiedGarbage.Spec.Cfb8.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
import VerifiedGarbage.Proof.AesEcb.Wipe

/-!
# AES's streaming modes on AArch64, without secret residue

The postconditions of `vg_aes_ctr_final`, `vg_aes_ofb_final`,
`vg_aes_cfb128_encrypt_final`, `vg_aes_cfb128_decrypt_final`,
`vg_aes_cfb8_encrypt` and `vg_aes_cfb8_decrypt` read the memory on return
only within the block at `iv` (or `ctr`) and the data
(`ScrubAll.ScrubAllOk`): each implementation, generic over the AES
implementation it calls, returns with every register it may leave secret
cleared, and its whole stack zeroed, if it has one (`ScrubAll.withScrubAll`).

The whole-block functions of CTR, OFB and CFB128 are not converted here: the
final functions call them by name, so their code changes only with the
finals'.
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

end VG.Proof.Aes.AArch64.ModesScrub
