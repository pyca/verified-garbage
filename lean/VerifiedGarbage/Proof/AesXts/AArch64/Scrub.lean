module

public import VerifiedGarbage.Spec.Xts.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
import VerifiedGarbage.Proof.AesEcb.Wipe

/-!
# XTS-AES on AArch64, without secret residue

The postconditions of `vg_aes_xts_encrypt_unit` and
`vg_aes_xts_decrypt_unit` read the memory on return only within the data
(`ScrubAll.ScrubAllOk`): each implementation, generic over the XTS
implementation it calls and without frames, returns with every register it
may leave secret cleared (`ScrubAll.withScrubAll`).
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

end VG.Proof.AesXts.AArch64.Scrub
