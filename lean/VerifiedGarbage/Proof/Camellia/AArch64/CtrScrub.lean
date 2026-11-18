module

public import VerifiedGarbage.Spec.Camellia.Ctr
public import VerifiedGarbage.Spec.Camellia.CtrFinal
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
import VerifiedGarbage.Proof.AesEcb.Wipe
import VerifiedGarbage.Proof.AesCbc.Wipe

/-!
# Camellia-CTR on AArch64, without secret residue

The postconditions of `vg_camellia_ctr` and `vg_camellia_ctr_final` read the
memory on return only within the counter block and the data
(`ScrubAll.ScrubAllOk`): each returns with every register it may leave
secret cleared, and its whole stack zeroed (`ScrubAll.withScrubAll`), among
which the frame of `vg_camellia_ctr`'s working space, which no longer zeroes
itself.
-/

@[expose] public section

namespace VG.Proof.Camellia.AArch64.CtrScrub

open VG.AArch64 VG.AArch64.ScrubAll
open VG.Proof.AesEcb (agree_of bytesAt_congr)

theorem ctrOk : ScrubAllOk (Spec.Camellia.ctrContract abi 3344) 3344 (Spec.Camellia.ctrSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Camellia.ctrSig) (by decide) (W := 3344) (by decide) (Nat.le_refl _)
    fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [_, _, _, _, n], _ =>
      simp only [Spec.Camellia.ctrSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk
      have h' := h key hk
      dsimp only [ArgWord.ofRaw] at h' ⊢
      have hd := agree_of hb.2.2
      rw [AesCbc.Wipe.blocksAt_congr fun i hi => hd i (by have := AesEcb.n_le (pb := abi.ptrBits) n; omega_using [hi, this]),
        bytesAt_congr (agree_of hb.2.1)]
      exact h'

theorem ctrFinalOk : ScrubAllOk (Spec.Camellia.ctrFinalContract abi 3424) 3424
    (Spec.Camellia.ctrFinalSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Camellia.ctrFinalSig) (by decide) (W := 3424) (by decide) (Nat.le_refl _)
    fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [_, _, _, _, n], _ =>
      simp only [Spec.Camellia.ctrFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk
      have h' := h key hk
      dsimp only [ArgWord.ofRaw, Spec.Ctr.CryptFinal] at h' ⊢
      have hd := agree_of hb.2.2
      rw [bytesAt_congr fun i hi => hd i (by have := AesEcb.n_le (pb := abi.ptrBits) n; omega_using [hi, this]),
        bytesAt_congr (agree_of hb.2.1)]
      exact h'

end VG.Proof.Camellia.AArch64.CtrScrub
