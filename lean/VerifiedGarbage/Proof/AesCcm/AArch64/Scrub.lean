module

public import VerifiedGarbage.Spec.Ccm.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll

/-!
# AES-CCM on AArch64, without secret residue

The postconditions of `vg_aes_ccm_seal` and `vg_aes_ccm_open` read the memory
on return only within the data and the tag (`ScrubAll.ScrubAllOk`): each
implementation, generic over the CMAC implementation it calls and its counter
mode, returns with every register it may leave secret cleared and its whole
stack zeroed (`ScrubAll.withScrubAll`). Its frame is sized to what its
callees need (`Frame.lean`: 416 bytes with the Cryptographic Extension, 2592
otherwise), so that the zeroing costs little where the callees need no
working space.
-/

@[expose] public section

namespace VG.Proof.AesCcm.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll

/-- The bytes of a buffer on which two memories agree. -/
theorem bytesAt_of {m₁ m₂ : Mem} {p : Addr} {L : Nat} (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a)
    {n : Nat} (hn : n ≤ L) : Spec.Aes.bytesAt m₂ p n = Spec.Aes.bytesAt m₁ p n := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => (h _ (Region.contains_ofNat p (by have := List.mem_range.mp hi; omega))).symm

theorem sealOk (stack : Nat) :
    ScrubAllOk (Spec.Ccm.sealContract abi stack) stack (Spec.Ccm.sealSig.retBits abi.ptrBits) :=
  scrubAllOk_args_any (sig := Spec.Ccm.sealSig) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ccm.sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ccm.sealPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ccm.sealPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ccm.sealPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [h key hk, bytesAt_of hb.2.2.2.1 (by simp), bytesAt_of hb.2.2.2.2 (by simp)]

theorem openOk (stack : Nat) :
    ScrubAllOk (Spec.Ccm.openContract abi stack) stack (Spec.Ccm.openSig.retBits abi.ptrBits) :=
  scrubAllOk_args_any (sig := Spec.Ccm.openSig) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ccm.openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ccm.openPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ccm.openPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ccm.openPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [bytesAt_of hb.2.2.2.1 (by simp)]
      exact h key hk

end VG.Proof.AesCcm.AArch64.Scrub
