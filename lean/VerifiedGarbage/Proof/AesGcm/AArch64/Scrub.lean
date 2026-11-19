module

public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Spec.Gcm.OutOfPlace
public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
public import VerifiedGarbage.Impl.Residue.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.Scratch

/-!
# AES-GCM on AArch64, without secret residue

The postconditions of `vg_aes_gcm_init`, `vg_aes_gcm_open` and
`vg_aes_gcm_open_to` read the memory on return only within the key context,
the data and the output (`ScrubAll.ScrubAllOk`): each implementation, generic
over the implementations of counter mode, GHASH and key expansion it calls,
returns with every register it may leave secret cleared and its whole stack
zeroed (`ScrubAll.scrubAllOf`, `Instances.lean`). Its frame is sized to what its
callees need (`gcmWn`, `gcmInitWn`), so that the zeroing costs little where
counter mode needs no working space.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll

/-- The bytes at `d` within a buffer on which two memories agree. -/
theorem bytesAt_of {m₁ m₂ : Mem} {p : Addr} {L : Nat} (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a)
    {d n : Nat} (hn : d + n ≤ L) :
    Spec.Aes.bytesAt m₂ (p + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt m₁ (p + BitVec.ofNat 64 d) n := by
  simp only [Spec.Aes.bytesAt]
  refine List.map_congr_left fun i hi => (h _ ?_).symm
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact Region.contains_ofNat p (by have := List.mem_range.mp hi; omega)

/-- `bytesAt_of` at the start of the buffer. -/
theorem bytesAt_of0 {m₁ m₂ : Mem} {p : Addr} {L : Nat} (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a)
    {n : Nat} (hn : n ≤ L) : Spec.Aes.bytesAt m₂ p n = Spec.Aes.bytesAt m₁ p n := by
  simpa using bytesAt_of h (d := 0) (n := n) (by omega)

theorem initOk (stack : Nat) (hW : 0 < stack) :
    ScrubAllOk (Spec.Gcm.initContract abi stack) stack (Spec.Gcm.initSig.retBits abi.ptrBits) :=
  scrubAllOk_regs_pre (sig := Spec.Gcm.initSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    fun vs m m₁ m₂ r hlen hp hb h => by
    match vs, hlen with
    | [key, keyLen, ctx], _ =>
      simp only [Spec.Gcm.initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr] (Spec.Gcm.initPre 64) _ m at hp
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr] (Spec.Gcm.initPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr] (Spec.Gcm.initPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Gcm.initPre, Spec.Gcm.initPost, Spec.Gcm.KeyRepr, Spec.Gcm.ctxH,
        Spec.Gcm.blockAt, ArgWord.ofRaw] at hp h ⊢
      rw [BitVec.setWidth_eq] at hp h ⊢
      obtain ⟨h₁, h₂⟩ := h
      have hR : 16 * (Spec.Aes.rounds ((Spec.Aes.bytesAt m key keyLen.toNat).length / 4) + 1) ≤ 32 * 8 := by
        simp only [Spec.Aes.bytesAt, List.length_map, List.length_range, Spec.Aes.rounds]
        rcases hp with h | h | h <;> simp [h]
      refine ⟨?_, ?_⟩
      · rw [bytesAt_of0 hb.2 hR]; exact h₁
      · rw [show (ctx + 240 : BitVec 64) = ctx + BitVec.ofNat 64 240 from rfl,
          bytesAt_of hb.2 (d := 240) (n := 16) (by decide)]
        exact h₂

theorem sealOk (stack : Nat) :
    ScrubAllOk (Spec.Gcm.sealContract abi stack) stack (Spec.Gcm.sealSig.retBits abi.ptrBits) := by
  refine scrubAllOk_args_any (sig := Spec.Gcm.sealSig) ?_
  intro vs m m₁ m₂ r hlen hb h
  match vs, hlen with
  | [ctx, rounds, nonce, nonceLen, aad, aadLen, data, len, tag], _ =>
    simp only [Spec.Gcm.sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr]
      (Spec.Gcm.sealPost 64) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr]
      (Spec.Gcm.sealPost 64) _ m m₂ r
    dsimp only [Curry.apply, Spec.Gcm.sealPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
    simp only [BitVec.setWidth_eq] at h ⊢
    rw [bytesAt_of0 hb.2.2.2.1 (Nat.le_refl _), bytesAt_of0 hb.2.2.2.2 (by omega)]
    exact h

theorem sealRoundsOk (stack : Nat) :
    ScrubAllOk (Proof.AesGcm.sealRoundsContract abi stack) stack (Spec.Gcm.sealSig.retBits abi.ptrBits) := by
  refine scrubAllOk_args_any (sig := Spec.Gcm.sealSig) ?_
  intro vs m m₁ m₂ r hlen hb h
  match vs, hlen with
  | [ctx, rounds, nonce, nonceLen, aad, aadLen, data, len, tag], _ =>
    simp only [Spec.Gcm.sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr]
      (Proof.AesGcm.sealRoundsPost 64) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr]
      (Proof.AesGcm.sealRoundsPost 64) _ m m₂ r
    dsimp only [Curry.apply, Proof.AesGcm.sealRoundsPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
    simp only [BitVec.setWidth_eq] at h ⊢
    rw [bytesAt_of0 hb.2.2.2.1 (Nat.le_refl _), bytesAt_of0 hb.2.2.2.2 (by omega)]
    exact h

theorem sealGatherOk (stack : Nat) :
    ScrubAllOk (Spec.Gcm.sealGatherContract abi stack) stack (Spec.Gcm.sealGatherSig.retBits abi.ptrBits) := by
  refine scrubAllOk_args_any (sig := Spec.Gcm.sealGatherSig) ?_
  intro vs m m₁ m₂ r hlen hb h
  match vs, hlen with
  | [ctx, rounds, nonce, nonceLen, aad, aadLen, src, srcCount, dst, len, tag], _ =>
    simp only [Spec.Gcm.sealGatherSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr]
      (Spec.Gcm.sealGatherPost 64) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr]
      (Spec.Gcm.sealGatherPost 64) _ m m₂ r
    dsimp only [Curry.apply, Spec.Gcm.sealGatherPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
    simp only [BitVec.setWidth_eq] at h ⊢
    intro key hk hl
    rw [bytesAt_of0 hb.2.2.2.1 (Nat.le_refl _), bytesAt_of0 hb.2.2.2.2 (by omega)]
    exact h key hk hl

theorem openOk (stack : Nat) :
    ScrubAllOk (Spec.Gcm.openContract abi stack) stack (Spec.Gcm.openSig.retBits abi.ptrBits) := by
  -- The postcondition is a `match` on a decryption: prove the locality by
  -- intros, so that no expected type of a `fun` is reduced to it.
  refine scrubAllOk_args_any (sig := Spec.Gcm.openSig) ?_
  intro vs m m₁ m₂ r hlen hb h
  match vs, hlen with
  | [ctx, rounds, nonce, nonceLen, aad, aadLen, data, len, tag, tagLen], _ =>
    simp only [Spec.Gcm.openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
      ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
      (Spec.Gcm.openPost 64) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
      ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
      (Spec.Gcm.openPost 64) _ m m₂ r
    dsimp only [Curry.apply, Spec.Gcm.openPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
    simp only [BitVec.setWidth_eq] at h ⊢
    intro key hk
    rw [bytesAt_of0 hb.2.2.2.1 (Nat.le_refl _)]
    exact h key hk

theorem openToOk (stack : Nat) :
    ScrubAllOk (Spec.Gcm.openToContract abi stack) stack (Spec.Gcm.openToSig.retBits abi.ptrBits) := by
  refine scrubAllOk_args_pre_any (sig := Spec.Gcm.openToSig) ?_
  intro vs m m₁ m₂ r hlen hp hb h
  match vs, hlen with
  | [ctx, rounds, nonce, nonceLen, aad, aadLen, src, len, dst, dstLen, tag, tagLen], _ =>
    simp only [Spec.Gcm.openToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
      ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
      (Spec.Gcm.openToPre 64) _ m at hp
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
      ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
      (Spec.Gcm.openToPost 64) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
      ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
      (Spec.Gcm.openToPost 64) _ m m₂ r
    dsimp only [Curry.apply, Spec.Gcm.openToPre, Spec.Gcm.openToPost, ArgWord.ofRaw, IntTy.bits] at hp h ⊢
    simp only [BitVec.setWidth_eq] at hp h ⊢
    intro key hk
    rw [bytesAt_of0 hb.2.2.2.2.1 (by omega)]
    exact h key hk

/-- The registers the tails of `init`, `open` and `open_to` clear: those
they may write, with every implementation of counter mode, GHASH and key
expansion (`Instances.lean`). -/
def clear : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
    .v26, .v27, .v28, .v29, .v30, .v31], []⟩


end VG.Proof.AesGcm.AArch64.Scrub
