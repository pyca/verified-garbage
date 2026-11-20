module

public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Spec.Gcm.OutOfPlace
public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Spec.Gcm.Powers8
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
public import VerifiedGarbage.Impl.Residue.AArch64.Scrub
import VerifiedGarbage.Proof.AesGcm.ScratchPowers8
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.Scratch

/-!
# AES-GCM on AArch64, without secret residue

The postconditions of `vg_aes_gcm_init`, `vg_aes_gcm_open` and
`vg_aes_gcm_open_to` read the memory on return only within the key context,
the data and the output (`ScrubAll.ScrubAllOk`): each implementation, generic
over the implementations of counter mode, GHASH and key expansion it calls,
returns with every register it may leave secret cleared and its whole stack
zeroed (`Impl/AesGcm/AArch64/Fn.lean`; `GhashImpls.lean` has the proofs). Its
frame is sized to what its callees need (`gcmWn`, `gcmInitWn`), so that the
zeroing costs little where counter mode needs no working space.
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

theorem sealWithPowersOk (stack : Nat) :
    ScrubAllOk (Spec.Gcm.sealWithPowersContract abi stack) stack (Spec.Gcm.sealWithPowersSig.retBits abi.ptrBits) := by
  refine scrubAllOk_args_any (sig := Spec.Gcm.sealWithPowersSig) ?_
  intro vs m m₁ m₂ r hlen hb h
  match vs, hlen with
  | [ctx, rounds, nonce, nonceLen, aad, aadLen, data, len, tag, pw], _ =>
    simp only [Spec.Gcm.sealWithPowersSig, Spec.Gcm.sealSig, Spec.Gcm.withPowersParam, List.cons_append,
      List.nil_append, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr]
      (Spec.Gcm.sealWithPowersPost 64) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.addr]
      (Spec.Gcm.sealWithPowersPost 64) _ m m₂ r
    dsimp only [Curry.apply, Spec.Gcm.sealWithPowersPost, Spec.Gcm.sealPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
    simp only [BitVec.setWidth_eq] at h ⊢
    intro key hk
    rw [bytesAt_of0 hb.2.2.2.1 (Nat.le_refl _), bytesAt_of0 hb.2.2.2.2.1 (by omega)]
    exact h key hk

theorem openWithPowersOk (stack : Nat) :
    ScrubAllOk (Spec.Gcm.openWithPowersContract abi stack) stack (Spec.Gcm.openWithPowersSig.retBits abi.ptrBits) := by
  refine scrubAllOk_args_any (sig := Spec.Gcm.openWithPowersSig) ?_
  intro vs m m₁ m₂ r hlen hb h
  match vs, hlen with
  | [ctx, rounds, nonce, nonceLen, aad, aadLen, data, len, tag, tagLen, pw], _ =>
    simp only [Spec.Gcm.openWithPowersSig, Spec.Gcm.openSig, Spec.Gcm.withPowersParam, List.cons_append,
      List.nil_append, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr]
      (Spec.Gcm.openWithPowersPost 64) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr]
      (Spec.Gcm.openWithPowersPost 64) _ m m₂ r
    dsimp only [Curry.apply, Spec.Gcm.openWithPowersPost, Spec.Gcm.openPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
    simp only [BitVec.setWidth_eq] at h ⊢
    intro key hk
    rw [bytesAt_of0 hb.2.2.2.1 (Nat.le_refl _)]
    exact h key hk

theorem openToWithPowersOk (stack : Nat) :
    ScrubAllOk (Spec.Gcm.openToWithPowersContract abi stack) stack
      (Spec.Gcm.openToWithPowersSig.retBits abi.ptrBits) := by
  refine scrubAllOk_args_pre_any (sig := Spec.Gcm.openToWithPowersSig) ?_
  intro vs m m₁ m₂ r hlen hp hb h
  match vs, hlen with
  | [ctx, rounds, nonce, nonceLen, aad, aadLen, src, len, dst, dstLen, tag, tagLen, pw], _ =>
    simp only [Spec.Gcm.openToWithPowersSig, Spec.Gcm.openToSig, Spec.Gcm.withPowersParam, List.cons_append,
      List.nil_append, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64,
        ArgWord.addr] (Spec.Gcm.openToWithPowersPre 64) _ m at hp
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64,
        ArgWord.addr] (Spec.Gcm.openToWithPowersPost 64) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64,
        ArgWord.addr] (Spec.Gcm.openToWithPowersPost 64) _ m m₂ r
    dsimp only [Curry.apply, Spec.Gcm.openToWithPowersPre, Spec.Gcm.openToPre, Spec.Gcm.openToWithPowersPost,
      Spec.Gcm.openToPost, ArgWord.ofRaw, IntTy.bits] at hp h ⊢
    simp only [BitVec.setWidth_eq] at hp h ⊢
    intro key hk
    rw [bytesAt_of0 hb.2.2.2.2.1 (by omega)]
    exact h key hk

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

/-- `vg_aes_gcm_store_powers`: its postcondition reads the memory on return
only within the powers. -/
theorem storePowersOk (stack : Nat) (hW : 0 < stack) :
    ScrubAllOk (Spec.Gcm.storePowersContract abi stack) stack (Spec.Gcm.storePowersSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Gcm.storePowersSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.AesGcm.storePowersPostOut_local _)

/-- `storePowersOk` in its frame of 80 bytes. -/
theorem storePowersOk80 :
    ScrubAllOk (Spec.Gcm.storePowersContract abi 80) 80 (Spec.Gcm.storePowersSig.retBits abi.ptrBits) :=
  storePowersOk 80 (by decide)

/-! ## The stream functions

Their postconditions read the memory on return only within their buffers:
the stream's state, and the text or the tag. -/

section
variable (pb : Nat)
open VG.Spec.Gcm VG.Proof.AesGcm

/-- `Spec.Gcm.streamEncryptPost` reads the memory on return only within the buffers. -/
theorem streamEncryptSpecPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (streamCryptSig.words pb).length →
    (∀ b ∈ Sig.bufs streamCryptSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamCryptSig.words pb) (Spec.Gcm.streamEncryptPost pb) vs m m₁ r →
      Curry.apply (streamCryptSig.words pb) (Spec.Gcm.streamEncryptPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 6) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨rd, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨state, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨al, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [streamCryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64, ArgWord.addr, ArgWord.int pb]
    (Spec.Gcm.streamEncryptPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64, ArgWord.addr, ArgWord.int pb]
    (Spec.Gcm.streamEncryptPost pb) _ m m₂ r
  dsimp only [Curry.apply, Spec.Gcm.streamEncryptPost, ArgWord.ofRaw] at h ⊢
  intro key hk iv a p hr hl ht
  obtain ⟨g₁, g₂⟩ := h key hk iv a p hr hl ht
  have := Nat.mod_le len.toNat (2 ^ pb)
  refine ⟨streamRepr_congr (fun i hi => agree_of hb.2.1 i (by omega_using [hi])) g₁, Eq.trans ?_ g₂⟩
  exact bytesAt_congr fun i hi => agree_of hb.2.2 i (by
    rw [BitVec.toNat_setWidth] at hi; omega_using [this, hi])

/-- `Spec.Gcm.streamDecryptPost` reads the memory on return only within the buffers. -/
theorem streamDecryptSpecPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (streamCryptSig.words pb).length →
    (∀ b ∈ Sig.bufs streamCryptSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamCryptSig.words pb) (Spec.Gcm.streamDecryptPost pb) vs m m₁ r →
      Curry.apply (streamCryptSig.words pb) (Spec.Gcm.streamDecryptPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 6) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨rd, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨state, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨al, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [streamCryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64, ArgWord.addr, ArgWord.int pb]
    (Spec.Gcm.streamDecryptPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64, ArgWord.addr, ArgWord.int pb]
    (Spec.Gcm.streamDecryptPost pb) _ m m₂ r
  dsimp only [Curry.apply, Spec.Gcm.streamDecryptPost, ArgWord.ofRaw] at h ⊢
  intro key hk iv a p hr hl ht
  obtain ⟨g₁, g₂⟩ := h key hk iv a p hr hl ht
  have := Nat.mod_le len.toNat (2 ^ pb)
  refine ⟨streamRepr_congr (fun i hi => agree_of hb.2.1 i (by omega_using [hi])) g₁, Eq.trans ?_ g₂⟩
  exact bytesAt_congr fun i hi => agree_of hb.2.2 i (by
    rw [BitVec.toNat_setWidth] at hi; omega_using [this, hi])

/-- `Spec.Gcm.streamFinishPost` reads the memory on return only within the buffers. -/
theorem streamFinishSpecPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (streamFinishSig.words pb).length →
    (∀ b ∈ Sig.bufs streamFinishSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamFinishSig.words pb) (Spec.Gcm.streamFinishPost pb) vs m m₁ r →
      Curry.apply (streamFinishSig.words pb) (Spec.Gcm.streamFinishPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 5) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨rd, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨state, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨al, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [streamFinishSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64, ArgWord.addr]
    (Spec.Gcm.streamFinishPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64, ArgWord.addr]
    (Spec.Gcm.streamFinishPost pb) _ m m₂ r
  dsimp only [Curry.apply, Spec.Gcm.streamFinishPost, ArgWord.ofRaw] at h ⊢
  intro key hk iv a c hr hl ht
  refine Eq.trans ?_ (h key hk iv a c hr hl ht)
  exact bytesAt_congr fun i hi => agree_of hb.2.2 i (by omega_using [hi])

/-- `Spec.Gcm.streamVerifyPost` reads the memory on return only within the buffers. -/
theorem streamVerifySpecPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (streamVerifySig.words pb).length →
    (∀ b ∈ Sig.bufs streamVerifySig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamVerifySig.words pb) (Spec.Gcm.streamVerifyPost pb) vs m m₁ r →
      Curry.apply (streamVerifySig.words pb) (Spec.Gcm.streamVerifyPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 6) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨rd, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨state, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨al, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tgl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [streamVerifySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64, ArgWord.addr, ArgWord.int pb]
    (Spec.Gcm.streamVerifyPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64, ArgWord.addr, ArgWord.int pb]
    (Spec.Gcm.streamVerifyPost pb) _ m m₂ r
  dsimp only [Curry.apply, Spec.Gcm.streamVerifyPost, ArgWord.ofRaw] at h ⊢
  exact h

end

theorem streamInitOk (stack : Nat) (hW : 0 < stack) :
    ScrubAllOk (Spec.Gcm.streamInitContract abi stack) stack (Spec.Gcm.streamInitSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Gcm.streamInitSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _) (Proof.AesGcm.streamInitPostOut_local _)

theorem streamAadOk (stack : Nat) (hW : 0 < stack) :
    ScrubAllOk (Spec.Gcm.streamAadContract abi stack) stack (Spec.Gcm.streamAadSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Gcm.streamAadSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _) (Proof.AesGcm.streamAadPostOut_local _)

theorem streamEncryptOk (stack : Nat) (hW : 0 < stack) :
    ScrubAllOk (Spec.Gcm.streamEncryptContract abi stack) stack (Spec.Gcm.streamCryptSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Gcm.streamCryptSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _) (streamEncryptSpecPostOut_local _)

theorem streamDecryptOk (stack : Nat) (hW : 0 < stack) :
    ScrubAllOk (Spec.Gcm.streamDecryptContract abi stack) stack (Spec.Gcm.streamCryptSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Gcm.streamCryptSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _) (streamDecryptSpecPostOut_local _)

theorem streamFinishOk (stack : Nat) (hW : 0 < stack) :
    ScrubAllOk (Spec.Gcm.streamFinishContract abi stack) stack (Spec.Gcm.streamFinishSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Gcm.streamFinishSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _) (streamFinishSpecPostOut_local _)

theorem streamVerifyOk (stack : Nat) (hW : 0 < stack) :
    ScrubAllOk (Spec.Gcm.streamVerifyContract abi stack) stack (Spec.Gcm.streamVerifySig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Gcm.streamVerifySig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _) (streamVerifySpecPostOut_local _)

end VG.Proof.AesGcm.AArch64.Scrub
