module

public import VerifiedGarbage.Impl.Aes.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.PPC64LE.ExpandKey
public import VerifiedGarbage.Proof.AesEcb.PPC64LE
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Wiped
public import VerifiedGarbage.Proof.AesCtr.PPC64LE.Verified
public import VerifiedGarbage.Proof.AesCtr.PPC64LE.Final
public import VerifiedGarbage.Proof.AesCfb.PPC64LE.Verified
public import VerifiedGarbage.Proof.AesCfb.PPC64LE.Final
public import VerifiedGarbage.Proof.AesCfb8.PPC64LE.Verified
public import VerifiedGarbage.Proof.AesOfb.PPC64LE.Verified
public import VerifiedGarbage.Proof.AesOfb.PPC64LE.Final
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Aes.Scratch
import VerifiedGarbage.Proof.AesEcb.Wipe
import VerifiedGarbage.Proof.AesCbc.Wipe
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Lit

/-!
# AES and its modes on PPC64LE, without secret residue

`vg_aes_expand_key`, `vg_aes_ecb_encrypt`, `vg_aes_ecb_decrypt`,
`vg_aes_cbc_encrypt`, `vg_aes_cbc_decrypt`, `vg_aes_ctr`,
`vg_aes_cfb128_encrypt`, `vg_aes_cfb128_decrypt`, `vg_aes_cfb8_encrypt`,
`vg_aes_cfb8_decrypt` and `vg_aes_ofb`, and the final partial-block functions
of CTR, CFB128 and OFB. Each is followed by `Impl.Scrub.PPC64LE.scrubTail`
(`PPC64LE.Scrub.verifiedScrubbed`), which clears the volatile registers and the
stack its frames used, but the final functions of CFB128 and OFB, which zero
their whole frame themselves and have no frames of their own inside it, and
need only the clearing of the registers (`PPC64LE.Scrub.verifiedScrubbedWiped`).
`vg_aes_ctr_final` calls the code of `vg_aes_ctr` as the internal
`vg_aes_ctr_core`. Their postconditions read the memory on return only
within their buffers, by RISC-V's proofs (`Proof/Aes/RISCV64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Aes.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub VG.Proof.Aes.ScrubLocal

/-! ## Postconditions -/

theorem expandKeyOut (stack : Nat) :
    PostOut (Spec.Aes.expandKeyContract PPC64LE.abi stack) (Spec.Aes.expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Aes.expandKeyPostOut_local _)

theorem len_le (x : BitVec 64) (k : Nat) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat * k ≤ x.toNat * k :=
  Nat.le_refl _

theorem len_le1 (x : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size :=
  Nat.le_of_eq (Nat.mul_one _).symm

namespace Ecb

open VG.Proof.AesEcb

/-- The postcondition of `vg_aes_ecb_encrypt` reads the memory on return only
within the buffers. -/
theorem encryptOut (stack : Nat) :
    PostOut (Spec.AesEcb.encryptContract abi stack) (Spec.Aes.blocksSig.retBits 64) := by
  rw [Proof.AesEcb.encrypt_eq]
  exact postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, rfl⟩ := vs_eq hlen
    rw [bufs_eq] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun key hk => ?_, fun z hz => ?_⟩
    · show Spec.Aes.statesAt m₂ c (d.setWidth abi.ptrBits).toNat = _
      have hd := agree_of hb.2.1
      rw [statesAt_congr fun i hi => hd i (by have := n_le (pb := abi.ptrBits) d; omega_using [hi, this])]
      exact h1 key hk
    · rw [← hb.2.2 z hz]
      exact h2 z hz

/-- The postcondition of `vg_aes_ecb_decrypt` reads the memory on return only
within the buffers. -/
theorem decryptOut (stack : Nat) :
    PostOut (Spec.AesEcb.decryptContract abi stack) (Spec.Aes.blocksSig.retBits 64) := by
  rw [Proof.AesEcb.decrypt_eq]
  exact postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, rfl⟩ := vs_eq hlen
    rw [bufs_eq] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun key hk => ?_, fun z hz => ?_⟩
    · show Spec.Aes.statesAt m₂ c (d.setWidth abi.ptrBits).toNat = _
      have hd := agree_of hb.2.1
      rw [statesAt_congr fun i hi => hd i (by have := n_le (pb := abi.ptrBits) d; omega_using [hi, this])]
      exact h1 key hk
    · rw [← hb.2.2 z hz]
      exact h2 z hz

end Ecb

namespace Cbc

open VG.Proof.AesCbc.Wipe

/-- The postcondition of `vg_aes_cbc_encrypt` reads the memory on return only
within the buffers. -/
theorem encryptOut (stack : Nat) :
    PostOut (Spec.Cbc.aesEncryptContract abi stack) (Spec.Cbc.aesSig.retBits 64) := by
  rw [Proof.AesCbc.Wipe.encrypt_eq]
  exact postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
    rw [bufs_eq] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
    obtain ⟨h1, h2⟩ := h
    have hd := AesEcb.agree_of hb.2.2.1
    have hb' : Spec.Cbc.blocksAt m₂ d (e.setWidth abi.ptrBits).toNat = Spec.Cbc.blocksAt m₁ d (e.setWidth abi.ptrBits).toNat :=
      blocksAt_congr fun i hi => hd i (by have := AesEcb.n_le (pb := abi.ptrBits) e; omega_using [hi, this])
    have hc := AesEcb.bytesAt_congr (AesEcb.agree_of hb.2.1)
    refine ⟨fun key hk => ?_, fun z hz => ?_⟩
    · obtain ⟨h1a, h1b⟩ := h1 key hk
      exact ⟨hb'.trans h1a, hc.trans h1b⟩
    · rw [← hb.2.2.2 z hz]
      exact h2 z hz

/-- The postcondition of `vg_aes_cbc_decrypt` reads the memory on return only
within the buffers. -/
theorem decryptOut (stack : Nat) :
    PostOut (Spec.Cbc.aesDecryptContract abi stack) (Spec.Cbc.aesSig.retBits 64) := by
  rw [Proof.AesCbc.Wipe.decrypt_eq]
  exact postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
    rw [bufs_eq] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
    obtain ⟨h1, h2⟩ := h
    have hd := AesEcb.agree_of hb.2.2.1
    have hb' : Spec.Cbc.blocksAt m₂ d (e.setWidth abi.ptrBits).toNat = Spec.Cbc.blocksAt m₁ d (e.setWidth abi.ptrBits).toNat :=
      blocksAt_congr fun i hi => hd i (by have := AesEcb.n_le (pb := abi.ptrBits) e; omega_using [hi, this])
    have hc := AesEcb.bytesAt_congr (AesEcb.agree_of hb.2.1)
    refine ⟨fun key hk => ?_, fun z hz => ?_⟩
    · obtain ⟨h1a, h1b⟩ := h1 key hk
      exact ⟨hb'.trans h1a, hc.trans h1b⟩
    · rw [← hb.2.2.2 z hz]
      exact h2 z hz

end Cbc

theorem cfb8EncryptOut (stack : Nat) :
    PostOut (Spec.Cfb8.aesEncryptContract PPC64LE.abi stack) (Spec.Cfb8.aesSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Cfb8.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfb8DecryptOut (stack : Nat) :
    PostOut (Spec.Cfb8.aesDecryptContract PPC64LE.abi stack) (Spec.Cfb8.aesSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Cfb8.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptOut (stack : Nat) :
    PostOut (Spec.Cfb.aesEncryptContract PPC64LE.abi stack) (Spec.Cfb.aesSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Cfb.aesSig, Spec.Cbc.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [blocksAt_of0 hb.2.2.1 (len_le ln 16), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptOut (stack : Nat) :
    PostOut (Spec.Cfb.aesDecryptContract PPC64LE.abi stack) (Spec.Cfb.aesSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Cfb.aesSig, Spec.Cbc.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [blocksAt_of0 hb.2.2.1 (len_le ln 16), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbOut (stack : Nat) :
    PostOut (Spec.Ofb.aesContract PPC64LE.abi stack) (Spec.Ofb.aesSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Ofb.aesSig, Spec.Cbc.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [blocksAt_of0 hb.2.2.1 (len_le ln 16), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ctrOut (stack : Nat) :
    PostOut (Spec.Ctr.aesContract PPC64LE.abi stack) (Spec.Ctr.aesSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, ctr, dt, ln, sc], _ =>
      simp only [Spec.Ctr.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ ctr 16 = _
      intro key hk
      rw [blocksAt_of0 hb.2.2.1 (len_le ln 16), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ctrFinalOut (stack : Nat) :
    PostOut (Spec.Ctr.aesFinalContract PPC64LE.abi stack) (Spec.Ctr.aesFinalSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, ctr, dt, ln, sc], _ =>
      simp only [Spec.Ctr.aesFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ ctr 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptFinalOut (stack : Nat) :
    PostOut (Spec.Cfb.aesEncryptFinalContract PPC64LE.abi stack) (Spec.Cfb.aesFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Cfb.aesFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptFinalOut (stack : Nat) :
    PostOut (Spec.Cfb.aesDecryptFinalContract PPC64LE.abi stack) (Spec.Cfb.aesFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Cfb.aesFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbFinalOut (stack : Nat) :
    PostOut (Spec.Ofb.aesFinalContract PPC64LE.abi stack) (Spec.Ofb.aesFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Ofb.aesFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk
/-! ## The functions as emitted -/

/-- `vg_aes_expand_key` as emitted (`Impl.Aes.PPC64LE.Fn.expandKey`) meets its
contract in constant time and returns without secret residue. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Aes.PPC64LE.Fn.expandKey
      (Spec.Aes.expandKeyContract PPC64LE.abi) 0 :=
  verifiedScrubbed (api := Spec.Aes.expandKeyApi) {
      code := Impl.Aes.PPC64LE.expandKey
      verified := Proof.Aes.PPC64LE.expandKey_direct_verified }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9]⟩
    (expandKeyOut _)
    (by dsimp only; lit_decide)

/-- `vg_aes_ecb_encrypt` as emitted (`Impl.Aes.PPC64LE.Fn.ecbEncrypt`) meets its
contract in constant time and returns without secret residue. -/
theorem ecbEncrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Aes.PPC64LE.Fn.ecbEncrypt
      (Spec.AesEcb.encryptContract PPC64LE.abi) 0 :=
  verifiedScrubbed (api := Spec.AesEcb.encryptApi) {
      code := Impl.Aes.PPC64LE.encryptBlocks
      verified := Proof.AesEcb.PPC64LE.encrypt_verified }
    0 ⟨true, false, [.r6, .r7, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (Ecb.encryptOut _)
    (by dsimp only; lit_decide)

/-- `vg_aes_ecb_decrypt` as emitted (`Impl.Aes.PPC64LE.Fn.ecbDecrypt`) meets its
contract in constant time and returns without secret residue. -/
theorem ecbDecrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Aes.PPC64LE.Fn.ecbDecrypt
      (Spec.AesEcb.decryptContract PPC64LE.abi) 0 :=
  verifiedScrubbed (api := Spec.AesEcb.decryptApi) {
      code := Impl.Aes.PPC64LE.decryptBlocks
      verified := Proof.AesEcb.PPC64LE.decrypt_verified }
    0 ⟨true, false, [.r6, .r7, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (Ecb.decryptOut _)
    (by dsimp only; lit_decide)

/-- `vg_aes_cbc_encrypt` as emitted (`Impl.Aes.PPC64LE.Fn.cbcEncrypt`) meets its
contract in constant time and returns without secret residue. -/
theorem cbcEncrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Aes.PPC64LE.Fn.cbcEncrypt
      (Spec.Cbc.aesEncryptContract PPC64LE.abi 48) 0 :=
  verifiedScrubbed (api := Spec.Cbc.aesEncryptApi) {
      code := Impl.AesCbc.PPC64LE.Wiped.encrypt
      verified := Proof.AesCbc.PPC64LE.Wiped.encrypt_verified }
    48 ⟨true, true, [.r4, .r5, .r6, .r7, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (Cbc.encryptOut _)
    (by dsimp only; lit_decide)

/-- `vg_aes_cbc_decrypt` as emitted (`Impl.Aes.PPC64LE.Fn.cbcDecrypt`) meets its
contract in constant time and returns without secret residue. -/
theorem cbcDecrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Aes.PPC64LE.Fn.cbcDecrypt
      (Spec.Cbc.aesDecryptContract PPC64LE.abi 48) 0 :=
  verifiedScrubbed (api := Spec.Cbc.aesDecryptApi) {
      code := Impl.AesCbc.PPC64LE.Wiped.decrypt
      verified := Proof.AesCbc.PPC64LE.Wiped.decrypt_verified }
    48 ⟨true, true, [.r4, .r5, .r6, .r7, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v19]⟩
    (Cbc.decryptOut _)
    (by dsimp only; lit_decide)

/-- `vg_aes_ctr` as emitted (`Impl.Aes.PPC64LE.Fn.ctr`) meets its contract in
constant time and returns without secret residue. -/
theorem ctr_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Aes.PPC64LE.Fn.ctr
      (Spec.Ctr.aesContract PPC64LE.abi) 0 :=
  verifiedScrubbed (api := Spec.Ctr.aesApi) {
      code := Impl.AesCtr.PPC64LE.crypt
      verified := Proof.AesCtr.keyed Proof.AesCtr.PPC64LE.crypt_verified }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v19]⟩
    (ctrOut _)
    (by dsimp only; lit_decide)

/-- `vg_aes_ctr_final` as emitted (`Impl.Aes.PPC64LE.Fn.ctrFinal`) meets its
contract in constant time and returns without secret residue. -/
theorem ctrFinal_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Aes.PPC64LE.Fn.ctrFinal
      (Spec.Ctr.aesFinalContract PPC64LE.abi 112) 0 :=
  verifiedScrubbed (api := Spec.Ctr.aesFinalApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 112 .r9 10 Impl.AesCtr.PPC64LE.cryptFinal
      verified := Proof.AesCtr.final_keyed Proof.AesCtr.PPC64LE.Final.cryptFinal_framed }
    112 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v19]⟩
    (ctrFinalOut _)
    (by dsimp only; lit_decide)

/-- `vg_aes_cfb128_encrypt` as emitted (`Impl.Aes.PPC64LE.Fn.cfbEncrypt`) meets
its contract in constant time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Aes.PPC64LE.Fn.cfbEncrypt
      (Spec.Cfb.aesEncryptContract PPC64LE.abi) 0 :=
  verifiedScrubbed (api := Spec.Cfb.aesEncryptApi) {
      code := Impl.AesCfb.PPC64LE.encrypt
      verified := Proof.AesCfb.encrypt_keyed Proof.AesCfb.PPC64LE.encrypt_verified }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (cfbEncryptOut _)
    (by dsimp only; lit_decide)

/-- `vg_aes_cfb128_decrypt` as emitted (`Impl.Aes.PPC64LE.Fn.cfbDecrypt`) meets
its contract in constant time and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Aes.PPC64LE.Fn.cfbDecrypt
      (Spec.Cfb.aesDecryptContract PPC64LE.abi) 0 :=
  verifiedScrubbed (api := Spec.Cfb.aesDecryptApi) {
      code := Impl.AesCfb.PPC64LE.decrypt
      verified := Proof.AesCfb.decrypt_keyed Proof.AesCfb.PPC64LE.decrypt_verified }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (cfbDecryptOut _)
    (by dsimp only; lit_decide)

/-- `vg_aes_cfb128_encrypt_final` as emitted
(`Impl.Aes.PPC64LE.Fn.cfbEncryptFinal`) meets its contract in constant time
and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Aes.PPC64LE.Fn.cfbEncryptFinal
      (Spec.Cfb.aesEncryptFinalContract PPC64LE.abi 96) 0 :=
  verifiedScrubbedWiped (api := Spec.Cfb.aesEncryptFinalApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r9 8 Impl.AesCfb.PPC64LE.encryptFinal
      verified := Proof.AesCfb.encryptFinal_keyed Proof.AesCfb.PPC64LE.Final.encryptFinal_framed }
    96 .r9 8 Impl.AesCfb.PPC64LE.encryptFinal
    ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩ rfl (cfbEncryptFinalOut _) (by dsimp only; lit_decide)

/-- `vg_aes_cfb128_decrypt_final` as emitted
(`Impl.Aes.PPC64LE.Fn.cfbDecryptFinal`) meets its contract in constant time
and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Aes.PPC64LE.Fn.cfbDecryptFinal
      (Spec.Cfb.aesDecryptFinalContract PPC64LE.abi 96) 0 :=
  verifiedScrubbedWiped (api := Spec.Cfb.aesDecryptFinalApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r9 8 Impl.AesCfb.PPC64LE.decryptFinal
      verified := Proof.AesCfb.decryptFinal_keyed Proof.AesCfb.PPC64LE.Final.decryptFinal_framed }
    96 .r9 8 Impl.AesCfb.PPC64LE.decryptFinal
    ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩ rfl (cfbDecryptFinalOut _) (by dsimp only; lit_decide)

/-- `vg_aes_cfb8_encrypt` as emitted (`Impl.Aes.PPC64LE.Fn.cfb8Encrypt`) meets its
contract in constant time and returns without secret residue. -/
theorem cfb8Encrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Aes.PPC64LE.Fn.cfb8Encrypt
      (Spec.Cfb8.aesEncryptContract PPC64LE.abi) 0 :=
  verifiedScrubbed (api := Spec.Cfb8.aesEncryptApi) {
      code := Impl.AesCfb8.PPC64LE.encrypt
      verified := Proof.AesCfb8.encrypt_keyed Proof.AesCfb8.PPC64LE.encrypt_verified }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (cfb8EncryptOut _)
    (by dsimp only; lit_decide)

/-- `vg_aes_cfb8_decrypt` as emitted (`Impl.Aes.PPC64LE.Fn.cfb8Decrypt`) meets its
contract in constant time and returns without secret residue. -/
theorem cfb8Decrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Aes.PPC64LE.Fn.cfb8Decrypt
      (Spec.Cfb8.aesDecryptContract PPC64LE.abi) 0 :=
  verifiedScrubbed (api := Spec.Cfb8.aesDecryptApi) {
      code := Impl.AesCfb8.PPC64LE.decrypt
      verified := Proof.AesCfb8.decrypt_keyed Proof.AesCfb8.PPC64LE.decrypt_verified }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (cfb8DecryptOut _)
    (by dsimp only; lit_decide)

/-- `vg_aes_ofb` as emitted (`Impl.Aes.PPC64LE.Fn.ofb`) meets its contract in
constant time and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Aes.PPC64LE.Fn.ofb
      (Spec.Ofb.aesContract PPC64LE.abi) 0 :=
  verifiedScrubbed (api := Spec.Ofb.aesApi) {
      code := Impl.AesOfb.PPC64LE.crypt
      verified := Proof.AesOfb.keyed Proof.AesOfb.PPC64LE.crypt_verified }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (ofbOut _)
    (by dsimp only; lit_decide)

/-- `vg_aes_ofb_final` as emitted (`Impl.Aes.PPC64LE.Fn.ofbFinal`) meets its
contract in constant time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Aes.PPC64LE.Fn.ofbFinal
      (Spec.Ofb.aesFinalContract PPC64LE.abi 96) 0 :=
  verifiedScrubbedWiped (api := Spec.Ofb.aesFinalApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r9 8 Impl.AesOfb.PPC64LE.cryptFinal
      verified := Proof.AesOfb.final_keyed Proof.AesOfb.PPC64LE.cryptFinal_framed }
    96 .r9 8 Impl.AesOfb.PPC64LE.cryptFinal
    ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩ rfl (ofbFinalOut _) (by dsimp only; lit_decide)

end VG.Proof.Aes.PPC64LE.Scrub
