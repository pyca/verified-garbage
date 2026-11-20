module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Aes.Arm.Fn
public import VerifiedGarbage.Proof.Aes.Arm.Frame
public import VerifiedGarbage.Proof.AesEcb.Arm
public import VerifiedGarbage.Proof.AesCbc.Arm.Wiped
public import VerifiedGarbage.Proof.AesCtr.Arm.Verified
public import VerifiedGarbage.Proof.AesCtr.Arm.Final
public import VerifiedGarbage.Proof.AesCfb.Arm.Verified
public import VerifiedGarbage.Proof.AesCfb.Arm.Final
public import VerifiedGarbage.Proof.AesCfb8.Arm.Verified
public import VerifiedGarbage.Proof.AesOfb.Arm.Verified
public import VerifiedGarbage.Proof.AesOfb.Arm.Final
public import VerifiedGarbage.Proof.AesXts.Arm.Unit.Verified
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Aes.Scratch
import VerifiedGarbage.Proof.AesEcb.Wipe
import VerifiedGarbage.Proof.AesCbc.Wipe
import VerifiedGarbage.Proof.AesCbc.Arm.Body
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Impl.Aes.Arm.Fn
meta import VerifiedGarbage.Proof.Aes.Arm.Frame
meta import VerifiedGarbage.Proof.AesEcb.Arm
meta import VerifiedGarbage.Proof.AesCbc.Arm.Wiped
meta import VerifiedGarbage.Proof.AesCtr.Arm.Verified
meta import VerifiedGarbage.Proof.AesCtr.Arm.Final
meta import VerifiedGarbage.Proof.AesCfb.Arm.Verified
meta import VerifiedGarbage.Proof.AesCfb.Arm.Final
meta import VerifiedGarbage.Proof.AesCfb8.Arm.Verified
meta import VerifiedGarbage.Proof.AesOfb.Arm.Verified
meta import VerifiedGarbage.Proof.AesOfb.Arm.Final
meta import VerifiedGarbage.Proof.AesXts.Arm.Unit.Verified
meta import VerifiedGarbage.Proof.Aes.ScrubLocal
meta import VerifiedGarbage.Proof.Aes.Scratch
meta import VerifiedGarbage.Proof.AesEcb.Wipe
meta import VerifiedGarbage.Proof.AesCbc.Wipe
meta import VerifiedGarbage.Proof.AesCbc.Arm.Body
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# AES and its modes on ARMv7, without secret residue

`vg_aes_expand_key`, `vg_aes_ecb_encrypt`, `vg_aes_ecb_decrypt`,
`vg_aes_cbc_encrypt`, `vg_aes_cbc_decrypt`, `vg_aes_ctr`,
`vg_aes_ctr_final`, `vg_aes_cfb128_encrypt`, `vg_aes_cfb128_decrypt`, their
`_final` functions, `vg_aes_cfb8_encrypt`, `vg_aes_cfb8_decrypt`,
`vg_aes_ofb`, `vg_aes_ofb_final`, `vg_aes_xts_encrypt_unit` and
`vg_aes_xts_decrypt_unit`. Each keeps its working space in frames within
the stack its contract reserves and makes no indirect call (evaluated by
`lit_decide`), and its postcondition reads the memory on return only within
its buffers (`Arm.Scrub.PostOut`, as on RISC-V, `Proof/Aes/RISCV64/Scrub.lean`,
`Proof/AesXts/RISCV64/Scrub.lean`). Each is emitted followed by a wipe of
that stack and by instructions that set the registers a callee may change,
and the flags to constants (`Impl.Aes.Arm.Fn`), and `Fn`
below states that it returns without secret residue
(`Arm.Scrub.verifiedScrubbedF`), which is what its registration binds.

The `_final` functions of CTR, CFB128 and OFB call the code of the
whole-block ones as it is verified, without the wipe, under names of their
own (`vg_aes_ctr_entry`, …), which the emitter writes as internal functions:
their own wipe covers the frames of that call.
-/

@[expose] public section

namespace VG.Proof.Aes.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Proof.Aes.ScrubLocal

/-! ## Postconditions -/

theorem expandKeyOut (stack : Nat) :
    PostOut (Spec.Aes.expandKeyContract Arm.abi stack) (Spec.Aes.expandKeySig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Aes.expandKeyPostOut_local _)

theorem len_le (x : BitVec 64) (k : Nat) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat * k ≤ x.toNat * k :=
  Nat.mul_le_mul_right _ (by
    show (x.setWidth 32).toNat ≤ x.toNat
    rw [BitVec.toNat_setWidth]; exact Nat.mod_le _ _)

theorem len_le1 (x : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size :=
  Nat.le_trans (Nat.le_of_eq (Nat.mul_one _).symm) (len_le x 1)

namespace Ecb

open VG.Proof.AesEcb

/-- The postcondition of `vg_aes_ecb_encrypt` reads the memory on return only
within the buffers. -/
theorem encryptOut (stack : Nat) :
    PostOut (Spec.AesEcb.encryptContract abi stack) (Spec.Aes.blocksSig.retBits 32) := by
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
    PostOut (Spec.AesEcb.decryptContract abi stack) (Spec.Aes.blocksSig.retBits 32) := by
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
    PostOut (Spec.Cbc.aesEncryptContract abi stack) (Spec.Cbc.aesSig.retBits 32) := by
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
    PostOut (Spec.Cbc.aesDecryptContract abi stack) (Spec.Cbc.aesSig.retBits 32) := by
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
    PostOut (Spec.Cfb8.aesEncryptContract Arm.abi stack) (Spec.Cfb8.aesSig.retBits 32) :=
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
    PostOut (Spec.Cfb8.aesDecryptContract Arm.abi stack) (Spec.Cfb8.aesSig.retBits 32) :=
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
    PostOut (Spec.Cfb.aesEncryptContract Arm.abi stack) (Spec.Cfb.aesSig.retBits 32) :=
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
    PostOut (Spec.Cfb.aesDecryptContract Arm.abi stack) (Spec.Cfb.aesSig.retBits 32) :=
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
    PostOut (Spec.Ofb.aesContract Arm.abi stack) (Spec.Ofb.aesSig.retBits 32) :=
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
    PostOut (Spec.Ctr.aesContract Arm.abi stack) (Spec.Ctr.aesSig.retBits 32) :=
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
    PostOut (Spec.Ctr.aesFinalContract Arm.abi stack) (Spec.Ctr.aesFinalSig.retBits 32) :=
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
    PostOut (Spec.Cfb.aesEncryptFinalContract Arm.abi stack) (Spec.Cfb.aesFinalSig.retBits 32) :=
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
    PostOut (Spec.Cfb.aesDecryptFinalContract Arm.abi stack) (Spec.Cfb.aesFinalSig.retBits 32) :=
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
    PostOut (Spec.Ofb.aesFinalContract Arm.abi stack) (Spec.Ofb.aesFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Ofb.aesFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem xtsEncryptUnitOut (stack : Nat) :
    PostOut (Spec.Xts.aesEncryptUnitContract Arm.abi stack) (Spec.Xts.aesUnitSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, tsch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Xts.aesUnitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, Spec.Xts.KeySchedules m sch tsch _ key → _ = some (Spec.Aes.bytesAt m₂ dt _)
      intro key hk
      rw [bytesAt_of0 hb.2.2.2.1 (len_le1 ln)]
      exact h key hk

theorem xtsDecryptUnitOut (stack : Nat) :
    PostOut (Spec.Xts.aesDecryptUnitContract Arm.abi stack) (Spec.Xts.aesUnitSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, tsch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Xts.aesUnitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, Spec.Xts.KeySchedules m sch tsch _ key → _ = some (Spec.Aes.bytesAt m₂ dt _)
      intro key hk
      rw [bytesAt_of0 hb.2.2.2.1 (len_le1 ln)]
      exact h key hk

/-! ## The code: its frames, and no indirect call -/

theorem frameOk_8 : FrameOk 8 := by decide
theorem frameOk_16 : FrameOk 16 := by decide
theorem frameOk_24 : FrameOk 24 := by decide
theorem frameOk_32 : FrameOk 32 := by decide
theorem frameOk_72 : FrameOk 72 := by decide
theorem frameOk_88 : FrameOk 88 := by decide
theorem frameOk_512 : FrameOk 512 := by decide

theorem expandKey_code :
    CodeOk (Impl.StackScratch.Arm.withRegScratchWiped 512 .r3 128 Impl.Aes.Arm.expandKey) 512 := by
  lit_decide

theorem ecbEncrypt_code : CodeOk Impl.AesEcb.Arm.encrypt 24 := by
  lit_decide

theorem ecbDecrypt_code : CodeOk Impl.AesEcb.Arm.decrypt 24 := by
  lit_decide

theorem cbcEncrypt_code : CodeOk Impl.AesCbc.Arm.Wiped.encrypt 32 := by
  lit_decide

theorem cbcDecrypt_code : CodeOk Impl.AesCbc.Arm.Wiped.decrypt 32 := by
  lit_decide

theorem ctr_code : CodeOk Impl.AesCtr.Arm.crypt 8 := by
  lit_decide

theorem ctrFinal_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 72 2 14 Impl.AesCtr.Arm.cryptFinal) 88 := by
  lit_decide

theorem cfbEncrypt_code : CodeOk Impl.AesCfb.Arm.encrypt 8 := by
  lit_decide

theorem cfbDecrypt_code : CodeOk Impl.AesCfb.Arm.decrypt 8 := by
  lit_decide

theorem cfbEncryptFinal_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 56 2 10 Impl.AesCfb.Arm.encryptFinal) 72 := by
  lit_decide

theorem cfbDecryptFinal_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 56 2 10 Impl.AesCfb.Arm.decryptFinal) 72 := by
  lit_decide

theorem cfb8Encrypt_code : CodeOk Impl.AesCfb8.Arm.encrypt 8 := by
  lit_decide

theorem cfb8Decrypt_code : CodeOk Impl.AesCfb8.Arm.decrypt 8 := by
  lit_decide

theorem ofb_code : CodeOk Impl.AesOfb.Arm.crypt 8 := by
  lit_decide

theorem ofbFinal_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 56 2 10 Impl.AesOfb.Arm.cryptFinal) 72 := by
  lit_decide

theorem xtsEncrypt_code : CodeOk Impl.AesXts.ArmUnit.encrypt 16 := by
  lit_decide

theorem xtsDecrypt_code : CodeOk Impl.AesXts.ArmUnit.decrypt 16 := by
  lit_decide

end VG.Proof.Aes.Arm.Scrub

namespace VG.Proof.Aes.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_aes_expand_key`. -/
theorem expandKey : VerifiedScrubbed target Impl.Aes.Arm.Fn.expandKey (Spec.Aes.expandKeyContract abi 512) 0 :=
  verifiedScrubbedF (api := Spec.Aes.expandKeyApi)
    { code := Impl.StackScratch.Arm.withRegScratchWiped 512 .r3 128 Impl.Aes.Arm.expandKey
      verified := Proof.Aes.Arm.expandKey_framed }
    (Scrub.expandKeyOut _) (scrubSideF_of Scrub.expandKey_code Scrub.frameOk_512 _)

/-- `vg_aes_ecb_encrypt`. -/
theorem ecbEncrypt : VerifiedScrubbed target Impl.Aes.Arm.Fn.ecbEncrypt (Spec.AesEcb.encryptContract abi 24) 0 :=
  verifiedScrubbedF (api := Spec.AesEcb.encryptApi)
    { code := Impl.AesEcb.Arm.encrypt
      verified := Proof.AesEcb.Arm.encrypt_verified }
    (Scrub.Ecb.encryptOut _) (scrubSideF_of Scrub.ecbEncrypt_code Scrub.frameOk_24 _)

/-- `vg_aes_ecb_decrypt`. -/
theorem ecbDecrypt : VerifiedScrubbed target Impl.Aes.Arm.Fn.ecbDecrypt (Spec.AesEcb.decryptContract abi 24) 0 :=
  verifiedScrubbedF (api := Spec.AesEcb.decryptApi)
    { code := Impl.AesEcb.Arm.decrypt
      verified := Proof.AesEcb.Arm.decrypt_verified }
    (Scrub.Ecb.decryptOut _) (scrubSideF_of Scrub.ecbDecrypt_code Scrub.frameOk_24 _)

/-- `vg_aes_cbc_encrypt`. -/
theorem cbcEncrypt : VerifiedScrubbed target Impl.Aes.Arm.Fn.cbcEncrypt (Spec.Cbc.aesEncryptContract abi 32) 0 :=
  verifiedScrubbedF (api := Spec.Cbc.aesEncryptApi)
    { code := Impl.AesCbc.Arm.Wiped.encrypt
      verified := Proof.AesCbc.Arm.Wiped.encrypt_verified }
    (Scrub.Cbc.encryptOut _) (scrubSideF_of Scrub.cbcEncrypt_code Scrub.frameOk_32 _)

/-- `vg_aes_cbc_decrypt`. -/
theorem cbcDecrypt : VerifiedScrubbed target Impl.Aes.Arm.Fn.cbcDecrypt (Spec.Cbc.aesDecryptContract abi 32) 0 :=
  verifiedScrubbedF (api := Spec.Cbc.aesDecryptApi)
    { code := Impl.AesCbc.Arm.Wiped.decrypt
      verified := Proof.AesCbc.Arm.Wiped.decrypt_verified }
    (Scrub.Cbc.decryptOut _) (scrubSideF_of Scrub.cbcDecrypt_code Scrub.frameOk_32 _)

/-- `vg_aes_ctr`. -/
theorem ctr : VerifiedScrubbed target Impl.Aes.Arm.Fn.ctr (Spec.Ctr.aesContract abi 8) 0 :=
  verifiedScrubbedF (api := Spec.Ctr.aesApi)
    { code := Impl.AesCtr.Arm.crypt
      verified := Proof.AesCtr.keyed Proof.AesCtr.Arm.crypt_verified }
    (Scrub.ctrOut _) (scrubSideF_of Scrub.ctr_code Scrub.frameOk_8 _)

/-- `vg_aes_ctr_final`. -/
theorem ctrFinal : VerifiedScrubbed target Impl.Aes.Arm.Fn.ctrFinal (Spec.Ctr.aesFinalContract abi 88) 0 :=
  verifiedScrubbedF (api := Spec.Ctr.aesFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 72 2 14 Impl.AesCtr.Arm.cryptFinal
      verified := Proof.AesCtr.final_keyed Proof.AesCtr.Arm.cryptFinal_framed }
    (Scrub.ctrFinalOut _) (scrubSideF_of Scrub.ctrFinal_code Scrub.frameOk_88 _)

/-- `vg_aes_cfb128_encrypt`. -/
theorem cfbEncrypt : VerifiedScrubbed target Impl.Aes.Arm.Fn.cfbEncrypt (Spec.Cfb.aesEncryptContract abi 8) 0 :=
  verifiedScrubbedF (api := Spec.Cfb.aesEncryptApi)
    { code := Impl.AesCfb.Arm.encrypt
      verified := Proof.AesCfb.encrypt_keyed Proof.AesCfb.Arm.encrypt_verified }
    (Scrub.cfbEncryptOut _) (scrubSideF_of Scrub.cfbEncrypt_code Scrub.frameOk_8 _)

/-- `vg_aes_cfb128_decrypt`. -/
theorem cfbDecrypt : VerifiedScrubbed target Impl.Aes.Arm.Fn.cfbDecrypt (Spec.Cfb.aesDecryptContract abi 8) 0 :=
  verifiedScrubbedF (api := Spec.Cfb.aesDecryptApi)
    { code := Impl.AesCfb.Arm.decrypt
      verified := Proof.AesCfb.decrypt_keyed Proof.AesCfb.Arm.decrypt_verified }
    (Scrub.cfbDecryptOut _) (scrubSideF_of Scrub.cfbDecrypt_code Scrub.frameOk_8 _)

/-- `vg_aes_cfb128_encrypt_final`. -/
theorem cfbEncryptFinal : VerifiedScrubbed target Impl.Aes.Arm.Fn.cfbEncryptFinal (Spec.Cfb.aesEncryptFinalContract abi 72) 0 :=
  verifiedScrubbedF (api := Spec.Cfb.aesEncryptFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 56 2 10 Impl.AesCfb.Arm.encryptFinal
      verified := Proof.AesCfb.encryptFinal_keyed Proof.AesCfb.Arm.encryptFinal_framed }
    (Scrub.cfbEncryptFinalOut _) (scrubSideF_of Scrub.cfbEncryptFinal_code Scrub.frameOk_72 _)

/-- `vg_aes_cfb128_decrypt_final`. -/
theorem cfbDecryptFinal : VerifiedScrubbed target Impl.Aes.Arm.Fn.cfbDecryptFinal (Spec.Cfb.aesDecryptFinalContract abi 72) 0 :=
  verifiedScrubbedF (api := Spec.Cfb.aesDecryptFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 56 2 10 Impl.AesCfb.Arm.decryptFinal
      verified := Proof.AesCfb.decryptFinal_keyed Proof.AesCfb.Arm.decryptFinal_framed }
    (Scrub.cfbDecryptFinalOut _) (scrubSideF_of Scrub.cfbDecryptFinal_code Scrub.frameOk_72 _)

/-- `vg_aes_cfb8_encrypt`. -/
theorem cfb8Encrypt : VerifiedScrubbed target Impl.Aes.Arm.Fn.cfb8Encrypt (Spec.Cfb8.aesEncryptContract abi 8) 0 :=
  verifiedScrubbedF (api := Spec.Cfb8.aesEncryptApi)
    { code := Impl.AesCfb8.Arm.encrypt
      verified := Proof.AesCfb8.encrypt_keyed Proof.AesCfb8.Arm.encrypt_verified }
    (Scrub.cfb8EncryptOut _) (scrubSideF_of Scrub.cfb8Encrypt_code Scrub.frameOk_8 _)

/-- `vg_aes_cfb8_decrypt`. -/
theorem cfb8Decrypt : VerifiedScrubbed target Impl.Aes.Arm.Fn.cfb8Decrypt (Spec.Cfb8.aesDecryptContract abi 8) 0 :=
  verifiedScrubbedF (api := Spec.Cfb8.aesDecryptApi)
    { code := Impl.AesCfb8.Arm.decrypt
      verified := Proof.AesCfb8.decrypt_keyed Proof.AesCfb8.Arm.decrypt_verified }
    (Scrub.cfb8DecryptOut _) (scrubSideF_of Scrub.cfb8Decrypt_code Scrub.frameOk_8 _)

/-- `vg_aes_ofb`. -/
theorem ofb : VerifiedScrubbed target Impl.Aes.Arm.Fn.ofb (Spec.Ofb.aesContract abi 8) 0 :=
  verifiedScrubbedF (api := Spec.Ofb.aesApi)
    { code := Impl.AesOfb.Arm.crypt
      verified := Proof.AesOfb.keyed Proof.AesOfb.Arm.crypt_verified }
    (Scrub.ofbOut _) (scrubSideF_of Scrub.ofb_code Scrub.frameOk_8 _)

/-- `vg_aes_ofb_final`. -/
theorem ofbFinal : VerifiedScrubbed target Impl.Aes.Arm.Fn.ofbFinal (Spec.Ofb.aesFinalContract abi 72) 0 :=
  verifiedScrubbedF (api := Spec.Ofb.aesFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 56 2 10 Impl.AesOfb.Arm.cryptFinal
      verified := Proof.AesOfb.final_keyed Proof.AesOfb.Arm.cryptFinal_framed }
    (Scrub.ofbFinalOut _) (scrubSideF_of Scrub.ofbFinal_code Scrub.frameOk_72 _)

/-- `vg_aes_xts_encrypt_unit`. -/
theorem xtsEncrypt : VerifiedScrubbed target Impl.Aes.Arm.Fn.xtsEncrypt (Spec.Xts.aesEncryptUnitContract abi 16) 0 :=
  verifiedScrubbedF (api := Spec.Xts.aesEncryptUnitApi)
    { code := Impl.AesXts.ArmUnit.encrypt
      verified := Proof.AesXts.Arm.Unit.encrypt_verified }
    (Scrub.xtsEncryptUnitOut _) (scrubSideF_of Scrub.xtsEncrypt_code Scrub.frameOk_16 _)

/-- `vg_aes_xts_decrypt_unit`. -/
theorem xtsDecrypt : VerifiedScrubbed target Impl.Aes.Arm.Fn.xtsDecrypt (Spec.Xts.aesDecryptUnitContract abi 16) 0 :=
  verifiedScrubbedF (api := Spec.Xts.aesDecryptUnitApi)
    { code := Impl.AesXts.ArmUnit.decrypt
      verified := Proof.AesXts.Arm.Unit.decrypt_verified }
    (Scrub.xtsDecryptUnitOut _) (scrubSideF_of Scrub.xtsDecrypt_code Scrub.frameOk_16 _)

end VG.Proof.Aes.Arm.Fn
