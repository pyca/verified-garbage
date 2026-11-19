module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
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
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Framework.Registration
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
`Proof/AesXts/RISCV64/Scrub.lean`). Each is registered followed by a wipe of
that stack and by instructions that set the registers a callee may change,
but the result, and the flags to constants (`Arm.Scrub.scrubRegF`).

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
    armStack (Impl.StackScratch.Arm.withRegScratchWiped 512 .r3 128 Impl.Aes.Arm.expandKey) ≤ 512 ∧
      noIcall (Impl.StackScratch.Arm.withRegScratchWiped 512 .r3 128 Impl.Aes.Arm.expandKey) = true := by
  lit_decide

theorem ecbEncrypt_code : armStack Proof.AesEcb.Arm.encrypt ≤ 24 ∧ noIcall Proof.AesEcb.Arm.encrypt = true := by
  lit_decide

theorem ecbDecrypt_code : armStack Proof.AesEcb.Arm.decrypt ≤ 24 ∧ noIcall Proof.AesEcb.Arm.decrypt = true := by
  lit_decide

theorem cbcEncrypt_code :
    armStack Proof.AesCbc.Arm.Wiped.encrypt ≤ 32 ∧ noIcall Proof.AesCbc.Arm.Wiped.encrypt = true := by
  lit_decide

theorem cbcDecrypt_code :
    armStack Proof.AesCbc.Arm.Wiped.decrypt ≤ 32 ∧ noIcall Proof.AesCbc.Arm.Wiped.decrypt = true := by
  lit_decide

theorem ctr_code : armStack Impl.AesCtr.Arm.crypt ≤ 8 ∧ noIcall Impl.AesCtr.Arm.crypt = true := by
  lit_decide

theorem ctrFinal_code :
    armStack (Impl.StackScratch.Arm.withStackScratchWiped 72 2 14 Impl.AesCtr.Arm.cryptFinal) ≤ 88 ∧
      noIcall (Impl.StackScratch.Arm.withStackScratchWiped 72 2 14 Impl.AesCtr.Arm.cryptFinal) = true := by
  lit_decide

theorem cfbEncrypt_code : armStack Impl.AesCfb.Arm.encrypt ≤ 8 ∧ noIcall Impl.AesCfb.Arm.encrypt = true := by
  lit_decide

theorem cfbDecrypt_code : armStack Impl.AesCfb.Arm.decrypt ≤ 8 ∧ noIcall Impl.AesCfb.Arm.decrypt = true := by
  lit_decide

theorem cfbEncryptFinal_code :
    armStack (Impl.StackScratch.Arm.withStackScratchWiped 56 2 10 Impl.AesCfb.Arm.encryptFinal) ≤ 72 ∧
      noIcall (Impl.StackScratch.Arm.withStackScratchWiped 56 2 10 Impl.AesCfb.Arm.encryptFinal) = true := by
  lit_decide

theorem cfbDecryptFinal_code :
    armStack (Impl.StackScratch.Arm.withStackScratchWiped 56 2 10 Impl.AesCfb.Arm.decryptFinal) ≤ 72 ∧
      noIcall (Impl.StackScratch.Arm.withStackScratchWiped 56 2 10 Impl.AesCfb.Arm.decryptFinal) = true := by
  lit_decide

theorem cfb8Encrypt_code : armStack Impl.AesCfb8.Arm.encrypt ≤ 8 ∧ noIcall Impl.AesCfb8.Arm.encrypt = true := by
  lit_decide

theorem cfb8Decrypt_code : armStack Impl.AesCfb8.Arm.decrypt ≤ 8 ∧ noIcall Impl.AesCfb8.Arm.decrypt = true := by
  lit_decide

theorem ofb_code : armStack Impl.AesOfb.Arm.crypt ≤ 8 ∧ noIcall Impl.AesOfb.Arm.crypt = true := by
  lit_decide

theorem ofbFinal_code :
    armStack (Impl.StackScratch.Arm.withStackScratchWiped 56 2 10 Impl.AesOfb.Arm.cryptFinal) ≤ 72 ∧
      noIcall (Impl.StackScratch.Arm.withStackScratchWiped 56 2 10 Impl.AesOfb.Arm.cryptFinal) = true := by
  lit_decide

theorem xtsEncrypt_code : armStack Impl.AesXts.ArmUnit.encrypt ≤ 16 ∧ noIcall Impl.AesXts.ArmUnit.encrypt = true := by
  lit_decide

theorem xtsDecrypt_code : armStack Impl.AesXts.ArmUnit.decrypt ≤ 16 ∧ noIcall Impl.AesXts.ArmUnit.decrypt = true := by
  lit_decide

/-! ## The registrations -/

/-- `vg_aes_expand_key`. -/
def expandKeyReg : Registration Spec.Aes.expandKeyApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withRegScratchWiped 512 .r3 128 Impl.Aes.Arm.expandKey
      verified := Proof.Aes.Arm.expandKey_framed }
    expandKey_code.1 expandKey_code.2 frameOk_512 (expandKeyOut _) rfl

/-- `vg_aes_ecb_encrypt`. -/
def ecbEncryptReg : Registration Spec.AesEcb.encryptApi Arm.target :=
  scrubRegF {
      code := Proof.AesEcb.Arm.encrypt
      verified := Proof.AesEcb.Arm.encrypt_verified }
    ecbEncrypt_code.1 ecbEncrypt_code.2 frameOk_24 (Ecb.encryptOut _) rfl

/-- `vg_aes_ecb_decrypt`. -/
def ecbDecryptReg : Registration Spec.AesEcb.decryptApi Arm.target :=
  scrubRegF {
      code := Proof.AesEcb.Arm.decrypt
      verified := Proof.AesEcb.Arm.decrypt_verified }
    ecbDecrypt_code.1 ecbDecrypt_code.2 frameOk_24 (Ecb.decryptOut _) rfl

/-- `vg_aes_cbc_encrypt`. -/
def cbcEncryptReg : Registration Spec.Cbc.aesEncryptApi Arm.target :=
  scrubRegF {
      code := Proof.AesCbc.Arm.Wiped.encrypt
      verified := Proof.AesCbc.Arm.Wiped.encrypt_verified }
    cbcEncrypt_code.1 cbcEncrypt_code.2 frameOk_32 (Cbc.encryptOut _) rfl

/-- `vg_aes_cbc_decrypt`. -/
def cbcDecryptReg : Registration Spec.Cbc.aesDecryptApi Arm.target :=
  scrubRegF {
      code := Proof.AesCbc.Arm.Wiped.decrypt
      verified := Proof.AesCbc.Arm.Wiped.decrypt_verified }
    cbcDecrypt_code.1 cbcDecrypt_code.2 frameOk_32 (Cbc.decryptOut _) rfl

/-- `vg_aes_ctr`. -/
def ctrReg : Registration Spec.Ctr.aesApi Arm.target :=
  scrubRegF {
      code := Impl.AesCtr.Arm.crypt
      verified := Proof.AesCtr.keyed Proof.AesCtr.Arm.crypt_verified }
    ctr_code.1 ctr_code.2 frameOk_8 (ctrOut _) rfl

/-- `vg_aes_ctr_final`. -/
def ctrFinalReg : Registration Spec.Ctr.aesFinalApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratchWiped 72 2 14 Impl.AesCtr.Arm.cryptFinal
      verified := Proof.AesCtr.final_keyed Proof.AesCtr.Arm.cryptFinal_framed }
    ctrFinal_code.1 ctrFinal_code.2 frameOk_88 (ctrFinalOut _) rfl

/-- `vg_aes_cfb128_encrypt`. -/
def cfbEncryptReg : Registration Spec.Cfb.aesEncryptApi Arm.target :=
  scrubRegF {
      code := Impl.AesCfb.Arm.encrypt
      verified := Proof.AesCfb.encrypt_keyed Proof.AesCfb.Arm.encrypt_verified }
    cfbEncrypt_code.1 cfbEncrypt_code.2 frameOk_8 (cfbEncryptOut _) rfl

/-- `vg_aes_cfb128_decrypt`. -/
def cfbDecryptReg : Registration Spec.Cfb.aesDecryptApi Arm.target :=
  scrubRegF {
      code := Impl.AesCfb.Arm.decrypt
      verified := Proof.AesCfb.decrypt_keyed Proof.AesCfb.Arm.decrypt_verified }
    cfbDecrypt_code.1 cfbDecrypt_code.2 frameOk_8 (cfbDecryptOut _) rfl

/-- `vg_aes_cfb128_encrypt_final`. -/
def cfbEncryptFinalReg : Registration Spec.Cfb.aesEncryptFinalApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratchWiped 56 2 10 Impl.AesCfb.Arm.encryptFinal
      verified := Proof.AesCfb.encryptFinal_keyed Proof.AesCfb.Arm.encryptFinal_framed }
    cfbEncryptFinal_code.1 cfbEncryptFinal_code.2 frameOk_72 (cfbEncryptFinalOut _) rfl

/-- `vg_aes_cfb128_decrypt_final`. -/
def cfbDecryptFinalReg : Registration Spec.Cfb.aesDecryptFinalApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratchWiped 56 2 10 Impl.AesCfb.Arm.decryptFinal
      verified := Proof.AesCfb.decryptFinal_keyed Proof.AesCfb.Arm.decryptFinal_framed }
    cfbDecryptFinal_code.1 cfbDecryptFinal_code.2 frameOk_72 (cfbDecryptFinalOut _) rfl

/-- `vg_aes_cfb8_encrypt`. -/
def cfb8EncryptReg : Registration Spec.Cfb8.aesEncryptApi Arm.target :=
  scrubRegF {
      code := Impl.AesCfb8.Arm.encrypt
      verified := Proof.AesCfb8.encrypt_keyed Proof.AesCfb8.Arm.encrypt_verified }
    cfb8Encrypt_code.1 cfb8Encrypt_code.2 frameOk_8 (cfb8EncryptOut _) rfl

/-- `vg_aes_cfb8_decrypt`. -/
def cfb8DecryptReg : Registration Spec.Cfb8.aesDecryptApi Arm.target :=
  scrubRegF {
      code := Impl.AesCfb8.Arm.decrypt
      verified := Proof.AesCfb8.decrypt_keyed Proof.AesCfb8.Arm.decrypt_verified }
    cfb8Decrypt_code.1 cfb8Decrypt_code.2 frameOk_8 (cfb8DecryptOut _) rfl

/-- `vg_aes_ofb`. -/
def ofbReg : Registration Spec.Ofb.aesApi Arm.target :=
  scrubRegF {
      code := Impl.AesOfb.Arm.crypt
      verified := Proof.AesOfb.keyed Proof.AesOfb.Arm.crypt_verified }
    ofb_code.1 ofb_code.2 frameOk_8 (ofbOut _) rfl

/-- `vg_aes_ofb_final`. -/
def ofbFinalReg : Registration Spec.Ofb.aesFinalApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratchWiped 56 2 10 Impl.AesOfb.Arm.cryptFinal
      verified := Proof.AesOfb.final_keyed Proof.AesOfb.Arm.cryptFinal_framed }
    ofbFinal_code.1 ofbFinal_code.2 frameOk_72 (ofbFinalOut _) rfl

/-- `vg_aes_xts_encrypt_unit`. -/
def xtsEncryptReg : Registration Spec.Xts.aesEncryptUnitApi Arm.target :=
  scrubRegF {
      code := Impl.AesXts.ArmUnit.encrypt
      verified := Proof.AesXts.Arm.Unit.encrypt_verified }
    xtsEncrypt_code.1 xtsEncrypt_code.2 frameOk_16 (xtsEncryptUnitOut _) rfl

/-- `vg_aes_xts_decrypt_unit`. -/
def xtsDecryptReg : Registration Spec.Xts.aesDecryptUnitApi Arm.target :=
  scrubRegF {
      code := Impl.AesXts.ArmUnit.decrypt
      verified := Proof.AesXts.Arm.Unit.decrypt_verified }
    xtsDecrypt_code.1 xtsDecrypt_code.2 frameOk_16 (xtsDecryptUnitOut _) rfl

end VG.Proof.Aes.Arm.Scrub
