module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Aes.RISCV64.Fn
public import VerifiedGarbage.Proof.Aes.RISCV64.Frame
public import VerifiedGarbage.Proof.AesEcb.RISCV64
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Wiped
public import VerifiedGarbage.Proof.AesCtr.RISCV64.Verified
public import VerifiedGarbage.Proof.AesCtr.RISCV64.Final
public import VerifiedGarbage.Proof.AesCfb.RISCV64.Verified
public import VerifiedGarbage.Proof.AesCfb.RISCV64.Final
public import VerifiedGarbage.Proof.AesCfb8.RISCV64.Verified
public import VerifiedGarbage.Proof.AesOfb.RISCV64.Verified
public import VerifiedGarbage.Proof.AesOfb.RISCV64.Final
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Aes.Scratch
import VerifiedGarbage.Proof.AesEcb.Wipe
import VerifiedGarbage.Proof.AesCbc.Wipe
import VerifiedGarbage.Proof.Framework.Omega

meta import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Impl.Aes.RISCV64.Fn
meta import VerifiedGarbage.Proof.Aes.RISCV64.Frame
meta import VerifiedGarbage.Proof.AesEcb.RISCV64
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.Wiped
meta import VerifiedGarbage.Proof.AesCtr.RISCV64.Verified
meta import VerifiedGarbage.Proof.AesCtr.RISCV64.Final
meta import VerifiedGarbage.Proof.AesCfb.RISCV64.Verified
meta import VerifiedGarbage.Proof.AesCfb.RISCV64.Final
meta import VerifiedGarbage.Proof.AesCfb8.RISCV64.Verified
meta import VerifiedGarbage.Proof.AesOfb.RISCV64.Verified
meta import VerifiedGarbage.Proof.AesOfb.RISCV64.Final
meta import VerifiedGarbage.Proof.Aes.ScrubLocal
meta import VerifiedGarbage.Proof.Aes.Scratch
meta import VerifiedGarbage.Proof.AesEcb.Wipe
meta import VerifiedGarbage.Proof.AesCbc.Wipe
meta import VerifiedGarbage.Proof.Framework.Omega
/-!
# AES and its modes on RISC-V, without secret residue

`vg_aes_expand_key`, `vg_aes_ecb_encrypt`, `vg_aes_ecb_decrypt`,
`vg_aes_cbc_encrypt`, `vg_aes_cbc_decrypt`, `vg_aes_ctr`,
`vg_aes_ctr_final`, `vg_aes_cfb128_encrypt`, `vg_aes_cfb128_decrypt`, their
`_final` functions, `vg_aes_cfb8_encrypt`, `vg_aes_cfb8_decrypt`,
`vg_aes_ofb` and `vg_aes_ofb_final`, as emitted (`Impl.Aes.RISCV64.Fn`):
each function followed by `Impl.Scrub.RISCV64.scrubTail`, which clears the
caller-saved registers and the stack its frames used. Each theorem below
states that one meets its contract in constant time and returns without
secret residue (`VerifiedScrubbed`, by `RISCV64.Scrub.verifiedScrubbedAll`),
which is what its registration binds. Their postconditions
read the memory on return only within their buffers
(`RISCV64.Scrub.PostOut`), as on x86-64 (`Proof/Aes/X86_64/Scrub.lean`,
`Proof/AesEcb/X86_64.lean`, `Proof/AesCbc/X86_64/Wiped.lean`,
`Proof/Aes/X86_64/ModesScrub.lean`, `Proof/Aes/X86_64/FinalScrub.lean`).
The `_final` functions call the code of the whole-block ones as internal
functions of their own, `vg_aes_ctr_core`, ….

The key expansion and the final partial-block functions of CTR, CFB and OFB instead clear only the runs of doublewords that the residue
analysis (`RISCV64.rtaint`) finds may differ between two runs
(`Impl.Scrub.RISCV64.scrubSel`, `RISCV64.Scrub.verifiedScrubbedSel`, whose
analysis the kernel evaluates here). Their code wipes its own scratch space,
which leaves no such doubleword.
-/

@[expose] public section

namespace VG.Proof.Aes.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub VG.Proof.Aes.ScrubLocal

/-! ## Postconditions -/

theorem expandKeyOut (stack : Nat) :
    PostOut (Spec.Aes.expandKeyContract RISCV64.abi stack) (Spec.Aes.expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Aes.expandKeyPostOut_local _)

theorem len_le (x : BitVec 64) (k : Nat) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat * k ≤ x.toNat * k :=
  Nat.le_refl _

theorem len_le1 (x : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size :=
  Nat.le_of_eq (Nat.mul_one _).symm

/-- The postcondition of `vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt` reads the
memory on return only within the buffers. -/
theorem ecbOut (g : List Byte → Spec.Aes.State → Spec.Aes.State) (w stack : Nat) :
    PostOut (Proof.AesEcb.wipedContract g w abi stack) (Spec.Aes.blocksSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.AesEcb.ecbPost_out _ g w)

/-- The postcondition of `vg_aes_cbc_encrypt` reads the memory on return only
within the buffers. -/
theorem cbcEncryptOut (S : Nat → Bool) (stack : Nat) :
    PostOut (Proof.AesCbc.Wipe.wipedContract Proof.AesCbc.Wipe.encPost S abi stack) (Spec.Cbc.aesSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.AesCbc.Wipe.wipedPost_ret _ _ S (Proof.AesCbc.Wipe.encPost_ret _))

/-- The postcondition of `vg_aes_cbc_decrypt` reads the memory on return only
within the buffers. -/
theorem cbcDecryptOut (S : Nat → Bool) (stack : Nat) :
    PostOut (Proof.AesCbc.Wipe.wipedContract Proof.AesCbc.Wipe.decPost S abi stack) (Spec.Cbc.aesSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.AesCbc.Wipe.wipedPost_ret _ _ S (Proof.AesCbc.Wipe.decPost_ret _))

theorem cfb8EncryptOut (stack : Nat) :
    PostOut (Spec.Cfb8.aesEncryptContract RISCV64.abi stack) (Spec.Cfb8.aesSig.retBits 64) :=
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
    PostOut (Spec.Cfb8.aesDecryptContract RISCV64.abi stack) (Spec.Cfb8.aesSig.retBits 64) :=
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
    PostOut (Spec.Cfb.aesEncryptContract RISCV64.abi stack) (Spec.Cfb.aesSig.retBits 64) :=
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
    PostOut (Spec.Cfb.aesDecryptContract RISCV64.abi stack) (Spec.Cfb.aesSig.retBits 64) :=
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
    PostOut (Spec.Ofb.aesContract RISCV64.abi stack) (Spec.Ofb.aesSig.retBits 64) :=
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
    PostOut (Spec.Ctr.aesContract RISCV64.abi stack) (Spec.Ctr.aesSig.retBits 64) :=
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
    PostOut (Spec.Ctr.aesFinalContract RISCV64.abi stack) (Spec.Ctr.aesFinalSig.retBits 64) :=
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
    PostOut (Spec.Cfb.aesEncryptFinalContract RISCV64.abi stack) (Spec.Cfb.aesFinalSig.retBits 64) :=
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
    PostOut (Spec.Cfb.aesDecryptFinalContract RISCV64.abi stack) (Spec.Cfb.aesFinalSig.retBits 64) :=
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
    PostOut (Spec.Ofb.aesFinalContract RISCV64.abi stack) (Spec.Ofb.aesFinalSig.retBits 64) :=
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

/-- `vg_aes_expand_key` as emitted (`Impl.Aes.RISCV64.Fn.expandKey`) meets its contract in
constant time and returns without secret residue. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed target Impl.Aes.RISCV64.Fn.expandKey (Spec.Aes.expandKeyContract RISCV64.abi 512) 0 :=
  verifiedScrubbedSel (api := Spec.Aes.expandKeyApi) (W := 512)
    { code := Impl.StackScratch.RISCV64.withStackScratchWiped 512 .a3 64 Impl.Aes.RISCV64.expandKey
      verified := Proof.Aes.RISCV64.expandKey_framed }
    [] [] (expandKeyOut _) (by lit_decide) (hbp_nil _) ⟨_, by taint_decide_ct⟩

/-- `vg_aes_ecb_encrypt` as emitted (`Impl.Aes.RISCV64.Fn.ecbEncrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem ecbEncrypt_wipes :
    VerifiedScrubbed target Impl.Aes.RISCV64.Fn.ecbEncrypt (Proof.AesEcb.wipedContract Proof.AesEcb.enc 2048 RISCV64.abi 32) 0 :=
  verifiedScrubbedAll (api := Proof.AesEcb.wipedApi Proof.AesEcb.enc 2048)
    { code := Proof.AesEcb.RISCV64.encrypt
      verified := Proof.AesEcb.RISCV64.encrypt_verified }
    (ecbOut _ _ _) (by lit_decide)

theorem ecbEncrypt_scrubbed :
    VerifiedScrubbed target Impl.Aes.RISCV64.Fn.ecbEncrypt (Spec.AesEcb.encryptContract RISCV64.abi 32) 0 :=
  Proof.AesEcb.encrypt_imp ecbEncrypt_wipes id

theorem ecbEncrypt_public :
    Spec.AesEcb.scratchOut.Of abi Impl.Aes.RISCV64.Fn.ecbEncrypt (Spec.AesEcb.encryptContract RISCV64.abi 32) :=
  Proof.AesEcb.scratch_public ecbEncrypt_wipes

/-- `vg_aes_ecb_decrypt` as emitted (`Impl.Aes.RISCV64.Fn.ecbDecrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem ecbDecrypt_wipes :
    VerifiedScrubbed target Impl.Aes.RISCV64.Fn.ecbDecrypt (Proof.AesEcb.wipedContract Proof.AesEcb.dec 2048 RISCV64.abi 32) 0 :=
  verifiedScrubbedAll (api := Proof.AesEcb.wipedApi Proof.AesEcb.dec 2048)
    { code := Proof.AesEcb.RISCV64.decrypt
      verified := Proof.AesEcb.RISCV64.decrypt_verified }
    (ecbOut _ _ _) (by lit_decide)

theorem ecbDecrypt_scrubbed :
    VerifiedScrubbed target Impl.Aes.RISCV64.Fn.ecbDecrypt (Spec.AesEcb.decryptContract RISCV64.abi 32) 0 :=
  Proof.AesEcb.decrypt_imp ecbDecrypt_wipes id

theorem ecbDecrypt_public :
    Spec.AesEcb.scratchOut.Of abi Impl.Aes.RISCV64.Fn.ecbDecrypt (Spec.AesEcb.decryptContract RISCV64.abi 32) :=
  Proof.AesEcb.scratch_public ecbDecrypt_wipes

/-- `vg_aes_cbc_encrypt` as emitted (`Impl.Aes.RISCV64.Fn.cbcEncrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cbcEncrypt_wipes :
    VerifiedScrubbed target Impl.Aes.RISCV64.Fn.cbcEncrypt (Proof.AesCbc.Wipe.wipedContract Proof.AesCbc.Wipe.encPost (fun i => decide (i < 2176)) RISCV64.abi 32) 0 :=
  verifiedScrubbedAll (api := Proof.AesCbc.Wipe.wipedApi Proof.AesCbc.Wipe.encPost (fun i => decide (i < 2176)))
    { code := Proof.AesCbc.RISCV64.Wiped.encrypt
      verified := Proof.AesCbc.RISCV64.Wiped.encrypt_verified }
    (cbcEncryptOut _ _) (by lit_decide)

theorem cbcEncrypt_scrubbed :
    VerifiedScrubbed target Impl.Aes.RISCV64.Fn.cbcEncrypt (Spec.Cbc.aesEncryptContract RISCV64.abi 32) 0 :=
  Proof.AesCbc.Wipe.encrypt_imp cbcEncrypt_wipes id

theorem cbcEncrypt_public :
    Spec.Cbc.aesScratchOut.Of abi Impl.Aes.RISCV64.Fn.cbcEncrypt (Spec.Cbc.aesEncryptContract RISCV64.abi 32) :=
  Proof.AesCbc.Wipe.scratch_public cbcEncrypt_wipes

/-- `vg_aes_cbc_decrypt` as emitted (`Impl.Aes.RISCV64.Fn.cbcDecrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cbcDecrypt_wipes :
    VerifiedScrubbed target Impl.Aes.RISCV64.Fn.cbcDecrypt (Proof.AesCbc.Wipe.wipedContract Proof.AesCbc.Wipe.decPost (fun i => decide (i < 2176)) RISCV64.abi 32) 0 :=
  verifiedScrubbedAll (api := Proof.AesCbc.Wipe.wipedApi Proof.AesCbc.Wipe.decPost (fun i => decide (i < 2176)))
    { code := Proof.AesCbc.RISCV64.Wiped.decrypt
      verified := Proof.AesCbc.RISCV64.Wiped.decrypt_verified }
    (cbcDecryptOut _ _) (by lit_decide)

theorem cbcDecrypt_scrubbed :
    VerifiedScrubbed target Impl.Aes.RISCV64.Fn.cbcDecrypt (Spec.Cbc.aesDecryptContract RISCV64.abi 32) 0 :=
  Proof.AesCbc.Wipe.decrypt_imp cbcDecrypt_wipes id

theorem cbcDecrypt_public :
    Spec.Cbc.aesScratchOut.Of abi Impl.Aes.RISCV64.Fn.cbcDecrypt (Spec.Cbc.aesDecryptContract RISCV64.abi 32) :=
  Proof.AesCbc.Wipe.scratch_public cbcDecrypt_wipes

/-- `vg_aes_ctr` as emitted (`Impl.Aes.RISCV64.Fn.ctr`) meets its contract in
constant time and returns without secret residue. -/
theorem ctr_scrubbed :
    VerifiedScrubbed target Impl.Aes.RISCV64.Fn.ctr (Spec.Ctr.aesContract RISCV64.abi) 0 :=
  verifiedScrubbedAll (api := Spec.Ctr.aesApi)
    { code := Impl.AesCtr.RISCV64.crypt
      verified := Proof.AesCtr.keyed Proof.AesCtr.RISCV64.crypt_verified }
    (ctrOut _) (by lit_decide)

/-- `vg_aes_ctr_final` as emitted (`Impl.Aes.RISCV64.Fn.ctrFinal`) meets its contract in
constant time and returns without secret residue. -/
theorem ctrFinal_scrubbed :
    VerifiedScrubbed target Impl.Aes.RISCV64.Fn.ctrFinal (Spec.Ctr.aesFinalContract RISCV64.abi 80) 0 :=
  verifiedScrubbedSel (api := Spec.Ctr.aesFinalApi) (W := 80)
    { code := Impl.StackScratch.RISCV64.withStackScratchWiped 80 .a6 10 Impl.AesCtr.RISCV64.cryptFinal
      verified := Proof.AesCtr.final_keyed Proof.AesCtr.RISCV64.Final.cryptFinal_framed }
    [] [] (ctrFinalOut _) (by lit_decide) (hbp_nil _) ⟨_, by taint_decide_ct⟩

/-- `vg_aes_cfb128_encrypt` as emitted (`Impl.Aes.RISCV64.Fn.cfbEncrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed target Impl.Aes.RISCV64.Fn.cfbEncrypt (Spec.Cfb.aesEncryptContract RISCV64.abi) 0 :=
  verifiedScrubbedAll (api := Spec.Cfb.aesEncryptApi)
    { code := Impl.AesCfb.RISCV64.encrypt
      verified := Proof.AesCfb.encrypt_keyed Proof.AesCfb.RISCV64.encrypt_verified }
    (cfbEncryptOut _) (by lit_decide)

/-- `vg_aes_cfb128_decrypt` as emitted (`Impl.Aes.RISCV64.Fn.cfbDecrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed target Impl.Aes.RISCV64.Fn.cfbDecrypt (Spec.Cfb.aesDecryptContract RISCV64.abi) 0 :=
  verifiedScrubbedAll (api := Spec.Cfb.aesDecryptApi)
    { code := Impl.AesCfb.RISCV64.decrypt
      verified := Proof.AesCfb.decrypt_keyed Proof.AesCfb.RISCV64.decrypt_verified }
    (cfbDecryptOut _) (by lit_decide)

/-- `vg_aes_cfb128_encrypt_final` as emitted (`Impl.Aes.RISCV64.Fn.cfbEncryptFinal`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed target Impl.Aes.RISCV64.Fn.cfbEncryptFinal (Spec.Cfb.aesEncryptFinalContract RISCV64.abi 64) 0 :=
  verifiedScrubbedSel (api := Spec.Cfb.aesEncryptFinalApi) (W := 64)
    { code := Impl.StackScratch.RISCV64.withStackScratchWiped 64 .a6 8 Impl.AesCfb.RISCV64.encryptFinal
      verified := Proof.AesCfb.encryptFinal_keyed Proof.AesCfb.RISCV64.Final.encryptFinal_framed }
    [] [] (cfbEncryptFinalOut _) (by lit_decide) (hbp_nil _) ⟨_, by taint_decide_ct⟩

/-- `vg_aes_cfb128_decrypt_final` as emitted (`Impl.Aes.RISCV64.Fn.cfbDecryptFinal`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed target Impl.Aes.RISCV64.Fn.cfbDecryptFinal (Spec.Cfb.aesDecryptFinalContract RISCV64.abi 64) 0 :=
  verifiedScrubbedSel (api := Spec.Cfb.aesDecryptFinalApi) (W := 64)
    { code := Impl.StackScratch.RISCV64.withStackScratchWiped 64 .a6 8 Impl.AesCfb.RISCV64.decryptFinal
      verified := Proof.AesCfb.decryptFinal_keyed Proof.AesCfb.RISCV64.Final.decryptFinal_framed }
    [] [] (cfbDecryptFinalOut _) (by lit_decide) (hbp_nil _) ⟨_, by taint_decide_ct⟩

/-- `vg_aes_cfb8_encrypt` as emitted (`Impl.Aes.RISCV64.Fn.cfb8Encrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cfb8Encrypt_scrubbed :
    VerifiedScrubbed target Impl.Aes.RISCV64.Fn.cfb8Encrypt (Spec.Cfb8.aesEncryptContract RISCV64.abi) 0 :=
  verifiedScrubbedAll (api := Spec.Cfb8.aesEncryptApi)
    { code := Impl.AesCfb8.RISCV64.encrypt
      verified := Proof.AesCfb8.encrypt_keyed Proof.AesCfb8.RISCV64.encrypt_verified }
    (cfb8EncryptOut _) (by lit_decide)

/-- `vg_aes_cfb8_decrypt` as emitted (`Impl.Aes.RISCV64.Fn.cfb8Decrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cfb8Decrypt_scrubbed :
    VerifiedScrubbed target Impl.Aes.RISCV64.Fn.cfb8Decrypt (Spec.Cfb8.aesDecryptContract RISCV64.abi) 0 :=
  verifiedScrubbedAll (api := Spec.Cfb8.aesDecryptApi)
    { code := Impl.AesCfb8.RISCV64.decrypt
      verified := Proof.AesCfb8.decrypt_keyed Proof.AesCfb8.RISCV64.decrypt_verified }
    (cfb8DecryptOut _) (by lit_decide)

/-- `vg_aes_ofb` as emitted (`Impl.Aes.RISCV64.Fn.ofb`) meets its contract in
constant time and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed target Impl.Aes.RISCV64.Fn.ofb (Spec.Ofb.aesContract RISCV64.abi) 0 :=
  verifiedScrubbedAll (api := Spec.Ofb.aesApi)
    { code := Impl.AesOfb.RISCV64.crypt
      verified := Proof.AesOfb.keyed Proof.AesOfb.RISCV64.crypt_verified }
    (ofbOut _) (by lit_decide)

/-- `vg_aes_ofb_final` as emitted (`Impl.Aes.RISCV64.Fn.ofbFinal`) meets its contract in
constant time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed target Impl.Aes.RISCV64.Fn.ofbFinal (Spec.Ofb.aesFinalContract RISCV64.abi 64) 0 :=
  verifiedScrubbedSel (api := Spec.Ofb.aesFinalApi) (W := 64)
    { code := Impl.StackScratch.RISCV64.withStackScratchWiped 64 .a6 8 Impl.AesOfb.RISCV64.cryptFinal
      verified := Proof.AesOfb.final_keyed Proof.AesOfb.RISCV64.cryptFinal_framed }
    [] [] (ofbFinalOut _) (by lit_decide) (hbp_nil _) ⟨_, by taint_decide_ct⟩

end VG.Proof.Aes.RISCV64.Scrub
