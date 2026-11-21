module

public import VerifiedGarbage.Impl.Blowfish.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Blowfish.Contract
public import VerifiedGarbage.Spec.Blowfish.Cbc
public import VerifiedGarbage.Spec.Blowfish.Cfb
public import VerifiedGarbage.Spec.Blowfish.CfbFinal
public import VerifiedGarbage.Spec.Blowfish.Ofb
public import VerifiedGarbage.Spec.Blowfish.OfbFinal
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.Verified
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Blowfish.ScrubLocal
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Blowfish on PPC64LE, without secret residue

Key expansion and the CBC, CFB64 and OFB functions zero their whole frame
themselves before they release it (`withStackScratchWiped`), and have no
frames of their own inside it, so they need only the clearing of the
volatile registers after them (`PPC64LE.Scrub.verifiedScrubbedWiped`). ECB's frame
of 288 bytes, of which its own wipe clears 32, is wiped whole after it
(`PPC64LE.Scrub.verifiedScrubbedAll`). Their postconditions read the memory on return
only within their buffers, as on RISC-V (`Proof/Blowfish/RISCV64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.PPC64LE.Scrub

open VG.Spec.Blowfish VG.PPC64LE VG.PPC64LE.Scrub VG.Proof.Blowfish.ScrubLocal

/-! ## Postconditions -/
theorem len_le (ln : BitVec 64) (k : Nat) :
    ((ArgWord.int abi.ptrBits).ofRaw ln).toNat * k ≤ ln.toNat * k :=
  Nat.le_refl _

theorem len_le1 (ln : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw ln).toNat ≤ ln.toNat * Elem.u8.size :=
  Nat.le_of_eq (Nat.mul_one _).symm

theorem expandKeyOut (stack : Nat) :
    PostOut (expandKeyContract PPC64LE.abi stack) (expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨kl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [expandKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show scheduleAt m₂ sc = _
    rw [scheduleAt_of hb.2]
    exact h

theorem ecbOut (d : Direction) (stack : Nat) : PostOut (ecbContract PPC64LE.abi d stack) (ecbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [ecbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show blocksAt m₂ dt _ = _
    rw [blocksAt_of hb.2 (len_le ln 8)]
    exact h

theorem cbcEncryptOut (stack : Nat) : PostOut (cbcEncryptChainedContract PPC64LE.abi stack) (cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [cbcBlocksAt_of hb.2.2 (len_le ln 8), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem cbcDecryptOut (stack : Nat) : PostOut (cbcDecryptChainedContract PPC64LE.abi stack) (cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [cbcBlocksAt_of hb.2.2 (len_le ln 8), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem cfbEncryptOut (stack : Nat) : PostOut (cfbEncryptContract PPC64LE.abi stack) (cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [cbcBlocksAt_of hb.2.2 (len_le ln 8), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem cfbDecryptOut (stack : Nat) : PostOut (cfbDecryptContract PPC64LE.abi stack) (cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [cbcBlocksAt_of hb.2.2 (len_le ln 8), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem ofbOut (stack : Nat) : PostOut (ofbContract PPC64LE.abi stack) (ofbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [cbcBlocksAt_of hb.2.2 (len_le ln 8), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem cfbEncryptFinalOut (stack : Nat) : PostOut (cfbEncryptFinalContract PPC64LE.abi stack) (cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [bytesAt_of hb.2.2 (len_le1 ln), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem cfbDecryptFinalOut (stack : Nat) : PostOut (cfbDecryptFinalContract PPC64LE.abi stack) (cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [bytesAt_of hb.2.2 (len_le1 ln), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

theorem ofbFinalOut (stack : Nat) : PostOut (ofbFinalContract PPC64LE.abi stack) (ofbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [ofbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
    rw [bytesAt_of hb.2.2 (len_le1 ln), bytesAt_of (n := 8) hb.2.1 (Nat.le_refl _)]
    exact h

/-! ## The functions as emitted -/

/-- `vg_blowfish_expand_key` as emitted (`Impl.Blowfish.PPC64LE.Fn.expandKey`)
meets its contract in constant time and returns without secret residue. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Blowfish.PPC64LE.Fn.expandKey
      (Spec.Blowfish.expandKeyContract PPC64LE.abi 64) 0 :=
  verifiedScrubbedWiped (api := Spec.Blowfish.expandKeyApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 64 .r6 4 Impl.Blowfish.PPC64LE.expandKey
      verified := Proof.Blowfish.PPC64LE.expandKey_framed }
    64 .r6 4 Impl.Blowfish.PPC64LE.expandKey
    ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17]⟩ rfl (expandKeyOut _) (by dsimp only; lit_decide)

/-- `vg_blowfish_ecb_encrypt` as emitted (`Impl.Blowfish.PPC64LE.Fn.ecbEncrypt`)
meets its contract in constant time and returns without secret residue. -/
theorem ecbEncrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Blowfish.PPC64LE.Fn.ecbEncrypt
      (Spec.Blowfish.ecbContract PPC64LE.abi Spec.Blowfish.Direction.encrypt 288) 0 :=
  verifiedScrubbedAll (api := Spec.Blowfish.ecbEncryptApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 288 .r6 4 Impl.Blowfish.PPC64LE.encrypt
      verified := Proof.Blowfish.PPC64LE.ecb_framed Proof.Blowfish.PPC64LE.encrypt_verified }
    288 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17]⟩
    (ecbOut .encrypt _)
    (by dsimp only; lit_decide)

/-- `vg_blowfish_ecb_decrypt` as emitted (`Impl.Blowfish.PPC64LE.Fn.ecbDecrypt`)
meets its contract in constant time and returns without secret residue. -/
theorem ecbDecrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Blowfish.PPC64LE.Fn.ecbDecrypt
      (Spec.Blowfish.ecbContract PPC64LE.abi Spec.Blowfish.Direction.decrypt 288) 0 :=
  verifiedScrubbedAll (api := Spec.Blowfish.ecbDecryptApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 288 .r6 4 Impl.Blowfish.PPC64LE.decrypt
      verified := Proof.Blowfish.PPC64LE.ecb_framed Proof.Blowfish.PPC64LE.decrypt_verified }
    288 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17]⟩
    (ecbOut .decrypt _)
    (by dsimp only; lit_decide)

/-- `vg_blowfish_cbc_encrypt_chained` as emitted
(`Impl.Blowfish.PPC64LE.Fn.cbcEncryptChained`) meets its contract in constant
time and returns without secret residue. -/
theorem cbcEncryptChained_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Blowfish.PPC64LE.Fn.cbcEncryptChained
      (Spec.Blowfish.cbcEncryptChainedContract PPC64LE.abi 128) 0 :=
  verifiedScrubbedWiped (api := Spec.Blowfish.cbcEncryptChainedApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.cbcEncryptChained
      verified := Proof.Blowfish.PPC64LE.cbcEnc_framed Proof.Blowfish.PPC64LE.Modes.cbcEncryptChained_verified }
    128 .r7 12 Impl.Blowfish.PPC64LE.cbcEncryptChained
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17]⟩ rfl (cbcEncryptOut _) (by dsimp only; lit_decide)

/-- `vg_blowfish_cbc_decrypt_chained` as emitted
(`Impl.Blowfish.PPC64LE.Fn.cbcDecryptChained`) meets its contract in constant
time and returns without secret residue. -/
theorem cbcDecryptChained_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Blowfish.PPC64LE.Fn.cbcDecryptChained
      (Spec.Blowfish.cbcDecryptChainedContract PPC64LE.abi 128) 0 :=
  verifiedScrubbedWiped (api := Spec.Blowfish.cbcDecryptChainedApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.cbcDecryptChained
      verified := Proof.Blowfish.PPC64LE.cbcDec_framed Proof.Blowfish.PPC64LE.Modes.cbcDecryptChained_verified }
    128 .r7 12 Impl.Blowfish.PPC64LE.cbcDecryptChained
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17]⟩ rfl (cbcDecryptOut _) (by dsimp only; lit_decide)

/-- `vg_blowfish_cfb64_encrypt` as emitted (`Impl.Blowfish.PPC64LE.Fn.cfbEncrypt`)
meets its contract in constant time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Blowfish.PPC64LE.Fn.cfbEncrypt
      (Spec.Blowfish.cfbEncryptContract PPC64LE.abi 128) 0 :=
  verifiedScrubbedWiped (api := Spec.Blowfish.cfbEncryptApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.cfbEncrypt
      verified := Proof.Blowfish.PPC64LE.cfbEnc_framed Proof.Blowfish.PPC64LE.Modes.cfbEncrypt_verified }
    128 .r7 12 Impl.Blowfish.PPC64LE.cfbEncrypt
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17]⟩ rfl (cfbEncryptOut _) (by dsimp only; lit_decide)

/-- `vg_blowfish_cfb64_decrypt` as emitted (`Impl.Blowfish.PPC64LE.Fn.cfbDecrypt`)
meets its contract in constant time and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Blowfish.PPC64LE.Fn.cfbDecrypt
      (Spec.Blowfish.cfbDecryptContract PPC64LE.abi 128) 0 :=
  verifiedScrubbedWiped (api := Spec.Blowfish.cfbDecryptApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.cfbDecrypt
      verified := Proof.Blowfish.PPC64LE.cfbDec_framed Proof.Blowfish.PPC64LE.Modes.cfbDecrypt_verified }
    128 .r7 12 Impl.Blowfish.PPC64LE.cfbDecrypt
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17]⟩ rfl (cfbDecryptOut _) (by dsimp only; lit_decide)

/-- `vg_blowfish_cfb64_encrypt_final` as emitted
(`Impl.Blowfish.PPC64LE.Fn.cfbEncryptFinal`) meets its contract in constant
time and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Blowfish.PPC64LE.Fn.cfbEncryptFinal
      (Spec.Blowfish.cfbEncryptFinalContract PPC64LE.abi 128) 0 :=
  verifiedScrubbedWiped (api := Spec.Blowfish.cfbEncryptFinalApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.cfbEncryptFinal
      verified := Proof.Blowfish.PPC64LE.FbFinal.cfbEncryptFinal_framed }
    128 .r7 12 Impl.Blowfish.PPC64LE.cfbEncryptFinal
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17]⟩ rfl (cfbEncryptFinalOut _) (by dsimp only; lit_decide)

/-- `vg_blowfish_cfb64_decrypt_final` as emitted
(`Impl.Blowfish.PPC64LE.Fn.cfbDecryptFinal`) meets its contract in constant
time and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Blowfish.PPC64LE.Fn.cfbDecryptFinal
      (Spec.Blowfish.cfbDecryptFinalContract PPC64LE.abi 128) 0 :=
  verifiedScrubbedWiped (api := Spec.Blowfish.cfbDecryptFinalApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.cfbDecryptFinal
      verified := Proof.Blowfish.PPC64LE.FbFinal.cfbDecryptFinal_framed }
    128 .r7 12 Impl.Blowfish.PPC64LE.cfbDecryptFinal
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17]⟩ rfl (cfbDecryptFinalOut _) (by dsimp only; lit_decide)

/-- `vg_blowfish_ofb` as emitted (`Impl.Blowfish.PPC64LE.Fn.ofb`) meets its
contract in constant time and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Blowfish.PPC64LE.Fn.ofb
      (Spec.Blowfish.ofbContract PPC64LE.abi 128) 0 :=
  verifiedScrubbedWiped (api := Spec.Blowfish.ofbApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.ofb
      verified := Proof.Blowfish.PPC64LE.ofb_framed Proof.Blowfish.PPC64LE.Modes.ofb_verified }
    128 .r7 12 Impl.Blowfish.PPC64LE.ofb
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17]⟩ rfl (ofbOut _) (by dsimp only; lit_decide)

/-- `vg_blowfish_ofb_final` as emitted (`Impl.Blowfish.PPC64LE.Fn.ofbFinal`) meets
its contract in constant time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Blowfish.PPC64LE.Fn.ofbFinal
      (Spec.Blowfish.ofbFinalContract PPC64LE.abi 128) 0 :=
  verifiedScrubbedWiped (api := Spec.Blowfish.ofbFinalApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.ofbFinal
      verified := Proof.Blowfish.PPC64LE.FbFinal.ofbFinal_framed }
    128 .r7 12 Impl.Blowfish.PPC64LE.ofbFinal
    ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17]⟩ rfl (ofbFinalOut _) (by dsimp only; lit_decide)

end VG.Proof.Blowfish.PPC64LE.Scrub
