module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubWiped
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

/-!
# Blowfish on PPC64LE, without secret residue

Key expansion and the CBC, CFB64 and OFB functions zero their whole frame
themselves before they release it (`withStackScratchWiped`), and have no
frames of their own inside it, so they need only the clearing of the
volatile registers after them (`PPC64LE.Scrub.withScrubWiped`). ECB's frame
of 288 bytes, of which its own wipe clears 32, is wiped whole after it
(`PPC64LE.Scrub.withScrub`). Their postconditions read the memory on return
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

/-! ## The registrations -/

/-- `Spec.Blowfish.expandKeyApi`. -/
def expandKeyReg : Registration Spec.Blowfish.expandKeyApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 64 .r6 4 Impl.Blowfish.PPC64LE.expandKey
      verified := Proof.Blowfish.PPC64LE.expandKey_framed }
    64 .r6 4 Impl.Blowfish.PPC64LE.expandKey rfl (expandKeyOut _)

/-- `Spec.Blowfish.ecbEncryptApi`. -/
def ecbEncryptReg : Registration Spec.Blowfish.ecbEncryptApi PPC64LE.target :=
  withScrub {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 288 .r6 4 Impl.Blowfish.PPC64LE.encrypt
      verified := Proof.Blowfish.PPC64LE.ecb_framed Proof.Blowfish.PPC64LE.encrypt_verified }
    (ecbOut .encrypt _)

/-- `Spec.Blowfish.ecbDecryptApi`. -/
def ecbDecryptReg : Registration Spec.Blowfish.ecbDecryptApi PPC64LE.target :=
  withScrub {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 288 .r6 4 Impl.Blowfish.PPC64LE.decrypt
      verified := Proof.Blowfish.PPC64LE.ecb_framed Proof.Blowfish.PPC64LE.decrypt_verified }
    (ecbOut .decrypt _)

/-- `Spec.Blowfish.cbcEncryptChainedApi`. -/
def cbcEncryptChainedReg : Registration Spec.Blowfish.cbcEncryptChainedApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.cbcEncryptChained
      verified := Proof.Blowfish.PPC64LE.cbcEnc_framed Proof.Blowfish.PPC64LE.Modes.cbcEncryptChained_verified }
    128 .r7 12 Impl.Blowfish.PPC64LE.cbcEncryptChained rfl (cbcEncryptOut _)

/-- `Spec.Blowfish.cbcDecryptChainedApi`. -/
def cbcDecryptChainedReg : Registration Spec.Blowfish.cbcDecryptChainedApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.cbcDecryptChained
      verified := Proof.Blowfish.PPC64LE.cbcDec_framed Proof.Blowfish.PPC64LE.Modes.cbcDecryptChained_verified }
    128 .r7 12 Impl.Blowfish.PPC64LE.cbcDecryptChained rfl (cbcDecryptOut _)

/-- `Spec.Blowfish.cfbEncryptApi`. -/
def cfbEncryptReg : Registration Spec.Blowfish.cfbEncryptApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.cfbEncrypt
      verified := Proof.Blowfish.PPC64LE.cfbEnc_framed Proof.Blowfish.PPC64LE.Modes.cfbEncrypt_verified }
    128 .r7 12 Impl.Blowfish.PPC64LE.cfbEncrypt rfl (cfbEncryptOut _)

/-- `Spec.Blowfish.cfbDecryptApi`. -/
def cfbDecryptReg : Registration Spec.Blowfish.cfbDecryptApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.cfbDecrypt
      verified := Proof.Blowfish.PPC64LE.cfbDec_framed Proof.Blowfish.PPC64LE.Modes.cfbDecrypt_verified }
    128 .r7 12 Impl.Blowfish.PPC64LE.cfbDecrypt rfl (cfbDecryptOut _)

/-- `Spec.Blowfish.cfbEncryptFinalApi`. -/
def cfbEncryptFinalReg : Registration Spec.Blowfish.cfbEncryptFinalApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.cfbEncryptFinal
      verified := Proof.Blowfish.PPC64LE.FbFinal.cfbEncryptFinal_framed }
    128 .r7 12 Impl.Blowfish.PPC64LE.cfbEncryptFinal rfl (cfbEncryptFinalOut _)

/-- `Spec.Blowfish.cfbDecryptFinalApi`. -/
def cfbDecryptFinalReg : Registration Spec.Blowfish.cfbDecryptFinalApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.cfbDecryptFinal
      verified := Proof.Blowfish.PPC64LE.FbFinal.cfbDecryptFinal_framed }
    128 .r7 12 Impl.Blowfish.PPC64LE.cfbDecryptFinal rfl (cfbDecryptFinalOut _)

/-- `Spec.Blowfish.ofbApi`. -/
def ofbReg : Registration Spec.Blowfish.ofbApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.ofb
      verified := Proof.Blowfish.PPC64LE.ofb_framed Proof.Blowfish.PPC64LE.Modes.ofb_verified }
    128 .r7 12 Impl.Blowfish.PPC64LE.ofb rfl (ofbOut _)

/-- `Spec.Blowfish.ofbFinalApi`. -/
def ofbFinalReg : Registration Spec.Blowfish.ofbFinalApi PPC64LE.target :=
  withScrubWiped {
      code := Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.ofbFinal
      verified := Proof.Blowfish.PPC64LE.FbFinal.ofbFinal_framed }
    128 .r7 12 Impl.Blowfish.PPC64LE.ofbFinal rfl (ofbFinalOut _)

/-- All are scrubbed: the side conditions of `withScrubWiped` and `withScrub` hold. -/
example : expandKeyReg.residue.isSome ∧
    ecbEncryptReg.residue.isSome ∧
    ecbDecryptReg.residue.isSome ∧
    cbcEncryptChainedReg.residue.isSome ∧
    cbcDecryptChainedReg.residue.isSome ∧
    cfbEncryptReg.residue.isSome ∧
    cfbDecryptReg.residue.isSome ∧
    cfbEncryptFinalReg.residue.isSome ∧
    cfbDecryptFinalReg.residue.isSome ∧
    ofbReg.residue.isSome ∧
    ofbFinalReg.residue.isSome := by decide

end VG.Proof.Blowfish.PPC64LE.Scrub
