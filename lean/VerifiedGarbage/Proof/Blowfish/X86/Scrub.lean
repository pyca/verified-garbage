module

public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.Blowfish.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Blowfish.Contract
public import VerifiedGarbage.Spec.Blowfish.Cbc
public import VerifiedGarbage.Spec.Blowfish.Cfb
public import VerifiedGarbage.Spec.Blowfish.CfbFinal
public import VerifiedGarbage.Spec.Blowfish.Ofb
public import VerifiedGarbage.Spec.Blowfish.OfbFinal
public import VerifiedGarbage.Proof.Blowfish.X86.Frame
public import VerifiedGarbage.Proof.Blowfish.X86.CbcVerified
public import VerifiedGarbage.Proof.Blowfish.X86.FbVerified
public import VerifiedGarbage.Proof.Blowfish.X86.FbFinalVerified
import VerifiedGarbage.Proof.Blowfish.ScrubLocal
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Blowfish.X86.Lit
import VerifiedGarbage.Proof.Blowfish.X86.ModesLit
import VerifiedGarbage.Proof.Blowfish.X86.FbFinalLit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Blowfish on x86 (32-bit), without secret residue

Key expansion, ECB and the CBC, CFB64 and OFB functions run with their
working space in a frame on the stack (`withStackScratchWiped`). As emitted
(`Impl.Blowfish.X86.Fn`), each then zeroes the stack its contract reserves
below `esp` and clears the registers a callee may change, and returns without
secret residue (`X86.Scrub.verifiedScrubbedF`). What the cleanup needs of the
code is one Boolean (`X86.Scrub.scrubFSide`), proved by
evaluating the code once (`lit_decide`). Their postconditions read the
memory on return only within their buffers, as on the other targets
(`Proof/Blowfish/ScrubLocal.lean`); a length is the low 32 bits of its
argument word.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86.Scrub

open VG.Spec.Blowfish VG.X86 VG.X86.Scrub VG.Proof.Blowfish.ScrubLocal

/-! ## Postconditions -/

theorem len_le (ln : BitVec 64) (k : Nat) :
    ((ArgWord.int abi.ptrBits).ofRaw ln).toNat * k ≤ ln.toNat * k :=
  Nat.mul_le_mul_right _ (by simp only [ArgWord.ofRaw, BitVec.toNat_setWidth]; exact Nat.mod_le _ _)

theorem len_le1 (ln : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw ln).toNat ≤ ln.toNat * Elem.u8.size := by
  have := len_le ln 1
  simpa only [Nat.mul_one, Elem.size] using this

theorem expandKeyOut (stack : Nat) :
    PostOut (expandKeyContract X86.abi stack) (expandKeySig.retBits 32) :=
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

theorem ecbOut (d : Direction) (stack : Nat) : PostOut (ecbContract X86.abi d stack) (ecbSig.retBits 32) :=
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

theorem cbcEncryptOut (stack : Nat) : PostOut (cbcEncryptChainedContract X86.abi stack) (cbcChainedSig.retBits 32) :=
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

theorem cbcDecryptOut (stack : Nat) : PostOut (cbcDecryptChainedContract X86.abi stack) (cbcChainedSig.retBits 32) :=
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

theorem cfbEncryptOut (stack : Nat) : PostOut (cfbEncryptContract X86.abi stack) (cfbSig.retBits 32) :=
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

theorem cfbDecryptOut (stack : Nat) : PostOut (cfbDecryptContract X86.abi stack) (cfbSig.retBits 32) :=
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

theorem ofbOut (stack : Nat) : PostOut (ofbContract X86.abi stack) (ofbSig.retBits 32) :=
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

theorem cfbEncryptFinalOut (stack : Nat) : PostOut (cfbEncryptFinalContract X86.abi stack) (cfbFinalSig.retBits 32) :=
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

theorem cfbDecryptFinalOut (stack : Nat) : PostOut (cfbDecryptFinalContract X86.abi stack) (cfbFinalSig.retBits 32) :=
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

theorem ofbFinalOut (stack : Nat) : PostOut (ofbFinalContract X86.abi stack) (ofbFinalSig.retBits 32) :=
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

/-- `Spec.Blowfish.expandKeyApi` as emitted (`Impl.Blowfish.X86.Fn.expandKey`) meets its contract
in constant time and returns without secret residue. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed X86.target Impl.Blowfish.X86.Fn.expandKey (Spec.Blowfish.expandKeyContract X86.abi 84) 0 :=
  verifiedScrubbedF (api := Spec.Blowfish.expandKeyApi)
    { code := Impl.StackScratch.X86.withStackScratchWiped 84 3 10 Impl.Blowfish.X86.expandKey
      verified := Proof.Blowfish.X86.expandKey_framed }
    (expandKeyOut _)

/-- `Spec.Blowfish.ecbEncryptApi` as emitted (`Impl.Blowfish.X86.Fn.ecbEncrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem ecbEncrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Blowfish.X86.Fn.ecbEncrypt (Spec.Blowfish.ecbContract X86.abi (Proof.Blowfish.X86.dir true) 276) 0 :=
  verifiedScrubbedF (api := Spec.Blowfish.ecbEncryptApi)
    { code := Impl.StackScratch.X86.withStackScratchWiped 276 3 10 Impl.Blowfish.X86.encrypt
      verified := Proof.Blowfish.X86.ecb_framed true }
    (ecbOut .encrypt _)

/-- `Spec.Blowfish.ecbDecryptApi` as emitted (`Impl.Blowfish.X86.Fn.ecbDecrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem ecbDecrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Blowfish.X86.Fn.ecbDecrypt (Spec.Blowfish.ecbContract X86.abi (Proof.Blowfish.X86.dir false) 276) 0 :=
  verifiedScrubbedF (api := Spec.Blowfish.ecbDecryptApi)
    { code := Impl.StackScratch.X86.withStackScratchWiped 276 3 10 Impl.Blowfish.X86.decrypt
      verified := Proof.Blowfish.X86.ecb_framed false }
    (ecbOut .decrypt _)

/-- `Spec.Blowfish.cbcEncryptChainedApi` as emitted (`Impl.Blowfish.X86.Fn.cbcEncryptChained`) meets its contract
in constant time and returns without secret residue. -/
theorem cbcEncryptChained_scrubbed :
    VerifiedScrubbed X86.target Impl.Blowfish.X86.Fn.cbcEncryptChained (Spec.Blowfish.cbcEncryptChainedContract X86.abi 112) 0 :=
  verifiedScrubbedF (api := Spec.Blowfish.cbcEncryptChainedApi)
    { code := Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cbcEncryptChained
      verified := Proof.Blowfish.X86.Cbc.cbcEncryptChained_framed }
    (cbcEncryptOut _)

/-- `Spec.Blowfish.cbcDecryptChainedApi` as emitted (`Impl.Blowfish.X86.Fn.cbcDecryptChained`) meets its contract
in constant time and returns without secret residue. -/
theorem cbcDecryptChained_scrubbed :
    VerifiedScrubbed X86.target Impl.Blowfish.X86.Fn.cbcDecryptChained (Spec.Blowfish.cbcDecryptChainedContract X86.abi 112) 0 :=
  verifiedScrubbedF (api := Spec.Blowfish.cbcDecryptChainedApi)
    { code := Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cbcDecryptChained
      verified := Proof.Blowfish.X86.Cbc.cbcDecryptChained_framed }
    (cbcDecryptOut _)

/-- `Spec.Blowfish.cfbEncryptApi` as emitted (`Impl.Blowfish.X86.Fn.cfbEncrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Blowfish.X86.Fn.cfbEncrypt (Spec.Blowfish.cfbEncryptContract X86.abi 112) 0 :=
  verifiedScrubbedF (api := Spec.Blowfish.cfbEncryptApi)
    { code := Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cfbEncrypt
      verified := Proof.Blowfish.X86.Fb.cfbEncrypt_framed }
    (cfbEncryptOut _)

/-- `Spec.Blowfish.cfbDecryptApi` as emitted (`Impl.Blowfish.X86.Fn.cfbDecrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Blowfish.X86.Fn.cfbDecrypt (Spec.Blowfish.cfbDecryptContract X86.abi 112) 0 :=
  verifiedScrubbedF (api := Spec.Blowfish.cfbDecryptApi)
    { code := Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cfbDecrypt
      verified := Proof.Blowfish.X86.Fb.cfbDecrypt_framed }
    (cfbDecryptOut _)

/-- `Spec.Blowfish.cfbEncryptFinalApi` as emitted (`Impl.Blowfish.X86.Fn.cfbEncryptFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Blowfish.X86.Fn.cfbEncryptFinal (Spec.Blowfish.cfbEncryptFinalContract X86.abi 112) 0 :=
  verifiedScrubbedF (api := Spec.Blowfish.cfbEncryptFinalApi)
    { code := Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cfbEncryptFinal
      verified := Proof.Blowfish.X86.FbFinal.cfbEncryptFinal_framed }
    (cfbEncryptFinalOut _)

/-- `Spec.Blowfish.cfbDecryptFinalApi` as emitted (`Impl.Blowfish.X86.Fn.cfbDecryptFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Blowfish.X86.Fn.cfbDecryptFinal (Spec.Blowfish.cfbDecryptFinalContract X86.abi 112) 0 :=
  verifiedScrubbedF (api := Spec.Blowfish.cfbDecryptFinalApi)
    { code := Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cfbDecryptFinal
      verified := Proof.Blowfish.X86.FbFinal.cfbDecryptFinal_framed }
    (cfbDecryptFinalOut _)

/-- `Spec.Blowfish.ofbApi` as emitted (`Impl.Blowfish.X86.Fn.ofb`) meets its contract
in constant time and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed X86.target Impl.Blowfish.X86.Fn.ofb (Spec.Blowfish.ofbContract X86.abi 112) 0 :=
  verifiedScrubbedF (api := Spec.Blowfish.ofbApi)
    { code := Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.ofb
      verified := Proof.Blowfish.X86.Fb.ofb_framed }
    (ofbOut _)

/-- `Spec.Blowfish.ofbFinalApi` as emitted (`Impl.Blowfish.X86.Fn.ofbFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Blowfish.X86.Fn.ofbFinal (Spec.Blowfish.ofbFinalContract X86.abi 112) 0 :=
  verifiedScrubbedF (api := Spec.Blowfish.ofbFinalApi)
    { code := Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.ofbFinal
      verified := Proof.Blowfish.X86.FbFinal.ofbFinal_framed }
    (ofbFinalOut _)

end VG.Proof.Blowfish.X86.Scrub
