module

public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Impl.Idea.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Idea.Contract
public import VerifiedGarbage.Spec.Idea.Cbc
public import VerifiedGarbage.Spec.Idea.Cfb
public import VerifiedGarbage.Spec.Idea.CfbFinal
public import VerifiedGarbage.Spec.Idea.Ofb
public import VerifiedGarbage.Spec.Idea.OfbFinal
public import VerifiedGarbage.Proof.Idea.X86.Key
public import VerifiedGarbage.Proof.Idea.X86.Verified
public import VerifiedGarbage.Proof.Idea.X86.CbcVerified
public import VerifiedGarbage.Proof.Idea.X86.FbVerified
public import VerifiedGarbage.Proof.Idea.X86.FbFinalVerified
import VerifiedGarbage.Proof.Idea.ScrubLocal
import VerifiedGarbage.Proof.Idea.X86.Lit
import VerifiedGarbage.Proof.Idea.X86.ModesLit
import VerifiedGarbage.Proof.Idea.X86.FbFinalLit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Proof.Framework.X86.ScrubSel
meta import VerifiedGarbage.Impl.Idea.X86.Fn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Idea.Contract
meta import VerifiedGarbage.Spec.Idea.Cbc
meta import VerifiedGarbage.Spec.Idea.Cfb
meta import VerifiedGarbage.Spec.Idea.CfbFinal
meta import VerifiedGarbage.Spec.Idea.Ofb
meta import VerifiedGarbage.Spec.Idea.OfbFinal
meta import VerifiedGarbage.Proof.Idea.X86.Key
meta import VerifiedGarbage.Proof.Idea.X86.Verified
meta import VerifiedGarbage.Proof.Idea.X86.CbcVerified
meta import VerifiedGarbage.Proof.Idea.X86.FbVerified
meta import VerifiedGarbage.Proof.Idea.X86.FbFinalVerified
meta import VerifiedGarbage.Proof.Idea.ScrubLocal
meta import VerifiedGarbage.Proof.Idea.X86.Lit
meta import VerifiedGarbage.Proof.Idea.X86.ModesLit
meta import VerifiedGarbage.Proof.Idea.X86.FbFinalLit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# IDEA on x86 (32-bit), without secret residue

The functions as emitted (`Impl.Idea.X86.Fn`) return without secret residue.
Key expansion calls nothing and has no frame, and then clears the registers
it may change (`X86.Scrub.verifiedScrubbed`). Key inversion, ECB and the CBC,
CFB64 and OFB functions run with their working space in a frame on the stack
(`withStackScratch`, `withStackScratchWiped`), and then clear the registers a
callee may change and zero stack below `esp`. Key inversion and ECB zero all
the stack their contracts reserve (`X86.Scrub.verifiedScrubbedAll`), whose
cleanup needs one Boolean of the code (`X86.Scrub.scrubSide`,
`X86.Scrub.scrubFSide`), proved by evaluating the code once (`lit_decide`).
The modes zero only the doublewords that the residue analysis finds they may
leave different in two runs (`X86.Scrub.verifiedScrubbedSel`, the analysis's
run checked by `taint_decide_ct`). Their postconditions read the
memory on return only within their buffers, as on the other targets
(`Proof/Idea/ScrubLocal.lean`); a length is the low 32 bits of its argument
word.
-/

@[expose] public section

namespace VG.Proof.Idea.X86.Scrub

open VG.Spec.Idea VG.X86 VG.X86.Scrub VG.Proof.Idea.ScrubLocal

/-! ## Postconditions -/

theorem len_le (ln : BitVec 64) (k : Nat) :
    ((ArgWord.int abi.ptrBits).ofRaw ln).toNat * k ≤ ln.toNat * k :=
  Nat.mul_le_mul_right _ (by simp only [ArgWord.ofRaw, BitVec.toNat_setWidth]; exact Nat.mod_le _ _)

theorem len_le1 (ln : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw ln).toNat ≤ ln.toNat * Elem.u8.size := by
  have := len_le ln 1
  simpa only [Nat.mul_one, Elem.size] using this

theorem invertKeyOut (stack : Nat) : PostOut (invertKeyContract X86.abi stack) (invertKeySig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 1) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨inv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [invertKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    show scheduleAt m₂ inv = _
    rw [scheduleAt_of hb.2]
    exact h

theorem ecbOut (stack : Nat) : PostOut (Spec.Idea.ecbContract X86.abi stack) (ecbSig.retBits 32) :=
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

/-- `Spec.Idea.expandKeyApi` as emitted (`Impl.Idea.X86.Fn.expandKey`) meets its contract
in constant time and returns without secret residue. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed X86.target Impl.Idea.X86.Fn.expandKey (Spec.Idea.expandKeyContract X86.abi) 0 :=
  verifiedScrubbed (api := Spec.Idea.expandKeyApi)
    { code := Impl.Idea.X86.expandKey
      verified := Proof.Idea.X86.expandKey_verified }

/-- `Spec.Idea.invertKeyApi` as emitted (`Impl.Idea.X86.Fn.invertKey`) meets its contract
in constant time and returns without secret residue. -/
theorem invertKey_scrubbed :
    VerifiedScrubbed X86.target Impl.Idea.X86.Fn.invertKey (Spec.Idea.invertKeyContract X86.abi 32) 0 :=
  verifiedScrubbedAll (api := Spec.Idea.invertKeyApi)
    { code := Impl.StackScratch.X86.withStackScratch 32 2 Impl.Idea.X86.invertKey
      verified := Proof.Idea.X86.invertKey_framed }
    (invertKeyOut _)

/-- `Spec.Idea.ecbApi` as emitted (`Impl.Idea.X86.Fn.ecb`) meets its contract
in constant time and returns without secret residue. -/
theorem ecb_scrubbed :
    VerifiedScrubbed X86.target Impl.Idea.X86.Fn.ecb (Spec.Idea.ecbContract X86.abi 152) 0 :=
  verifiedScrubbedAll (api := Spec.Idea.ecbApi)
    { code := Impl.StackScratch.X86.withStackScratchWiped 152 3 Proof.Idea.X86.wipedWords Impl.Idea.X86.ecb
      verified := Proof.Idea.X86.ecb_framed }
    (ecbOut _)

/-- `Spec.Idea.cbcEncryptChainedApi` as emitted (`Impl.Idea.X86.Fn.cbcEncryptChained`) meets its contract
in constant time and returns without secret residue. -/
theorem cbcEncryptChained_scrubbed :
    VerifiedScrubbed X86.target Impl.Idea.X86.Fn.cbcEncryptChained (Spec.Idea.cbcEncryptChainedContract X86.abi 208) 0 :=
  verifiedScrubbedSel (api := Spec.Idea.cbcEncryptChainedApi) (W := 208)
    { code := Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.cbcEncryptChained
      verified := Proof.Idea.X86.Cbc.cbcEncryptChained_framed }
    Impl.Idea.X86.Fn.modeWords (cbcEncryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Idea.cbcDecryptChainedApi` as emitted (`Impl.Idea.X86.Fn.cbcDecryptChained`) meets its contract
in constant time and returns without secret residue. -/
theorem cbcDecryptChained_scrubbed :
    VerifiedScrubbed X86.target Impl.Idea.X86.Fn.cbcDecryptChained (Spec.Idea.cbcDecryptChainedContract X86.abi 208) 0 :=
  verifiedScrubbedSel (api := Spec.Idea.cbcDecryptChainedApi) (W := 208)
    { code := Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.cbcDecryptChained
      verified := Proof.Idea.X86.Cbc.cbcDecryptChained_framed }
    Impl.Idea.X86.Fn.modeWords (cbcDecryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Idea.cfbEncryptApi` as emitted (`Impl.Idea.X86.Fn.cfbEncrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Idea.X86.Fn.cfbEncrypt (Spec.Idea.cfbEncryptContract X86.abi 208) 0 :=
  verifiedScrubbedSel (api := Spec.Idea.cfbEncryptApi) (W := 208)
    { code := Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.cfbEncrypt
      verified := Proof.Idea.X86.Fb.cfbEncrypt_framed }
    Impl.Idea.X86.Fn.modeWords (cfbEncryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Idea.cfbDecryptApi` as emitted (`Impl.Idea.X86.Fn.cfbDecrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Idea.X86.Fn.cfbDecrypt (Spec.Idea.cfbDecryptContract X86.abi 208) 0 :=
  verifiedScrubbedSel (api := Spec.Idea.cfbDecryptApi) (W := 208)
    { code := Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.cfbDecrypt
      verified := Proof.Idea.X86.Fb.cfbDecrypt_framed }
    Impl.Idea.X86.Fn.modeWords (cfbDecryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Idea.cfbEncryptFinalApi` as emitted (`Impl.Idea.X86.Fn.cfbEncryptFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Idea.X86.Fn.cfbEncryptFinal (Spec.Idea.cfbEncryptFinalContract X86.abi 208) 0 :=
  verifiedScrubbedSel (api := Spec.Idea.cfbEncryptFinalApi) (W := 208)
    { code := Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.cfbEncryptFinal
      verified := Proof.Idea.X86.FbFinal.cfbEncryptFinal_framed }
    Impl.Idea.X86.Fn.modeWords (cfbEncryptFinalOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Idea.cfbDecryptFinalApi` as emitted (`Impl.Idea.X86.Fn.cfbDecryptFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Idea.X86.Fn.cfbDecryptFinal (Spec.Idea.cfbDecryptFinalContract X86.abi 208) 0 :=
  verifiedScrubbedSel (api := Spec.Idea.cfbDecryptFinalApi) (W := 208)
    { code := Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.cfbDecryptFinal
      verified := Proof.Idea.X86.FbFinal.cfbDecryptFinal_framed }
    Impl.Idea.X86.Fn.modeWords (cfbDecryptFinalOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Idea.ofbApi` as emitted (`Impl.Idea.X86.Fn.ofb`) meets its contract
in constant time and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed X86.target Impl.Idea.X86.Fn.ofb (Spec.Idea.ofbContract X86.abi 208) 0 :=
  verifiedScrubbedSel (api := Spec.Idea.ofbApi) (W := 208)
    { code := Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.ofb
      verified := Proof.Idea.X86.Fb.ofb_framed }
    Impl.Idea.X86.Fn.modeWords (ofbOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Idea.ofbFinalApi` as emitted (`Impl.Idea.X86.Fn.ofbFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.Idea.X86.Fn.ofbFinal (Spec.Idea.ofbFinalContract X86.abi 208) 0 :=
  verifiedScrubbedSel (api := Spec.Idea.ofbFinalApi) (W := 208)
    { code := Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.ofbFinal
      verified := Proof.Idea.X86.FbFinal.ofbFinal_framed }
    Impl.Idea.X86.Fn.modeWords (ofbFinalOut _) (by decide) ⟨_, by taint_decide_ct⟩

end VG.Proof.Idea.X86.Scrub
