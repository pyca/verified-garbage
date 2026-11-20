module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Framework.Arm.ScrubSel
public import VerifiedGarbage.Impl.Idea.Arm.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Idea.Contract
public import VerifiedGarbage.Spec.Idea.Cbc
public import VerifiedGarbage.Spec.Idea.Cfb
public import VerifiedGarbage.Spec.Idea.CfbFinal
public import VerifiedGarbage.Spec.Idea.Ofb
public import VerifiedGarbage.Spec.Idea.OfbFinal
public import VerifiedGarbage.Proof.Idea.Arm.Key
public import VerifiedGarbage.Proof.Idea.Arm.Verified
public import VerifiedGarbage.Proof.Idea.Arm.CbcVerified
public import VerifiedGarbage.Proof.Idea.Arm.FbVerified
public import VerifiedGarbage.Proof.Idea.Arm.FbFinalVerified
public import VerifiedGarbage.Proof.Modes.Arm.ScrubCode
import VerifiedGarbage.Proof.Idea.ScrubLocal
import VerifiedGarbage.Proof.Idea.Arm.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubSel
meta import VerifiedGarbage.Impl.Idea.Arm.Fn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Idea.Contract
meta import VerifiedGarbage.Spec.Idea.Cbc
meta import VerifiedGarbage.Spec.Idea.Cfb
meta import VerifiedGarbage.Spec.Idea.CfbFinal
meta import VerifiedGarbage.Spec.Idea.Ofb
meta import VerifiedGarbage.Spec.Idea.OfbFinal
meta import VerifiedGarbage.Proof.Idea.Arm.Key
meta import VerifiedGarbage.Proof.Idea.Arm.Verified
meta import VerifiedGarbage.Proof.Idea.Arm.CbcVerified
meta import VerifiedGarbage.Proof.Idea.Arm.FbVerified
meta import VerifiedGarbage.Proof.Idea.Arm.FbFinalVerified
meta import VerifiedGarbage.Proof.Modes.Arm.ScrubCode
meta import VerifiedGarbage.Proof.Idea.ScrubLocal
meta import VerifiedGarbage.Proof.Idea.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# IDEA on ARMv7, without secret residue

The functions as emitted (`Impl.Idea.Arm.Fn`) return without secret residue.
Key expansion has no frame, and then sets the registers a callee may change
to constants (`Arm.Scrub.verifiedScrubbed`). Key inversion and ECB keep their
working space in a frame of 24 and 32 bytes (`withRegScratch`), and the CBC,
CFB64 and OFB functions 64 bytes of their own around ECB's 32
(`withStackScratchWiped`). None makes an indirect call. Key inversion and
ECB are emitted followed by a wipe of the stack their contracts reserve,
then the registers (`Arm.Scrub.verifiedScrubbedAll`). The modes wipe their own
frame, and are emitted followed by a wipe of only the words of that stack
that the residue analysis (`Arm.rtaint`) finds may differ between two runs,
then the registers (`Arm.Scrub.verifiedScrubbedSel`, whose analysis the
kernel evaluates here: `taint_decide_ct`): of their 96 bytes, the 40 that
ECB's frame and theirs leave. Their postconditions read the memory on
return only within their buffers, as on the other targets
(`Proof/Idea/ScrubLocal.lean`).

The modes call ECB's code as it is verified, without the wipe, under a name
of its own (`vg_idea_ecb_entry`, `Impl.Idea.Arm.ecbCore`), which the
emitter writes as an internal function: the analysis of each mode covers
the frame of that call.
-/

@[expose] public section

namespace VG.Proof.Idea.Arm.Scrub

open VG VG.Spec.Idea VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Proof.Modes.Arm VG.Proof.Idea.ScrubLocal

/-! ## Postconditions -/

theorem len_le (ln : BitVec 64) (k : Nat) :
    ((ArgWord.int Arm.abi.ptrBits).ofRaw ln).toNat * k ≤ ln.toNat * k :=
  Nat.mul_le_mul_right _ (by simp only [ArgWord.ofRaw, BitVec.toNat_setWidth]; exact Nat.mod_le _ _)

theorem len_le1 (ln : BitVec 64) : ((ArgWord.int Arm.abi.ptrBits).ofRaw ln).toNat ≤ ln.toNat * Elem.u8.size := by
  have := len_le ln 1
  simpa only [Nat.mul_one, Elem.size] using this

theorem invertKeyOut (stack : Nat) : PostOut (invertKeyContract Arm.abi stack) (invertKeySig.retBits 32) :=
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

theorem ecbOut (stack : Nat) : PostOut (Spec.Idea.ecbContract Arm.abi stack) (ecbSig.retBits 32) :=
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

theorem cbcEncryptOut (stack : Nat) : PostOut (cbcEncryptChainedContract Arm.abi stack) (cbcChainedSig.retBits 32) :=
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

theorem cbcDecryptOut (stack : Nat) : PostOut (cbcDecryptChainedContract Arm.abi stack) (cbcChainedSig.retBits 32) :=
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

theorem cfbEncryptOut (stack : Nat) : PostOut (cfbEncryptContract Arm.abi stack) (cfbSig.retBits 32) :=
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

theorem cfbDecryptOut (stack : Nat) : PostOut (cfbDecryptContract Arm.abi stack) (cfbSig.retBits 32) :=
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

theorem ofbOut (stack : Nat) : PostOut (ofbContract Arm.abi stack) (ofbSig.retBits 32) :=
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

theorem cfbEncryptFinalOut (stack : Nat) : PostOut (cfbEncryptFinalContract Arm.abi stack) (cfbFinalSig.retBits 32) :=
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

theorem cfbDecryptFinalOut (stack : Nat) : PostOut (cfbDecryptFinalContract Arm.abi stack) (cfbFinalSig.retBits 32) :=
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

theorem ofbFinalOut (stack : Nat) : PostOut (ofbFinalContract Arm.abi stack) (ofbFinalSig.retBits 32) :=
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

/-! ## The code: its frames, and no indirect call -/

theorem expandKey_noFrames : Impl.Idea.Arm.expandKey.noFrames = true := by lit_decide

theorem invertKey_code : armStack Impl.Idea.Arm.invertKey = 0 ∧
    noIcall Impl.Idea.Arm.invertKey = true := by lit_decide

theorem ecb_code : armStack Impl.Idea.Arm.ecb = 0 ∧ noIcall Impl.Idea.Arm.ecb = true := by lit_decide

theorem frameOk_24 : FrameOk 24 := by decide
theorem frameOk_32 : FrameOk 32 := by decide
theorem invertKey_scrub :
    CodeOk (Impl.StackScratch.Arm.withRegScratch 24 .r2 Impl.Idea.Arm.invertKey) 24 :=
  CodeOk.alloc (n := 0) (CodeOk.seq (CodeOk.block _) ⟨Nat.le_of_eq invertKey_code.1, invertKey_code.2⟩)

theorem ecbCode_scrub : CodeOk Impl.Idea.Arm.ecbCode 32 :=
  CodeOk.alloc (n := 0) (CodeOk.seq (CodeOk.block _) ⟨Nat.le_of_eq ecb_code.1, ecb_code.2⟩)

end VG.Proof.Idea.Arm.Scrub

namespace VG.Proof.Idea.Arm.Fn

open VG VG.Spec.Idea VG.Arm VG.Arm.Scrub

/-- `vg_idea_expand_key`. -/
theorem expandKey :
    VerifiedScrubbed target Impl.Idea.Arm.Fn.expandKey (expandKeyContract Arm.abi) 0 :=
  verifiedScrubbed (api := expandKeyApi)
    { code := Impl.Idea.Arm.expandKey, verified := Proof.Idea.Arm.expandKey_verified }
    Scrub.expandKey_noFrames

/-- `vg_idea_invert_key`. -/
theorem invertKey :
    VerifiedScrubbed target Impl.Idea.Arm.Fn.invertKey (invertKeyContract Arm.abi 24) 0 :=
  verifiedScrubbedAll (api := invertKeyApi)
    { code := Impl.StackScratch.Arm.withRegScratch 24 .r2 Impl.Idea.Arm.invertKey
      verified := Proof.Idea.Arm.invertKey_framed }
    (Scrub.invertKeyOut _) (scrubSideF_of Scrub.invertKey_scrub Scrub.frameOk_24 _)

/-- `vg_idea_ecb`. -/
theorem ecb : VerifiedScrubbed target Impl.Idea.Arm.Fn.ecb (ecbContract Arm.abi 32) 0 :=
  verifiedScrubbedAll (api := ecbApi)
    { code := Impl.Idea.Arm.ecbCode, verified := Proof.Idea.Arm.ecb_framed }
    (Scrub.ecbOut _) (scrubSideF_of Scrub.ecbCode_scrub Scrub.frameOk_32 _)

/-- `vg_idea_cbc_encrypt_chained`. -/
theorem cbcEncryptChained : VerifiedScrubbed target Impl.Idea.Arm.Fn.cbcEncryptChained (cbcEncryptChainedContract Arm.abi 96) 0 :=
  verifiedScrubbedSel (api := cbcEncryptChainedApi) (W := 96)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Idea.Arm.cbcEncryptChained
      verified := Proof.Idea.Arm.cbcEncryptChained_framed }
    Impl.Idea.Arm.Fn.modeWords []
    (Scrub.cbcEncryptOut _)
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_idea_cbc_decrypt_chained`. -/
theorem cbcDecryptChained : VerifiedScrubbed target Impl.Idea.Arm.Fn.cbcDecryptChained (cbcDecryptChainedContract Arm.abi 96) 0 :=
  verifiedScrubbedSel (api := cbcDecryptChainedApi) (W := 96)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Idea.Arm.cbcDecryptChained
      verified := Proof.Idea.Arm.cbcDecryptChained_framed }
    Impl.Idea.Arm.Fn.modeWords []
    (Scrub.cbcDecryptOut _)
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_idea_cfb64_encrypt`. -/
theorem cfbEncrypt : VerifiedScrubbed target Impl.Idea.Arm.Fn.cfbEncrypt (cfbEncryptContract Arm.abi 96) 0 :=
  verifiedScrubbedSel (api := cfbEncryptApi) (W := 96)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Idea.Arm.cfbEncrypt
      verified := Proof.Idea.Arm.cfbEncrypt_framed }
    Impl.Idea.Arm.Fn.modeWords []
    (Scrub.cfbEncryptOut _)
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_idea_cfb64_decrypt`. -/
theorem cfbDecrypt : VerifiedScrubbed target Impl.Idea.Arm.Fn.cfbDecrypt (cfbDecryptContract Arm.abi 96) 0 :=
  verifiedScrubbedSel (api := cfbDecryptApi) (W := 96)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Idea.Arm.cfbDecrypt
      verified := Proof.Idea.Arm.cfbDecrypt_framed }
    Impl.Idea.Arm.Fn.modeWords []
    (Scrub.cfbDecryptOut _)
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_idea_cfb64_encrypt_final`. -/
theorem cfbEncryptFinal : VerifiedScrubbed target Impl.Idea.Arm.Fn.cfbEncryptFinal (cfbEncryptFinalContract Arm.abi 96) 0 :=
  verifiedScrubbedSel (api := cfbEncryptFinalApi) (W := 96)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Idea.Arm.cfbEncryptFinal
      verified := Proof.Idea.Arm.cfbEncryptFinal_framed }
    Impl.Idea.Arm.Fn.modeWords []
    (Scrub.cfbEncryptFinalOut _)
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_idea_cfb64_decrypt_final`. -/
theorem cfbDecryptFinal : VerifiedScrubbed target Impl.Idea.Arm.Fn.cfbDecryptFinal (cfbDecryptFinalContract Arm.abi 96) 0 :=
  verifiedScrubbedSel (api := cfbDecryptFinalApi) (W := 96)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Idea.Arm.cfbDecryptFinal
      verified := Proof.Idea.Arm.cfbDecryptFinal_framed }
    Impl.Idea.Arm.Fn.modeWords []
    (Scrub.cfbDecryptFinalOut _)
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_idea_ofb`. -/
theorem ofb : VerifiedScrubbed target Impl.Idea.Arm.Fn.ofb (ofbContract Arm.abi 96) 0 :=
  verifiedScrubbedSel (api := ofbApi) (W := 96)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Idea.Arm.ofb
      verified := Proof.Idea.Arm.ofb_framed }
    Impl.Idea.Arm.Fn.modeWords []
    (Scrub.ofbOut _)
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_idea_ofb_final`. -/
theorem ofbFinal : VerifiedScrubbed target Impl.Idea.Arm.Fn.ofbFinal (ofbFinalContract Arm.abi 96) 0 :=
  verifiedScrubbedSel (api := ofbFinalApi) (W := 96)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Idea.Arm.ofbFinal
      verified := Proof.Idea.Arm.ofbFinal_framed }
    Impl.Idea.Arm.Fn.modeWords []
    (Scrub.ofbFinalOut _)
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

end VG.Proof.Idea.Arm.Fn
