module

public import VerifiedGarbage.Spec.Blowfish.Contract
public import VerifiedGarbage.Spec.Blowfish.Cbc
public import VerifiedGarbage.Spec.Blowfish.Cfb
public import VerifiedGarbage.Spec.Blowfish.CfbFinal
public import VerifiedGarbage.Spec.Blowfish.Ofb
public import VerifiedGarbage.Spec.Blowfish.OfbFinal
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Framework.Arm.ScrubSel
public import VerifiedGarbage.Impl.Blowfish.Arm.Fn
public import VerifiedGarbage.Proof.Blowfish.Arm.Frame
public import VerifiedGarbage.Proof.Blowfish.Arm.CbcVerified
public import VerifiedGarbage.Proof.Blowfish.Arm.FbVerified
public import VerifiedGarbage.Proof.Blowfish.Arm.FbFinalVerified
public import VerifiedGarbage.Proof.Modes.Arm.ScrubCode
import VerifiedGarbage.Proof.Blowfish.ScrubLocal
import VerifiedGarbage.Proof.Blowfish.Arm.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Spec.Blowfish.Contract
meta import VerifiedGarbage.Spec.Blowfish.Cbc
meta import VerifiedGarbage.Spec.Blowfish.Cfb
meta import VerifiedGarbage.Spec.Blowfish.CfbFinal
meta import VerifiedGarbage.Spec.Blowfish.Ofb
meta import VerifiedGarbage.Spec.Blowfish.OfbFinal
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubSel
meta import VerifiedGarbage.Impl.Blowfish.Arm.Fn
meta import VerifiedGarbage.Proof.Blowfish.Arm.Frame
meta import VerifiedGarbage.Proof.Blowfish.Arm.CbcVerified
meta import VerifiedGarbage.Proof.Blowfish.Arm.FbVerified
meta import VerifiedGarbage.Proof.Blowfish.Arm.FbFinalVerified
meta import VerifiedGarbage.Proof.Modes.Arm.ScrubCode
meta import VerifiedGarbage.Proof.Blowfish.ScrubLocal
meta import VerifiedGarbage.Proof.Blowfish.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# Blowfish on ARMv7, without secret residue

The eleven Blowfish functions with their cleanup (`Impl.Blowfish.Arm.Fn`):
each zeroes the stack its contract reserves and returns with the registers a
callee may change set to constants (`Arm.Scrub.verifiedScrubbedAll`). Key
expansion, which wipes its working space, zeroes only the words of that
stack that the residue analysis (`Arm.rtaint`) finds may differ between two
runs (`Arm.Scrub.verifiedScrubbedSel`, whose analysis the kernel evaluates
here: `taint_decide_ct`); ECB and the modes leave most of theirs secret, and
keep the loop of `scrubAll`, the shorter code. Key
expansion and ECB keep their working space in a frame of 96 and 256 bytes
(`withRegScratchWiped`); the modes keep theirs in a frame of 64 bytes and
call ECB's code, with its frame, under a name of its own
(`vg_blowfish_ecb_encrypt_entry`, `Impl.Blowfish.Arm.ecbCore`), which the
emitter writes as an internal function: 320 bytes in all. What the cleanup
of ECB and the modes needs of their code (`CodeOk`) follows from ECB's,
evaluated once by `lit_decide`, through the generic modes'
(`Proof/Modes/Arm/ScrubCode.lean`), and their postconditions read the memory
on return only within the buffers (`Arm.Scrub.PostOut`), as on x86
(`Proof/Blowfish/X86/Scrub.lean`); a length is the low 32 bits of its
argument word.
-/

@[expose] public section

namespace VG

materialize_code Impl.Blowfish.Arm.expandKey

end VG

namespace VG.Proof.Blowfish.Arm.Scrub

open VG VG.Spec.Blowfish VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Proof.Modes.Arm
open VG.Proof.Blowfish.ScrubLocal

/-! ## Postconditions -/

theorem len_le (ln : BitVec 64) (k : Nat) :
    ((ArgWord.int Arm.abi.ptrBits).ofRaw ln).toNat * k ≤ ln.toNat * k :=
  Nat.mul_le_mul_right _ (by simp only [ArgWord.ofRaw, BitVec.toNat_setWidth]; exact Nat.mod_le _ _)

theorem len_le1 (ln : BitVec 64) : ((ArgWord.int Arm.abi.ptrBits).ofRaw ln).toNat ≤ ln.toNat * Elem.u8.size := by
  have := len_le ln 1
  simpa only [Nat.mul_one, Elem.size] using this

theorem expandKeyOut (stack : Nat) :
    PostOut (expandKeyContract (Arm.abi.withConsts Impl.Blowfish.Arm.initConsts) stack) (expandKeySig.retBits 32) :=
  postOut_of_local (leak := none) (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
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

theorem ecbOut (d : Direction) (stack : Nat) : PostOut (ecbContract Arm.abi d stack) (ecbSig.retBits 32) :=
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

/-! ## The code: frames and indirect calls -/

theorem encrypt_armStack : armStack Impl.Blowfish.Arm.encrypt ≤ 0 := by lit_decide
theorem encrypt_noIcall : noIcall Impl.Blowfish.Arm.encrypt = true := by lit_decide
theorem decrypt_armStack : armStack Impl.Blowfish.Arm.decrypt ≤ 0 := by lit_decide
theorem decrypt_noIcall : noIcall Impl.Blowfish.Arm.decrypt = true := by lit_decide

/-- ECB's code, in its 256-byte scratch frame. -/
theorem ecbCode_ok (up : Bool) : CodeOk (Impl.Blowfish.Arm.ecbCode up) 256 := by
  cases up
  · exact withRegScratchWiped_scrubArm (n := 0) ⟨decrypt_armStack, decrypt_noIcall⟩
  · exact withRegScratchWiped_scrubArm (n := 0) ⟨encrypt_armStack, encrypt_noIcall⟩

/-- ECB's code, as the modes call it: it takes no working space of theirs,
so its call needs no frame. -/
theorem ecbCore_ok (up : Bool) :
    armStack (Impl.Blowfish.Arm.ecbCore up).code + callExtraArm (Impl.Blowfish.Arm.ecbCore up) ≤ 256 ∧
      noIcall (Impl.Blowfish.Arm.ecbCore up).code = true :=
  ecbCode_ok up

/-- A mode one block at a time, in its 64-byte scratch frame. -/
theorem seq_ok (up : Bool) (m : Impl.Modes.Arm.Mode) :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 ((Impl.Blowfish.Arm.ecbCore up).seq m)) 320 :=
  withStackScratchWiped_scrubArm (seq_scrubArm (ecbCore_ok up) m)

/-- A mode over a message's last piece, in its 64-byte scratch frame. -/
theorem seqFinal_ok (up : Bool) (m : Impl.Modes.Arm.Mode) :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 ((Impl.Blowfish.Arm.ecbCore up).seqFinal m)) 320 :=
  withStackScratchWiped_scrubArm (seqFinal_scrubArm (ecbCore_ok up) m)

theorem frameOk_256 : FrameOk 256 := by decide
theorem frameOk_320 : FrameOk 320 := by decide

end VG.Proof.Blowfish.Arm.Scrub

namespace VG.Proof.Blowfish.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_blowfish_expand_key`. -/
theorem expandKey :
    VerifiedScrubbed target Impl.Blowfish.Arm.Fn.expandKey
      (Spec.Blowfish.expandKeyContract (abi.withConsts Impl.Blowfish.Arm.initConsts) 96) 0 :=
  verifiedScrubbedSel (api := Spec.Blowfish.expandKeyApi) (W := 96)
    { code := Impl.StackScratch.Arm.withRegScratchWiped 96 .r3 20 Impl.Blowfish.Arm.expandKey
      verified := Proof.Blowfish.Arm.expandKey_framed }
    Impl.Blowfish.Arm.Fn.expandKeyWords []
    (Scrub.expandKeyOut 96)
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_blowfish_ecb_encrypt`. -/
theorem ecbEncrypt :
    VerifiedScrubbed target Impl.Blowfish.Arm.Fn.ecbEncrypt (Spec.Blowfish.ecbEncryptContract abi 256) 0 :=
  verifiedScrubbedAll (api := Spec.Blowfish.ecbEncryptApi)
    { code := Impl.Blowfish.Arm.ecbCode true, verified := Proof.Blowfish.Arm.ecb_framed true }
    (Scrub.ecbOut .encrypt 256) (scrubSideF_of (Scrub.ecbCode_ok true) Scrub.frameOk_256 _)

/-- `vg_blowfish_ecb_decrypt`. -/
theorem ecbDecrypt :
    VerifiedScrubbed target Impl.Blowfish.Arm.Fn.ecbDecrypt (Spec.Blowfish.ecbDecryptContract abi 256) 0 :=
  verifiedScrubbedAll (api := Spec.Blowfish.ecbDecryptApi)
    { code := Impl.Blowfish.Arm.ecbCode false, verified := Proof.Blowfish.Arm.ecb_framed false }
    (Scrub.ecbOut .decrypt 256) (scrubSideF_of (Scrub.ecbCode_ok false) Scrub.frameOk_256 _)

/-- `vg_blowfish_cbc_encrypt_chained`. -/
theorem cbcEncryptChained :
    VerifiedScrubbed target Impl.Blowfish.Arm.Fn.cbcEncryptChained (Spec.Blowfish.cbcEncryptChainedContract abi 320) 0 :=
  verifiedScrubbedAll (api := Spec.Blowfish.cbcEncryptChainedApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.cbcEncryptChained
      verified := Proof.Blowfish.Arm.cbcEncryptChained_framed }
    (Scrub.cbcEncryptOut 320) (scrubSideF_of (Scrub.seq_ok true Impl.Modes.Arm.cbcEncChained) Scrub.frameOk_320 _)

/-- `vg_blowfish_cbc_decrypt_chained`. -/
theorem cbcDecryptChained :
    VerifiedScrubbed target Impl.Blowfish.Arm.Fn.cbcDecryptChained (Spec.Blowfish.cbcDecryptChainedContract abi 320) 0 :=
  verifiedScrubbedAll (api := Spec.Blowfish.cbcDecryptChainedApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.cbcDecryptChained
      verified := Proof.Blowfish.Arm.cbcDecryptChained_framed }
    (Scrub.cbcDecryptOut 320) (scrubSideF_of (Scrub.seq_ok false Impl.Modes.Arm.cbcDecChained) Scrub.frameOk_320 _)

/-- `vg_blowfish_cfb64_encrypt`. -/
theorem cfbEncrypt :
    VerifiedScrubbed target Impl.Blowfish.Arm.Fn.cfbEncrypt (Spec.Blowfish.cfbEncryptContract abi 320) 0 :=
  verifiedScrubbedAll (api := Spec.Blowfish.cfbEncryptApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.cfbEncrypt
      verified := Proof.Blowfish.Arm.cfbEncrypt_framed }
    (Scrub.cfbEncryptOut 320) (scrubSideF_of (Scrub.seq_ok true Impl.Modes.Arm.cfbEnc) Scrub.frameOk_320 _)

/-- `vg_blowfish_cfb64_decrypt`. -/
theorem cfbDecrypt :
    VerifiedScrubbed target Impl.Blowfish.Arm.Fn.cfbDecrypt (Spec.Blowfish.cfbDecryptContract abi 320) 0 :=
  verifiedScrubbedAll (api := Spec.Blowfish.cfbDecryptApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.cfbDecrypt
      verified := Proof.Blowfish.Arm.cfbDecrypt_framed }
    (Scrub.cfbDecryptOut 320) (scrubSideF_of (Scrub.seq_ok true Impl.Modes.Arm.cfbDec) Scrub.frameOk_320 _)

/-- `vg_blowfish_cfb64_encrypt_final`. -/
theorem cfbEncryptFinal :
    VerifiedScrubbed target Impl.Blowfish.Arm.Fn.cfbEncryptFinal (Spec.Blowfish.cfbEncryptFinalContract abi 320) 0 :=
  verifiedScrubbedAll (api := Spec.Blowfish.cfbEncryptFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.cfbEncryptFinal
      verified := Proof.Blowfish.Arm.cfbEncryptFinal_framed }
    (Scrub.cfbEncryptFinalOut 320) (scrubSideF_of (Scrub.seqFinal_ok true Impl.Modes.Arm.cfbEnc) Scrub.frameOk_320 _)

/-- `vg_blowfish_cfb64_decrypt_final`. -/
theorem cfbDecryptFinal :
    VerifiedScrubbed target Impl.Blowfish.Arm.Fn.cfbDecryptFinal (Spec.Blowfish.cfbDecryptFinalContract abi 320) 0 :=
  verifiedScrubbedAll (api := Spec.Blowfish.cfbDecryptFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.cfbDecryptFinal
      verified := Proof.Blowfish.Arm.cfbDecryptFinal_framed }
    (Scrub.cfbDecryptFinalOut 320) (scrubSideF_of (Scrub.seqFinal_ok true Impl.Modes.Arm.cfbDecF) Scrub.frameOk_320 _)

/-- `vg_blowfish_ofb`. -/
theorem ofb :
    VerifiedScrubbed target Impl.Blowfish.Arm.Fn.ofb (Spec.Blowfish.ofbContract abi 320) 0 :=
  verifiedScrubbedAll (api := Spec.Blowfish.ofbApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.ofb
      verified := Proof.Blowfish.Arm.ofb_framed }
    (Scrub.ofbOut 320) (scrubSideF_of (Scrub.seq_ok true Impl.Modes.Arm.ofb) Scrub.frameOk_320 _)

/-- `vg_blowfish_ofb_final`. -/
theorem ofbFinal :
    VerifiedScrubbed target Impl.Blowfish.Arm.Fn.ofbFinal (Spec.Blowfish.ofbFinalContract abi 320) 0 :=
  verifiedScrubbedAll (api := Spec.Blowfish.ofbFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.ofbFinal
      verified := Proof.Blowfish.Arm.ofbFinal_framed }
    (Scrub.ofbFinalOut 320) (scrubSideF_of (Scrub.seqFinal_ok true Impl.Modes.Arm.ofb) Scrub.frameOk_320 _)

end VG.Proof.Blowfish.Arm.Fn
