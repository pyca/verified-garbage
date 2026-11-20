module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Framework.Arm.ScrubSel
public import VerifiedGarbage.Impl.Camellia.Arm.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Camellia.Arm.KeyVerified
public import VerifiedGarbage.Proof.Camellia.Arm.Verified
public import VerifiedGarbage.Proof.Camellia.Arm.CbcVerified
public import VerifiedGarbage.Proof.Camellia.Arm.FbVerified
public import VerifiedGarbage.Proof.Camellia.Arm.FbFinalVerified
public import VerifiedGarbage.Proof.Camellia.Arm.CtrVerified
public import VerifiedGarbage.Proof.Camellia.Arm.CtrFinal
public import VerifiedGarbage.Impl.Camellia.Arm.FbFinal
public import VerifiedGarbage.Proof.Modes.Arm.ScrubCode
public import VerifiedGarbage.Proof.Camellia.ScrubLocal
import VerifiedGarbage.Proof.Camellia.Scratch
import VerifiedGarbage.Proof.Camellia.Arm.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubSel
meta import VerifiedGarbage.Impl.Camellia.Arm.Fn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Camellia.Arm.KeyVerified
meta import VerifiedGarbage.Proof.Camellia.Arm.Verified
meta import VerifiedGarbage.Proof.Camellia.Arm.CbcVerified
meta import VerifiedGarbage.Proof.Camellia.Arm.FbVerified
meta import VerifiedGarbage.Proof.Camellia.Arm.FbFinalVerified
meta import VerifiedGarbage.Proof.Camellia.Arm.CtrVerified
meta import VerifiedGarbage.Proof.Camellia.Arm.CtrFinal
meta import VerifiedGarbage.Impl.Camellia.Arm.FbFinal
meta import VerifiedGarbage.Proof.Modes.Arm.ScrubCode
meta import VerifiedGarbage.Proof.Camellia.ScrubLocal
meta import VerifiedGarbage.Proof.Camellia.Scratch
meta import VerifiedGarbage.Proof.Camellia.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# Camellia on ARMv7, without secret residue

Every public function of Camellia on ARMv7 keeps its working space in a
frame: key expansion's 2720 bytes (`withRegScratchWiped`), ECB's 2816
(`withStackScratchWiped`), the modes one block at a time 2816 bytes of
their own (the table of subkeys built once, `Impl/Modes/Arm/SeqKeyed.lean`),
the modes in groups of blocks (`Impl/Modes/Arm/Wide.lean`) and over a
message's last piece 88 bytes of their own around ECB's 2816 and the groups'
128, and CTR over a message's last piece 72 bytes around CTR's. None makes
an indirect call, and their postconditions read the memory on return only
within their buffers (`Arm.Scrub.PostOut`, from the lemmas of
`Proof/Camellia/ScrubLocal.lean` that RISC-V uses too). Each wipes its own
working space, and is emitted followed by a wipe of only the words of the
stack its contract reserves (rounded up to a frame size the model accepts,
`Arm.Scrub.Verified.stack_le`) that the residue analysis finds may differ
between two runs (`Impl.Residue.Arm.scrubSel`), and by instructions that
set the registers a callee may change, but the result, and the flags to
constants (`Impl.Camellia.Arm.Fn`). `Fn` below states that each returns
without secret residue (`Arm.Scrub.verifiedScrubbedSel`, whose analysis,
`Arm.rtaint`, the kernel evaluates here: `taint_decide_ct`), which is what
its registration binds.

The modes call ECB's and CTR's code as it is verified, without the wipe,
under names of their own (`vg_camellia_ecb_encrypt_entry`,
`Impl.Camellia.Arm.ecbCore`; `vg_camellia_ctr_entry`,
`Impl.Camellia.Arm.ctrCall`), which the emitter writes as internal
functions: the analysis of each mode covers the frame of that call.
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm.Scrub

open VG VG.Spec.Camellia VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Proof.Modes.Arm
open VG.Proof.Camellia.ScrubLocal

/-! ## The postconditions -/

theorem len_le (x : BitVec 64) (k : Nat) : ((ArgWord.int Arm.abi.ptrBits).ofRaw x).toNat * k ≤ x.toNat * k :=
  Nat.mul_le_mul_right _ (by
    simp only [ArgWord.ofRaw, BitVec.toNat_setWidth]
    exact Nat.mod_le _ _)

theorem len_le1 (x : BitVec 64) : ((ArgWord.int Arm.abi.ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size := by
  have := len_le x 1
  simpa only [Nat.mul_one, Elem.size] using this

theorem expandKeyOut (stack : Nat) : PostOut (expandKeyContract Arm.abi stack) (expandKeySig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Camellia.expandKeyPostOut_local _)

theorem ecbOut (d : Direction) (stack : Nat) : PostOut (ecbContract Arm.abi d stack) (ecbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, dt, ln], _ =>
      simp only [ecbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → blocksAt m₂ dt _ = _
      intro key hk
      rw [blocksAt_of hb.2 (len_le ln 16)]
      exact h key hk

/-- The postcondition of a mode of whole blocks: its blocks and its IV (or
counter block). -/
theorem cbcEncryptOut (stack : Nat) :
    PostOut (cbcEncryptChainedContract Arm.abi stack) (cbcChainedSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cbcDecryptOut (stack : Nat) :
    PostOut (cbcDecryptChainedContract Arm.abi stack) (cbcChainedSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptOut (stack : Nat) : PostOut (cfbEncryptContract Arm.abi stack) (cfbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptOut (stack : Nat) : PostOut (cfbDecryptContract Arm.abi stack) (cfbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbOut (stack : Nat) : PostOut (ofbContract Arm.abi stack) (ofbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ctrOut (stack : Nat) : PostOut (ctrContract Arm.abi stack) (ctrSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, ct, dt, ln], _ =>
      simp only [ctrSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ ct 16 = _
      intro key hk
      rw [cbcBlocksAt_of hb.2.2 (len_le ln 16), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptFinalOut (stack : Nat) :
    PostOut (cfbEncryptFinalContract Arm.abi stack) (cfbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [aesBytesAt_of hb.2.2 (len_le1 ln), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptFinalOut (stack : Nat) :
    PostOut (cfbDecryptFinalContract Arm.abi stack) (cfbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [aesBytesAt_of hb.2.2 (len_le1 ln), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbFinalOut (stack : Nat) : PostOut (ofbFinalContract Arm.abi stack) (ofbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [ofbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [aesBytesAt_of hb.2.2 (len_le1 ln), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ctrFinalOut (stack : Nat) :
    PostOut (ctrFinalContract Arm.abi stack) (ctrFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, ct, dt, ln], _ =>
      simp only [ctrFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ ct 16 = _
      intro key hk
      rw [aesBytesAt_of hb.2.2 (len_le1 ln), aesBytesAt_of (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

/-! ## The code as literals

The code of the table's construction and of the encipherment from it, as
literals, which the residue analysis of the modes (`taint_decide_ct`) reads. -/
materialize_flat_code ecbKeysEncrypt := Impl.Camellia.Arm.ecbKeys .encrypt
materialize_flat_code ecbKeyedCode := Impl.Camellia.Arm.ecbKeyed

/-! ## The stack, rounded up to a frame size -/

theorem cbcEncryptSat : ∃ s, (cbcEncryptChainedContract Arm.abi 2832).pre s := by
  implies_sat [cbcEncryptChainedContract, cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [cbcFrameSat, cbcSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using cbcFrameSat 0

theorem cbcDecryptSat : ∃ s, (cbcDecryptChainedContract Arm.abi 3040).pre s := by
  implies_sat [cbcDecryptChainedContract, cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [cbcFrameSat, cbcSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using cbcFrameSat 0

theorem cfbEncryptSat : ∃ s, (cfbEncryptContract Arm.abi 2832).pre s := by
  implies_sat [cfbEncryptContract, cfbSig, cfbPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [fbFrameSat, fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbFrameSat 0

theorem cfbDecryptSat : ∃ s, (cfbDecryptContract Arm.abi 3040).pre s := by
  implies_sat [cfbDecryptContract, cfbSig, cfbPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [fbFrameSat, fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbFrameSat 0

theorem ofbSat : ∃ s, (ofbContract Arm.abi 2832).pre s := by
  implies_sat [ofbContract, ofbSig, ofbPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [fbFrameSat, fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbFrameSat 0

theorem ctrSat : ∃ s, (ctrContract Arm.abi 3040).pre s := by
  implies_sat [ctrContract, ctrSig, ctrPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [fbFrameSat, fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbFrameSat 0

theorem cfbEncryptFinalSat : ∃ s, (cfbEncryptFinalContract Arm.abi 2912).pre s := by
  implies_sat [cfbEncryptFinalContract, cfbFinalSig, cfbFinalPre, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [fbFrameSat, fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbFrameSat 0

theorem cfbDecryptFinalSat : ∃ s, (cfbDecryptFinalContract Arm.abi 2912).pre s := by
  implies_sat [cfbDecryptFinalContract, cfbFinalSig, cfbFinalPre, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [fbFrameSat, fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbFrameSat 0

theorem ofbFinalSat : ∃ s, (ofbFinalContract Arm.abi 2912).pre s := by
  implies_sat [ofbFinalContract, ofbFinalSig, ofbFinalPre, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [fbFrameSat, fbSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using fbFrameSat 0

theorem ctrFinalSat : ∃ s, (ctrFinalContract Arm.abi 3120).pre s := by
  implies_sat [ctrFinalContract, ctrFinalSig, ctrFinalPre, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [CtrFinal.ctrFinalFrameSat, CtrFinal.ctrFinalSat] using CtrFinal.ctrFinalFrameSat

end VG.Proof.Camellia.Arm.Scrub

namespace VG.Proof.Camellia.Arm.Fn

open VG VG.Spec.Camellia VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Proof.Modes.Arm
open VG.Proof.Camellia.ScrubLocal

/-- `vg_camellia_expand_key`. -/
theorem expandKey :
    VerifiedScrubbed target Impl.Camellia.Arm.Fn.expandKey (expandKeyContract Arm.abi 2720) 0 :=
  verifiedScrubbedSel (api := expandKeyApi) (W := 2720)
    { code := Impl.StackScratch.Arm.withRegScratchWiped 2720 .r3 680 Impl.Camellia.Arm.expandKey
      verified := Proof.Camellia.Arm.expandKey_framed }
    Impl.Camellia.Arm.Fn.expandKeyWords []
    (Scrub.expandKeyOut _) (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_camellia_ecb_encrypt`. -/
theorem ecbEncrypt :
    VerifiedScrubbed target Impl.Camellia.Arm.Fn.ecbEncrypt (ecbContract Arm.abi .encrypt 2816) 0 :=
  verifiedScrubbedSel (api := ecbEncryptApi) (W := 2816)
    { code := Impl.Camellia.Arm.ecbCode .encrypt
      verified := Proof.Camellia.Arm.ecb_framed .encrypt }
    Impl.Camellia.Arm.Fn.ecbWords []
    (Scrub.ecbOut .encrypt _) (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_camellia_ecb_decrypt`. -/
theorem ecbDecrypt :
    VerifiedScrubbed target Impl.Camellia.Arm.Fn.ecbDecrypt (ecbContract Arm.abi .decrypt 2816) 0 :=
  verifiedScrubbedSel (api := ecbDecryptApi) (W := 2816)
    { code := Impl.Camellia.Arm.ecbCode .decrypt
      verified := Proof.Camellia.Arm.ecb_framed .decrypt }
    Impl.Camellia.Arm.Fn.ecbWords []
    (Scrub.ecbOut .decrypt _) (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_camellia_cbc_encrypt_chained`. -/
theorem cbcEncrypt :
    VerifiedScrubbed target Impl.Camellia.Arm.Fn.cbcEncrypt (cbcEncryptChainedContract Arm.abi 2832) 0 :=
  verifiedScrubbedSel (api := cbcEncryptChainedApi) (W := 2832)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 2816 1 698 Impl.Camellia.Arm.cbcEncryptChained
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.cbcEncryptChained_framed Scrub.cbcEncryptSat }
    Impl.Camellia.Arm.Fn.seqWords []
    (Scrub.cbcEncryptOut _) (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_camellia_cbc_decrypt_chained`. -/
theorem cbcDecrypt :
    VerifiedScrubbed target Impl.Camellia.Arm.Fn.cbcDecrypt (cbcDecryptChainedContract Arm.abi 3040) 0 :=
  verifiedScrubbedSel (api := cbcDecryptChainedApi) (W := 3040)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cbcDecryptChained
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.cbcDecryptChained_framed Scrub.cbcDecryptSat }
    Impl.Camellia.Arm.Fn.wideWords []
    (Scrub.cbcDecryptOut _) (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_camellia_cfb128_encrypt`. -/
theorem cfbEncrypt :
    VerifiedScrubbed target Impl.Camellia.Arm.Fn.cfbEncrypt (cfbEncryptContract Arm.abi 2832) 0 :=
  verifiedScrubbedSel (api := cfbEncryptApi) (W := 2832)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 2816 1 698 Impl.Camellia.Arm.cfbEncrypt
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.cfbEncrypt_framed Scrub.cfbEncryptSat }
    Impl.Camellia.Arm.Fn.seqWords []
    (Scrub.cfbEncryptOut _) (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_camellia_cfb128_decrypt`. -/
theorem cfbDecrypt :
    VerifiedScrubbed target Impl.Camellia.Arm.Fn.cfbDecrypt (cfbDecryptContract Arm.abi 3040) 0 :=
  verifiedScrubbedSel (api := cfbDecryptApi) (W := 3040)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cfbDecrypt
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.cfbDecrypt_framed Scrub.cfbDecryptSat }
    Impl.Camellia.Arm.Fn.wideWords []
    (Scrub.cfbDecryptOut _) (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_camellia_cfb128_encrypt_final`. -/
theorem cfbEncryptFinal :
    VerifiedScrubbed target Impl.Camellia.Arm.Fn.cfbEncryptFinal (cfbEncryptFinalContract Arm.abi 2912) 0 :=
  verifiedScrubbedSel (api := cfbEncryptFinalApi) (W := 2912)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cfbEncryptFinal
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.cfbEncryptFinal_framed Scrub.cfbEncryptFinalSat }
    Impl.Camellia.Arm.Fn.finalWords []
    (Scrub.cfbEncryptFinalOut _) (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_camellia_cfb128_decrypt_final`. -/
theorem cfbDecryptFinal :
    VerifiedScrubbed target Impl.Camellia.Arm.Fn.cfbDecryptFinal (cfbDecryptFinalContract Arm.abi 2912) 0 :=
  verifiedScrubbedSel (api := cfbDecryptFinalApi) (W := 2912)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cfbDecryptFinal
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.cfbDecryptFinal_framed Scrub.cfbDecryptFinalSat }
    Impl.Camellia.Arm.Fn.finalWords []
    (Scrub.cfbDecryptFinalOut _) (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_camellia_ctr`. -/
theorem ctr : VerifiedScrubbed target Impl.Camellia.Arm.Fn.ctr (ctrContract Arm.abi 3040) 0 :=
  verifiedScrubbedSel (api := ctrApi) (W := 3040)
    { code := Impl.Camellia.Arm.ctrFramed
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.ctr_framed Scrub.ctrSat }
    Impl.Camellia.Arm.Fn.wideWords []
    (Scrub.ctrOut _) (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_camellia_ctr_final`. -/
theorem ctrFinal : VerifiedScrubbed target Impl.Camellia.Arm.Fn.ctrFinal (ctrFinalContract Arm.abi 3120) 0 :=
  verifiedScrubbedSel (api := ctrFinalApi) (W := 3120)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 72 1 14 Impl.Camellia.Arm.ctrFinal
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.CtrFinal.ctrFinal_framed Scrub.ctrFinalSat }
    Impl.Camellia.Arm.Fn.ctrFinalWords []
    (Scrub.ctrFinalOut _) (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_camellia_ofb`. -/
theorem ofb : VerifiedScrubbed target Impl.Camellia.Arm.Fn.ofb (ofbContract Arm.abi 2832) 0 :=
  verifiedScrubbedSel (api := ofbApi) (W := 2832)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 2816 1 698 Impl.Camellia.Arm.ofb
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.ofb_framed Scrub.ofbSat }
    Impl.Camellia.Arm.Fn.seqWords []
    (Scrub.ofbOut _) (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_camellia_ofb_final`. -/
theorem ofbFinal : VerifiedScrubbed target Impl.Camellia.Arm.Fn.ofbFinal (ofbFinalContract Arm.abi 2912) 0 :=
  verifiedScrubbedSel (api := ofbFinalApi) (W := 2912)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.ofbFinal
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.ofbFinal_framed Scrub.ofbFinalSat }
    Impl.Camellia.Arm.Fn.finalWords []
    (Scrub.ofbFinalOut _) (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

end VG.Proof.Camellia.Arm.Fn
