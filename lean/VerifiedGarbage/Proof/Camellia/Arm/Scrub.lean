module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Modes.Arm.Wrap
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
meta import VerifiedGarbage.Proof.Modes.Arm.Wrap
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
frame, left as it is: key expansion's 2720 bytes (`withRegScratch`), the
modes one block at a time 2816 bytes of their own (the table of subkeys
built once, `Impl/Modes/Arm/SeqKeyed.lean`), the modes in groups of blocks
(`Impl/Modes/Arm/Wide.lean`) and over a message's last piece 88 bytes of
their own (`withStackScratch`) around the 2816 of the ECB core they call
(`Impl.Camellia.Arm.ecbCore`) and the groups' 128, and CTR over a message's
last piece 72 bytes around CTR's, whose code it calls under a name of its
own (`vg_camellia_ctr_entry`, `Impl.Camellia.Arm.ctrCall`). The ECB
functions call the core in a frame of 8 bytes (`Core.wrap`). None makes an
indirect call, and their postconditions read the memory on return only
within their buffers (`Arm.Scrub.PostOut`, from the lemmas of
`Proof/Camellia/ScrubLocal.lean` that RISC-V uses too). Each is emitted
followed by `scrubAll` (`Impl.Camellia.Arm.Fn`), which zeroes the stack its
contract reserves (rounded up to a frame size the model accepts,
`Arm.Scrub.Verified.stack_le`) in a loop and sets the registers a callee may
change, but the result, and the flags to constants. `Fn` below states that
each returns without secret residue (`Arm.Scrub.verifiedScrubbedAll`, given
that its frames are within that stack: `CodeOk`), which is what its
registration binds.
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
materialize_code ecbKeysEncrypt := Impl.Camellia.Arm.ecbKeys .encrypt
materialize_code ecbKeyedCode := Impl.Camellia.Arm.ecbKeyed

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

/-! ## The stack the functions zeroed in a loop use

The frames of the key expansion and of the modes one block at a time, which
`scrubAll` zeroes (`Arm.Scrub.CodeOk`). -/

theorem expandKey_code :
    CodeOk (Impl.StackScratch.Arm.withRegScratch 2720 .r3 Impl.Camellia.Arm.expandKey) 2720 := by
  lit_decide

theorem cbcEncrypt_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 2816 1 Impl.Camellia.Arm.cbcEncryptChained) 2832 := by
  lit_decide

theorem cfbEncrypt_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 2816 1 Impl.Camellia.Arm.cfbEncrypt) 2832 := by
  lit_decide

theorem ofb_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 2816 1 Impl.Camellia.Arm.ofb) 2832 := by
  lit_decide

theorem cbcDecrypt_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 88 1 Impl.Camellia.Arm.cbcDecryptChained) 3040 := by
  lit_decide

theorem cfbDecrypt_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 88 1 Impl.Camellia.Arm.cfbDecrypt) 3040 := by
  lit_decide

theorem cfbEncryptFinal_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 88 1 Impl.Camellia.Arm.cfbEncryptFinal) 2912 := by
  lit_decide

theorem cfbDecryptFinal_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 88 1 Impl.Camellia.Arm.cfbDecryptFinal) 2912 := by
  lit_decide

theorem ofbFinal_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 88 1 Impl.Camellia.Arm.ofbFinal) 2912 := by
  lit_decide

theorem ctr_code : CodeOk Impl.Camellia.Arm.ctrFramed 3040 := by
  unfold Impl.Camellia.Arm.ctrFramed; lit_decide

theorem ctrFinal_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 72 1 Impl.Camellia.Arm.ctrFinal) 3120 := by
  lit_decide

theorem ecbWrap_code (d : Impl.Camellia.Arm.Dir) : CodeOk (Impl.Camellia.Arm.ecbCore d).wrap 2832 :=
  CodeOk.push (n := 2824) (CodeOk.seq ((CodeOk.block _).mono (Nat.zero_le _))
    (CodeOk.seq (CodeOk.call ⟨Nat.le_trans (ecb_stack d) (by decide), by cases d <;> lit_decide⟩)
      ((CodeOk.block _).mono (Nat.zero_le _))))

/-! ## The ECB functions: a call of the core -/

/-- The public ECB functions' contract on the subkeys, with the 8 bytes of
the call's frame more than the core's, is what the call of the core meets. -/
theorem ecbWrap_implies (dir : Impl.Camellia.Arm.Dir) :
    (wrapContract (ecbSpec dir)).Implies (Proof.Camellia.ecbContractSk Arm.abi (specDir dir) 2824) where
  pre s h := by
    sig_pre [Proof.Camellia.ecbContractSk, Spec.Camellia.ecbSig, Spec.Camellia.ecbPre, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    obtain ⟨stk, -, rd, wr, kd, bk, bd, fK, fD, rr⟩ := h
    exact { stk := stk, rd := rd, wr := wr, kd := kd, bk := bk, bd := bd, fK := fK, fD := fD
            rr := fun _ => rr
            a3 := fun _ h => by cases h }
  post s s' _ h := by
    sig_post [Proof.Camellia.ecbContractSk, Spec.Camellia.ecbSig, Proof.Camellia.ecbPostSk, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    intro rr
    change VG.Proof.Modes.blocksOf 16 s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
      (VG.Proof.Modes.blocksOf 16 s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat).map
        (dirCipher dir (Spec.Camellia.subkeysAt s.mem (State.addr (s.gpr .r0)) (rsel (s.gpr .r1)))) at h
    rw [rsel_eq rr] at h
    simp only [State.addr] at h
    rw [blocksOf_eq, blocksOf_eq] at h
    refine (List.map_inj_right (fun a b e => Vector.toList_inj.mp e)).1 ?_
    rw [h, ecb_dir, List.map_map, List.map_map]
    exact List.map_congr_left fun v _ => dirCipher_toList dir _ v
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Camellia.ecbContractSk, Spec.Camellia.ecbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun _ => h.2.2.2.2⟩
  sat := by
    implies_sat [Proof.Camellia.ecbContractSk, Spec.Camellia.ecbSig, Spec.Camellia.ecbPre, Proof.Camellia.ecbPostSk,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [ecbFrameSat, ecbSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using ecbFrameSat

theorem ecbWrapSat (dir : Impl.Camellia.Arm.Dir) :
    ∃ s, (Proof.Camellia.ecbContractSk Arm.abi (specDir dir) 2832).pre s := by
  implies_sat [Proof.Camellia.ecbContractSk, Spec.Camellia.ecbSig, Spec.Camellia.ecbPre, Proof.Camellia.ecbPostSk,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [ecbFrameSat, ecbSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using ecbFrameSat

/-- The ECB functions, by their contract. -/
theorem ecbWrap_verified (dir : Impl.Camellia.Arm.Dir) :
    Verified Arm.target (Impl.Camellia.Arm.ecbCore dir).wrap
      (ecbContract Arm.abi (specDir dir) 2832) :=
  Proof.Camellia.ecb_of_sk (Verified.stack_le (by decide)
    (Proof.Modes.Arm.wrap_verified (ecbSpec dir) rfl (ecbWrap_implies dir)) (ecbWrapSat dir))

end VG.Proof.Camellia.Arm.Scrub

namespace VG.Proof.Camellia.Arm.Fn

open VG VG.Spec.Camellia VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Proof.Modes.Arm
open VG.Proof.Camellia.ScrubLocal

/-- `vg_camellia_expand_key`. -/
theorem expandKey :
    VerifiedScrubbed target Impl.Camellia.Arm.Fn.expandKey (expandKeyContract Arm.abi 2720) 0 :=
  verifiedScrubbedAll (api := expandKeyApi)
    { code := Impl.StackScratch.Arm.withRegScratch 2720 .r3 Impl.Camellia.Arm.expandKey
      verified := Proof.Camellia.Arm.expandKey_framed }
    (Scrub.expandKeyOut _) (scrubSideF_of Scrub.expandKey_code (by decide) _)

/-- `vg_camellia_ecb_encrypt`. -/
theorem ecbEncrypt :
    VerifiedScrubbed target Impl.Camellia.Arm.Fn.ecbEncrypt (ecbContract Arm.abi .encrypt 2832) 0 :=
  verifiedScrubbedAll (api := ecbEncryptApi)
    { code := (Impl.Camellia.Arm.ecbCore .encrypt).wrap
      verified := Scrub.ecbWrap_verified .encrypt }
    (Scrub.ecbOut .encrypt _) (scrubSideF_of (Scrub.ecbWrap_code .encrypt) (by decide) _)

/-- `vg_camellia_ecb_decrypt`. -/
theorem ecbDecrypt :
    VerifiedScrubbed target Impl.Camellia.Arm.Fn.ecbDecrypt (ecbContract Arm.abi .decrypt 2832) 0 :=
  verifiedScrubbedAll (api := ecbDecryptApi)
    { code := (Impl.Camellia.Arm.ecbCore .decrypt).wrap
      verified := Scrub.ecbWrap_verified .decrypt }
    (Scrub.ecbOut .decrypt _) (scrubSideF_of (Scrub.ecbWrap_code .decrypt) (by decide) _)

/-- `vg_camellia_cbc_encrypt_chained`. -/
theorem cbcEncrypt :
    VerifiedScrubbed target Impl.Camellia.Arm.Fn.cbcEncrypt (cbcEncryptChainedContract Arm.abi 2832) 0 :=
  verifiedScrubbedAll (api := cbcEncryptChainedApi)
    { code := Impl.StackScratch.Arm.withStackScratch 2816 1 Impl.Camellia.Arm.cbcEncryptChained
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.cbcEncryptChained_framed Scrub.cbcEncryptSat }
    (Scrub.cbcEncryptOut _) (scrubSideF_of Scrub.cbcEncrypt_code (by decide) _)

/-- `vg_camellia_cbc_decrypt_chained`. -/
theorem cbcDecrypt :
    VerifiedScrubbed target Impl.Camellia.Arm.Fn.cbcDecrypt (cbcDecryptChainedContract Arm.abi 3040) 0 :=
  verifiedScrubbedAll (api := cbcDecryptChainedApi)
    { code := Impl.StackScratch.Arm.withStackScratch 88 1 Impl.Camellia.Arm.cbcDecryptChained
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.cbcDecryptChained_framed Scrub.cbcDecryptSat }
    (Scrub.cbcDecryptOut _) (scrubSideF_of Scrub.cbcDecrypt_code (by decide) _)

/-- `vg_camellia_cfb128_encrypt`. -/
theorem cfbEncrypt :
    VerifiedScrubbed target Impl.Camellia.Arm.Fn.cfbEncrypt (cfbEncryptContract Arm.abi 2832) 0 :=
  verifiedScrubbedAll (api := cfbEncryptApi)
    { code := Impl.StackScratch.Arm.withStackScratch 2816 1 Impl.Camellia.Arm.cfbEncrypt
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.cfbEncrypt_framed Scrub.cfbEncryptSat }
    (Scrub.cfbEncryptOut _) (scrubSideF_of Scrub.cfbEncrypt_code (by decide) _)

/-- `vg_camellia_cfb128_decrypt`. -/
theorem cfbDecrypt :
    VerifiedScrubbed target Impl.Camellia.Arm.Fn.cfbDecrypt (cfbDecryptContract Arm.abi 3040) 0 :=
  verifiedScrubbedAll (api := cfbDecryptApi)
    { code := Impl.StackScratch.Arm.withStackScratch 88 1 Impl.Camellia.Arm.cfbDecrypt
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.cfbDecrypt_framed Scrub.cfbDecryptSat }
    (Scrub.cfbDecryptOut _) (scrubSideF_of Scrub.cfbDecrypt_code (by decide) _)

/-- `vg_camellia_cfb128_encrypt_final`. -/
theorem cfbEncryptFinal :
    VerifiedScrubbed target Impl.Camellia.Arm.Fn.cfbEncryptFinal (cfbEncryptFinalContract Arm.abi 2912) 0 :=
  verifiedScrubbedAll (api := cfbEncryptFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratch 88 1 Impl.Camellia.Arm.cfbEncryptFinal
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.cfbEncryptFinal_framed Scrub.cfbEncryptFinalSat }
    (Scrub.cfbEncryptFinalOut _) (scrubSideF_of Scrub.cfbEncryptFinal_code (by decide) _)

/-- `vg_camellia_cfb128_decrypt_final`. -/
theorem cfbDecryptFinal :
    VerifiedScrubbed target Impl.Camellia.Arm.Fn.cfbDecryptFinal (cfbDecryptFinalContract Arm.abi 2912) 0 :=
  verifiedScrubbedAll (api := cfbDecryptFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratch 88 1 Impl.Camellia.Arm.cfbDecryptFinal
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.cfbDecryptFinal_framed Scrub.cfbDecryptFinalSat }
    (Scrub.cfbDecryptFinalOut _) (scrubSideF_of Scrub.cfbDecryptFinal_code (by decide) _)

/-- `vg_camellia_ctr`. -/
theorem ctr : VerifiedScrubbed target Impl.Camellia.Arm.Fn.ctr (ctrContract Arm.abi 3040) 0 :=
  verifiedScrubbedAll (api := ctrApi)
    { code := Impl.Camellia.Arm.ctrFramed
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.ctr_framed Scrub.ctrSat }
    (Scrub.ctrOut _) (scrubSideF_of Scrub.ctr_code (by decide) _)

/-- `vg_camellia_ctr_final`. -/
theorem ctrFinal : VerifiedScrubbed target Impl.Camellia.Arm.Fn.ctrFinal (ctrFinalContract Arm.abi 3120) 0 :=
  verifiedScrubbedAll (api := ctrFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratch 72 1 Impl.Camellia.Arm.ctrFinal
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.CtrFinal.ctrFinal_framed Scrub.ctrFinalSat }
    (Scrub.ctrFinalOut _) (scrubSideF_of Scrub.ctrFinal_code (by decide) _)

/-- `vg_camellia_ofb`. -/
theorem ofb : VerifiedScrubbed target Impl.Camellia.Arm.Fn.ofb (ofbContract Arm.abi 2832) 0 :=
  verifiedScrubbedAll (api := ofbApi)
    { code := Impl.StackScratch.Arm.withStackScratch 2816 1 Impl.Camellia.Arm.ofb
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.ofb_framed Scrub.ofbSat }
    (Scrub.ofbOut _) (scrubSideF_of Scrub.ofb_code (by decide) _)

/-- `vg_camellia_ofb_final`. -/
theorem ofbFinal : VerifiedScrubbed target Impl.Camellia.Arm.Fn.ofbFinal (ofbFinalContract Arm.abi 2912) 0 :=
  verifiedScrubbedAll (api := ofbFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratch 88 1 Impl.Camellia.Arm.ofbFinal
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.ofbFinal_framed Scrub.ofbFinalSat }
    (Scrub.ofbFinalOut _) (scrubSideF_of Scrub.ofbFinal_code (by decide) _)

end VG.Proof.Camellia.Arm.Fn
