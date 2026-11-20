module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
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
`Proof/Camellia/ScrubLocal.lean` that RISC-V uses too). Each is emitted
followed by a wipe of the stack its contract reserves, rounded up to a
frame size the model accepts (`Arm.Scrub.Verified.stack_le`), and by
instructions that set the registers a callee may change, but the result,
and the flags to constants (`Impl.Camellia.Arm.Fn`), and `Fn` below states
that each returns without secret residue (`Arm.Scrub.verifiedScrubbedF`),
which is what its registration binds.

The modes call ECB's and CTR's code as it is verified, without the wipe,
under names of their own (`vg_camellia_ecb_encrypt_entry`,
`Impl.Camellia.Arm.ecbCore`; `vg_camellia_ctr_entry`,
`Impl.Camellia.Arm.ctrCall`), which the emitter writes as internal
functions: their own wipe covers the frame of that call.
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

/-! ## The code: its frames, and no indirect call -/

/-! The code of the table's construction and of the encipherment from it,
as literals, which `lit_decide` reads. -/
materialize_flat_code ecbKeysEncrypt := Impl.Camellia.Arm.ecbKeys .encrypt
materialize_flat_code ecbKeyedCode := Impl.Camellia.Arm.ecbKeyed

theorem frameOk_2720 : FrameOk 2720 := by decide
theorem frameOk_2816 : FrameOk 2816 := by decide
theorem frameOk_2832 : FrameOk 2832 := by decide
theorem frameOk_2912 : FrameOk 2912 := by decide
theorem frameOk_3040 : FrameOk 3040 := by decide
theorem frameOk_3120 : FrameOk 3120 := by decide

theorem expandKey_code : armStack Impl.Camellia.Arm.expandKey = 0 ∧
    noIcall Impl.Camellia.Arm.expandKey = true := by lit_decide

theorem encrypt_code : armStack (Impl.Camellia.Arm.ecb .encrypt) = 0 ∧
    noIcall (Impl.Camellia.Arm.ecb .encrypt) = true := by lit_decide

theorem decrypt_code : armStack (Impl.Camellia.Arm.ecb .decrypt) = 0 ∧
    noIcall (Impl.Camellia.Arm.ecb .decrypt) = true := by lit_decide

theorem keys_code : armStack (Impl.Camellia.Arm.ecbKeys .encrypt) = 0 ∧
    noIcall (Impl.Camellia.Arm.ecbKeys .encrypt) = true := by lit_decide

theorem keyed_code : armStack Impl.Camellia.Arm.ecbKeyed = 0 ∧
    noIcall Impl.Camellia.Arm.ecbKeyed = true := by lit_decide

theorem ecbCode_scrub (d : Impl.Camellia.Arm.Dir) :
    CodeOk (Impl.Camellia.Arm.ecbCode d) 2816 := by
  cases d
  · exact withStackScratchWiped_scrubArm (n := 0) ⟨Nat.le_of_eq encrypt_code.1, encrypt_code.2⟩
  · exact withStackScratchWiped_scrubArm (n := 0) ⟨Nat.le_of_eq decrypt_code.1, decrypt_code.2⟩

/-- ECB's code, as the modes call it. -/
theorem ecbCore_scrub (d : Impl.Camellia.Arm.Dir) :
    armStack (Impl.Camellia.Arm.ecbCore d).code + callExtraArm (Impl.Camellia.Arm.ecbCore d) ≤ 2816 ∧
      noIcall (Impl.Camellia.Arm.ecbCore d).code = true := by
  simpa only [callExtraArm, Impl.Camellia.Arm.ecbCore, ite_true, Nat.add_zero] using ecbCode_scrub d

/-- A mode in groups of blocks: the groups' buffer of 128 bytes, around the
calls of the core, and the blocks left as `Core.seq`'s. -/
theorem seq8_scrub {c : Impl.Modes.Arm.Core} {n : Nat}
    (hc : armStack c.code + callExtraArm c ≤ n ∧ noIcall c.code = true)
    (m : Impl.Modes.Arm.Mode) (wm : Impl.Modes.Arm.WMode) :
    armStack (c.seq8 m wm) ≤ n + 128 ∧ noIcall (c.seq8 m wm) = true := by
  obtain ⟨h₁, h₂⟩ := callStep_scrubArm hc
  simp only [Impl.Modes.Arm.Core.seq8, Impl.Modes.Arm.Core.seqW, Impl.Modes.Arm.Core.wide,
    Impl.Modes.Arm.wideLevels, Impl.Modes.Arm.wideBuf, Impl.Modes.Arm.Core.wlevels,
    Impl.Modes.Arm.Core.wlevel, Impl.Modes.Arm.Core.wbody, Impl.Modes.Arm.Core.body, armStack, noIcall,
    hc.2, h₂, Bool.and_true, Nat.zero_max, Nat.max_zero, and_true]
  omega

/-- A mode one block at a time from the table built once: its construction,
then a call of the encipherment from it, in a frame of 8 bytes. -/
theorem seqK_scrub {c : Impl.Modes.Arm.Core} {k : Impl.Modes.Arm.Keyed} {n : Nat}
    (hk : armStack k.keysCode ≤ n ∧ noIcall k.keysCode = true ∧ armStack k.code + 8 ≤ n ∧
      noIcall k.code = true)
    (m : Impl.Modes.Arm.Mode) :
    armStack (c.seqK k m) ≤ n ∧ noIcall (c.seqK k m) = true := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hk
  simp only [Impl.Modes.Arm.Core.seqK, Impl.Modes.Arm.Core.keysStep, Impl.Modes.Arm.Core.bodyK,
    Impl.Modes.Arm.Keyed.callStep, armStack, noIcall, h₂, h₄, Bool.and_true,
    List.length_cons, List.length_nil, Nat.zero_max, Nat.max_zero, and_true]
  omega

theorem keyed_scrub : armStack (Impl.Camellia.Arm.keyed .encrypt).keysCode ≤ 8 ∧
    noIcall (Impl.Camellia.Arm.keyed .encrypt).keysCode = true ∧
    armStack (Impl.Camellia.Arm.keyed .encrypt).code + 8 ≤ 8 ∧
    noIcall (Impl.Camellia.Arm.keyed .encrypt).code = true := by
  simp only [Impl.Camellia.Arm.keyed]
  exact ⟨by rw [keys_code.1]; omega, keys_code.2, by rw [keyed_code.1], keyed_code.2⟩

/-- A mode one block at a time, in its 2816-byte scratch frame. -/
theorem seqK_framed_scrub (m : Impl.Modes.Arm.Mode) :
    armStack (Impl.StackScratch.Arm.withStackScratchWiped 2816 1 698
      ((Impl.Camellia.Arm.scrCore .encrypt).seqK (Impl.Camellia.Arm.keyed .encrypt) m)) ≤ 2832 ∧
      noIcall (Impl.StackScratch.Arm.withStackScratchWiped 2816 1 698
        ((Impl.Camellia.Arm.scrCore .encrypt).seqK (Impl.Camellia.Arm.keyed .encrypt) m)) = true := by
  obtain ⟨h₁, h₂⟩ := withStackScratchWiped_scrubArm (bytes := 2816) (m := 1) (words := 698)
    (seqK_scrub (c := Impl.Camellia.Arm.scrCore .encrypt) keyed_scrub m)
  exact ⟨by omega, h₂⟩

/-- A mode in groups of blocks, in its 88-byte scratch frame. -/
theorem seq8_framed_scrub (d : Impl.Camellia.Arm.Dir) (m : Impl.Modes.Arm.Mode) (wm : Impl.Modes.Arm.WMode) :
    armStack (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 ((Impl.Camellia.Arm.ecbCore d).seq8 m wm))
      ≤ 3032 ∧
      noIcall (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18
        ((Impl.Camellia.Arm.ecbCore d).seq8 m wm)) = true :=
  withStackScratchWiped_scrubArm (seq8_scrub (ecbCore_scrub d) m wm)

/-- A mode over a message's last piece, in its 88-byte scratch frame. -/
theorem seqFinal_scrub (m : Impl.Modes.Arm.Mode) :
    armStack (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18
      ((Impl.Camellia.Arm.ecbCore .encrypt).seqFinal m)) ≤ 2904 ∧
      noIcall (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18
        ((Impl.Camellia.Arm.ecbCore .encrypt).seqFinal m)) = true :=
  withStackScratchWiped_scrubArm (seqFinal_scrubArm (ecbCore_scrub .encrypt) m)

theorem ctrFramed_scrub : CodeOk Impl.Camellia.Arm.ctrFramed 3032 :=
  seq8_framed_scrub .encrypt Impl.Modes.Arm.ctr Impl.Modes.Arm.ctrW

theorem cbcEncrypt_scrub :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 2816 1 698 Impl.Camellia.Arm.cbcEncryptChained) 2832 :=
  seqK_framed_scrub Impl.Modes.Arm.cbcEncChained

theorem cfbEncrypt_scrub :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 2816 1 698 Impl.Camellia.Arm.cfbEncrypt) 2832 :=
  seqK_framed_scrub Impl.Modes.Arm.cfbEnc

theorem ofb_scrub :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 2816 1 698 Impl.Camellia.Arm.ofb) 2832 :=
  seqK_framed_scrub Impl.Modes.Arm.ofb

theorem cbcDecrypt_scrub :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cbcDecryptChained) 3032 :=
  seq8_framed_scrub .decrypt Impl.Modes.Arm.cbcDecChained Impl.Modes.Arm.cbcDecW

theorem cfbDecrypt_scrub :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cfbDecrypt) 3032 :=
  seq8_framed_scrub .encrypt Impl.Modes.Arm.cfbDec Impl.Modes.Arm.cfbDecW

theorem cfbEncryptFinal_scrub :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cfbEncryptFinal) 2904 :=
  seqFinal_scrub Impl.Modes.Arm.cfbEnc

theorem cfbDecryptFinal_scrub :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cfbDecryptFinal) 2904 :=
  seqFinal_scrub Impl.Modes.Arm.cfbDecF

theorem ofbFinal_scrub :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.ofbFinal) 2904 :=
  seqFinal_scrub Impl.Modes.Arm.ofb

/-- CTR over a message's last piece: its calls of CTR, in a frame of 8 bytes,
in its 72-byte frame. -/
theorem ctrFinal_scrub :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 72 1 14 Impl.Camellia.Arm.ctrFinal) 3112 := by
  refine withStackScratchWiped_scrubArm (n := 3040) ?_
  obtain ⟨h₁, h₂⟩ := ctrFramed_scrub
  simp only [Impl.Camellia.Arm.ctrFinal, Impl.Camellia.Arm.ctrFinalTail, Impl.Camellia.Arm.ctrCall, armStack,
    noIcall, h₂, Bool.and_true, List.length_cons, List.length_nil, Nat.zero_max, Nat.max_zero,
    and_true]
  omega

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
  verifiedScrubbedF (api := expandKeyApi)
    { code := Impl.StackScratch.Arm.withRegScratchWiped 2720 .r3 680 Impl.Camellia.Arm.expandKey
      verified := Proof.Camellia.Arm.expandKey_framed }
    (Scrub.expandKeyOut _)
    (scrubSideF_of (withRegScratchWiped_scrubArm (n := 0)
      ⟨Nat.le_of_eq Scrub.expandKey_code.1, Scrub.expandKey_code.2⟩) Scrub.frameOk_2720 _)

/-- `vg_camellia_ecb_encrypt`. -/
theorem ecbEncrypt :
    VerifiedScrubbed target Impl.Camellia.Arm.Fn.ecbEncrypt (ecbContract Arm.abi .encrypt 2816) 0 :=
  verifiedScrubbedF (api := ecbEncryptApi)
    { code := Impl.Camellia.Arm.ecbCode .encrypt
      verified := Proof.Camellia.Arm.ecb_framed .encrypt }
    (Scrub.ecbOut .encrypt _) (scrubSideF_of (Scrub.ecbCode_scrub .encrypt) Scrub.frameOk_2816 _)

/-- `vg_camellia_ecb_decrypt`. -/
theorem ecbDecrypt :
    VerifiedScrubbed target Impl.Camellia.Arm.Fn.ecbDecrypt (ecbContract Arm.abi .decrypt 2816) 0 :=
  verifiedScrubbedF (api := ecbDecryptApi)
    { code := Impl.Camellia.Arm.ecbCode .decrypt
      verified := Proof.Camellia.Arm.ecb_framed .decrypt }
    (Scrub.ecbOut .decrypt _) (scrubSideF_of (Scrub.ecbCode_scrub .decrypt) Scrub.frameOk_2816 _)

/-- `vg_camellia_cbc_encrypt_chained`. -/
theorem cbcEncrypt :
    VerifiedScrubbed target Impl.Camellia.Arm.Fn.cbcEncrypt (cbcEncryptChainedContract Arm.abi 2832) 0 :=
  verifiedScrubbedF (api := cbcEncryptChainedApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 2816 1 698 Impl.Camellia.Arm.cbcEncryptChained
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.cbcEncryptChained_framed Scrub.cbcEncryptSat }
    (Scrub.cbcEncryptOut _) (scrubSideF_of Scrub.cbcEncrypt_scrub Scrub.frameOk_2832 _)

/-- `vg_camellia_cbc_decrypt_chained`. -/
theorem cbcDecrypt :
    VerifiedScrubbed target Impl.Camellia.Arm.Fn.cbcDecrypt (cbcDecryptChainedContract Arm.abi 3040) 0 :=
  verifiedScrubbedF (api := cbcDecryptChainedApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cbcDecryptChained
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.cbcDecryptChained_framed Scrub.cbcDecryptSat }
    (Scrub.cbcDecryptOut _)
    (scrubSideF_of (CodeOk.mono Scrub.cbcDecrypt_scrub (by decide)) Scrub.frameOk_3040 _)

/-- `vg_camellia_cfb128_encrypt`. -/
theorem cfbEncrypt :
    VerifiedScrubbed target Impl.Camellia.Arm.Fn.cfbEncrypt (cfbEncryptContract Arm.abi 2832) 0 :=
  verifiedScrubbedF (api := cfbEncryptApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 2816 1 698 Impl.Camellia.Arm.cfbEncrypt
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.cfbEncrypt_framed Scrub.cfbEncryptSat }
    (Scrub.cfbEncryptOut _) (scrubSideF_of Scrub.cfbEncrypt_scrub Scrub.frameOk_2832 _)

/-- `vg_camellia_cfb128_decrypt`. -/
theorem cfbDecrypt :
    VerifiedScrubbed target Impl.Camellia.Arm.Fn.cfbDecrypt (cfbDecryptContract Arm.abi 3040) 0 :=
  verifiedScrubbedF (api := cfbDecryptApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cfbDecrypt
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.cfbDecrypt_framed Scrub.cfbDecryptSat }
    (Scrub.cfbDecryptOut _)
    (scrubSideF_of (CodeOk.mono Scrub.cfbDecrypt_scrub (by decide)) Scrub.frameOk_3040 _)

/-- `vg_camellia_cfb128_encrypt_final`. -/
theorem cfbEncryptFinal :
    VerifiedScrubbed target Impl.Camellia.Arm.Fn.cfbEncryptFinal (cfbEncryptFinalContract Arm.abi 2912) 0 :=
  verifiedScrubbedF (api := cfbEncryptFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cfbEncryptFinal
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.cfbEncryptFinal_framed Scrub.cfbEncryptFinalSat }
    (Scrub.cfbEncryptFinalOut _)
    (scrubSideF_of (CodeOk.mono Scrub.cfbEncryptFinal_scrub (by decide)) Scrub.frameOk_2912 _)

/-- `vg_camellia_cfb128_decrypt_final`. -/
theorem cfbDecryptFinal :
    VerifiedScrubbed target Impl.Camellia.Arm.Fn.cfbDecryptFinal (cfbDecryptFinalContract Arm.abi 2912) 0 :=
  verifiedScrubbedF (api := cfbDecryptFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cfbDecryptFinal
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.cfbDecryptFinal_framed Scrub.cfbDecryptFinalSat }
    (Scrub.cfbDecryptFinalOut _)
    (scrubSideF_of (CodeOk.mono Scrub.cfbDecryptFinal_scrub (by decide)) Scrub.frameOk_2912 _)

/-- `vg_camellia_ctr`. -/
theorem ctr : VerifiedScrubbed target Impl.Camellia.Arm.Fn.ctr (ctrContract Arm.abi 3040) 0 :=
  verifiedScrubbedF (api := ctrApi)
    { code := Impl.Camellia.Arm.ctrFramed
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.ctr_framed Scrub.ctrSat }
    (Scrub.ctrOut _) (scrubSideF_of (CodeOk.mono Scrub.ctrFramed_scrub (by decide)) Scrub.frameOk_3040 _)

/-- `vg_camellia_ctr_final`. -/
theorem ctrFinal : VerifiedScrubbed target Impl.Camellia.Arm.Fn.ctrFinal (ctrFinalContract Arm.abi 3120) 0 :=
  verifiedScrubbedF (api := ctrFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 72 1 14 Impl.Camellia.Arm.ctrFinal
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.CtrFinal.ctrFinal_framed Scrub.ctrFinalSat }
    (Scrub.ctrFinalOut _) (scrubSideF_of (CodeOk.mono Scrub.ctrFinal_scrub (by decide)) Scrub.frameOk_3120 _)

/-- `vg_camellia_ofb`. -/
theorem ofb : VerifiedScrubbed target Impl.Camellia.Arm.Fn.ofb (ofbContract Arm.abi 2832) 0 :=
  verifiedScrubbedF (api := ofbApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 2816 1 698 Impl.Camellia.Arm.ofb
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.ofb_framed Scrub.ofbSat }
    (Scrub.ofbOut _) (scrubSideF_of Scrub.ofb_scrub Scrub.frameOk_2832 _)

/-- `vg_camellia_ofb_final`. -/
theorem ofbFinal : VerifiedScrubbed target Impl.Camellia.Arm.Fn.ofbFinal (ofbFinalContract Arm.abi 2912) 0 :=
  verifiedScrubbedF (api := ofbFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.ofbFinal
      verified := Verified.stack_le (by decide) Proof.Camellia.Arm.ofbFinal_framed Scrub.ofbFinalSat }
    (Scrub.ofbFinalOut _) (scrubSideF_of (CodeOk.mono Scrub.ofbFinal_scrub (by decide)) Scrub.frameOk_2912 _)

end VG.Proof.Camellia.Arm.Fn
