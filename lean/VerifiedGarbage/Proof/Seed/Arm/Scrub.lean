module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.Seed.Arm.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Seed.Arm.KeyVerified
public import VerifiedGarbage.Proof.Seed.Arm.Verified
public import VerifiedGarbage.Proof.Seed.Arm.CbcVerified
public import VerifiedGarbage.Proof.Seed.Arm.FbVerified
public import VerifiedGarbage.Proof.Seed.Arm.FbFinalVerified
public import VerifiedGarbage.Proof.Modes.Arm.ScrubCode
import VerifiedGarbage.Proof.Seed.Scratch
import VerifiedGarbage.Proof.Seed.CbcScratch
import VerifiedGarbage.Proof.Seed.FbScratch
import VerifiedGarbage.Proof.Modes.CfbFinalScratch
import VerifiedGarbage.Proof.Seed.Arm.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.Seed.Arm.Fn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Seed.Arm.KeyVerified
meta import VerifiedGarbage.Proof.Seed.Arm.Verified
meta import VerifiedGarbage.Proof.Seed.Arm.CbcVerified
meta import VerifiedGarbage.Proof.Seed.Arm.FbVerified
meta import VerifiedGarbage.Proof.Seed.Arm.FbFinalVerified
meta import VerifiedGarbage.Proof.Modes.Arm.ScrubCode
meta import VerifiedGarbage.Proof.Seed.Scratch
meta import VerifiedGarbage.Proof.Seed.CbcScratch
meta import VerifiedGarbage.Proof.Seed.FbScratch
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Proof.Seed.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SEED on ARMv7, without secret residue

Every public function of SEED on ARMv7 keeps its working space in a frame:
key expansion's and ECB's 752 bytes (`withRegScratchWiped`), and the modes
80 bytes of their own around ECB's 752, with the groups' 128 for those in
groups of blocks (`Impl/Modes/Arm/Wide.lean`). None makes an indirect call,
and their postconditions read the memory on return only within their
buffers (`Arm.Scrub.PostOut`, from the lemmas of `Proof/Seed/Scratch.lean`,
`CbcScratch.lean`, `FbScratch.lean` and `Proof/Modes/CfbFinalScratch.lean`
that x86 uses too). Each is emitted followed by a wipe of the stack its
contract reserves and by instructions that set the registers a callee may
change and the flags to constants (`Impl.Seed.Arm.Fn`), and `Fn` below
states that each returns without secret residue
(`Arm.Scrub.verifiedScrubbedF`), which is what its registration binds.

The modes call ECB's code as it is verified, without the wipe, under names
of their own (`vg_seed_ecb_encrypt_entry`, `Impl.Seed.Arm.ecbCore`), which
the emitter writes as internal functions: their own wipe covers the frame
of that call.
-/

@[expose] public section

namespace VG.Proof.Seed.Arm.Scrub

open VG VG.Spec.Seed VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Proof.Modes.Arm

/-! ## The postconditions -/

theorem expandKeyOut (stack : Nat) : PostOut (expandKeyContract Arm.abi stack) (expandKeySig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.expandKeyPostOut_local _)

theorem ecbOut (d : Direction) (stack : Nat) : PostOut (ecbContract Arm.abi d stack) (ecbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.ecbPostOut_local _ d)

theorem cbcEncryptOut (stack : Nat) :
    PostOut (cbcEncryptChainedContract Arm.abi stack) (cbcChainedSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.cbcEncChainedPostOut_local _)

theorem cbcDecryptOut (stack : Nat) :
    PostOut (cbcDecryptChainedContract Arm.abi stack) (cbcChainedSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.cbcDecChainedPostOut_local _)

theorem cfbEncryptOut (stack : Nat) : PostOut (cfbEncryptContract Arm.abi stack) (cfbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.cfbEncPostOut_local _)

theorem cfbDecryptOut (stack : Nat) : PostOut (cfbDecryptContract Arm.abi stack) (cfbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.cfbDecPostOut_local _)

theorem cfbEncryptFinalOut (stack : Nat) :
    PostOut (cfbEncryptFinalContract Arm.abi stack) (cfbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.encFinalPost_local _)

theorem cfbDecryptFinalOut (stack : Nat) :
    PostOut (cfbDecryptFinalContract Arm.abi stack) (cfbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.decFinalPost_local _)

theorem ofbOut (stack : Nat) : PostOut (ofbContract Arm.abi stack) (ofbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.ofbPostOut_local _)

theorem ofbFinalOut (stack : Nat) : PostOut (ofbFinalContract Arm.abi stack) (ofbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.ofbFinalPost_local _)

/-! ## The code: its frames, and no indirect call -/

theorem frameOk_752 : FrameOk 752 := by decide
theorem frameOk_832 : FrameOk 832 := by decide
theorem frameOk_960 : FrameOk 960 := by decide

theorem expandKey_code : armStack Impl.Seed.Arm.expandKey = 0 ∧
    noIcall Impl.Seed.Arm.expandKey = true := by lit_decide

theorem encrypt_code : armStack (Impl.Seed.Arm.ecb .encrypt) = 0 ∧
    noIcall (Impl.Seed.Arm.ecb .encrypt) = true := by lit_decide

theorem decrypt_code : armStack (Impl.Seed.Arm.ecb .decrypt) = 0 ∧
    noIcall (Impl.Seed.Arm.ecb .decrypt) = true := by lit_decide

theorem expandKey_scrub :
    CodeOk (Impl.StackScratch.Arm.withRegScratchWiped 752 .r2 188 Impl.Seed.Arm.expandKey) 752 :=
  withRegScratchWiped_scrubArm (n := 0) ⟨Nat.le_of_eq expandKey_code.1, expandKey_code.2⟩

theorem ecbCode_scrub (d : Direction) : CodeOk (Impl.Seed.Arm.ecbCode d) 752 := by
  cases d
  · exact withRegScratchWiped_scrubArm (n := 0) ⟨Nat.le_of_eq encrypt_code.1, encrypt_code.2⟩
  · exact withRegScratchWiped_scrubArm (n := 0) ⟨Nat.le_of_eq decrypt_code.1, decrypt_code.2⟩

/-- ECB's code, as the modes call it. -/
theorem ecbCore_scrub (d : Direction) :
    armStack (Impl.Seed.Arm.ecbCore d).code + callExtraArm (Impl.Seed.Arm.ecbCore d) ≤ 752 ∧
      noIcall (Impl.Seed.Arm.ecbCore d).code = true := by
  simpa only [callExtraArm, Impl.Seed.Arm.ecbCore, ite_true, Nat.add_zero] using ecbCode_scrub d

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

/-- A mode one block at a time, in its 80-byte scratch frame. -/
theorem seq_framed_scrub (m : Impl.Modes.Arm.Mode) :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 ((Impl.Seed.Arm.ecbCore .encrypt).seq m)) 832 :=
  withStackScratchWiped_scrubArm (seq_scrubArm (ecbCore_scrub .encrypt) m)

/-- A mode in groups of blocks, in its 80-byte scratch frame. -/
theorem seq8_framed_scrub (d : Direction) (m : Impl.Modes.Arm.Mode) (wm : Impl.Modes.Arm.WMode) :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 ((Impl.Seed.Arm.ecbCore d).seq8 m wm)) 960 :=
  withStackScratchWiped_scrubArm (seq8_scrub (ecbCore_scrub d) m wm)

/-- A mode over a message's last piece, in its 80-byte scratch frame. -/
theorem seqFinal_framed_scrub (m : Impl.Modes.Arm.Mode) :
    CodeOk (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18
      ((Impl.Seed.Arm.ecbCore .encrypt).seqFinal m)) 832 :=
  withStackScratchWiped_scrubArm (seqFinal_scrubArm (ecbCore_scrub .encrypt) m)

end VG.Proof.Seed.Arm.Scrub

namespace VG.Proof.Seed.Arm.Fn

open VG VG.Spec.Seed VG.Arm VG.Arm.Scrub

/-- `vg_seed_expand_key`. -/
theorem expandKey :
    VerifiedScrubbed target Impl.Seed.Arm.Fn.expandKey (expandKeyContract Arm.abi 752) 0 :=
  verifiedScrubbedF (api := expandKeyApi)
    { code := Impl.StackScratch.Arm.withRegScratchWiped 752 .r2 188 Impl.Seed.Arm.expandKey
      verified := Proof.Seed.Arm.expandKey_framed }
    (Scrub.expandKeyOut _) (scrubSideF_of Scrub.expandKey_scrub Scrub.frameOk_752 _)

/-- `vg_seed_ecb_encrypt`. -/
theorem ecbEncrypt :
    VerifiedScrubbed target Impl.Seed.Arm.Fn.ecbEncrypt (ecbContract Arm.abi .encrypt 752) 0 :=
  verifiedScrubbedF (api := ecbEncryptApi)
    { code := Impl.Seed.Arm.ecbCode .encrypt
      verified := Proof.Seed.Arm.ecb_framed .encrypt }
    (Scrub.ecbOut .encrypt _) (scrubSideF_of (Scrub.ecbCode_scrub .encrypt) Scrub.frameOk_752 _)

/-- `vg_seed_ecb_decrypt`. -/
theorem ecbDecrypt :
    VerifiedScrubbed target Impl.Seed.Arm.Fn.ecbDecrypt (ecbContract Arm.abi .decrypt 752) 0 :=
  verifiedScrubbedF (api := ecbDecryptApi)
    { code := Impl.Seed.Arm.ecbCode .decrypt
      verified := Proof.Seed.Arm.ecb_framed .decrypt }
    (Scrub.ecbOut .decrypt _) (scrubSideF_of (Scrub.ecbCode_scrub .decrypt) Scrub.frameOk_752 _)

/-- `vg_seed_cbc_encrypt_chained`. -/
theorem cbcEncrypt :
    VerifiedScrubbed target Impl.Seed.Arm.Fn.cbcEncrypt (cbcEncryptChainedContract Arm.abi 832) 0 :=
  verifiedScrubbedF (api := cbcEncryptChainedApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cbcEncryptChained
      verified := Proof.Seed.Arm.cbcEncryptChained_framed }
    (Scrub.cbcEncryptOut _)
    (scrubSideF_of (Scrub.seq_framed_scrub Impl.Modes.Arm.cbcEncChained) Scrub.frameOk_832 _)

/-- `vg_seed_cbc_decrypt_chained`. -/
theorem cbcDecrypt :
    VerifiedScrubbed target Impl.Seed.Arm.Fn.cbcDecrypt (cbcDecryptChainedContract Arm.abi 960) 0 :=
  verifiedScrubbedF (api := cbcDecryptChainedApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cbcDecryptChained
      verified := Proof.Seed.Arm.cbcDecryptChained_framed }
    (Scrub.cbcDecryptOut _)
    (scrubSideF_of (Scrub.seq8_framed_scrub .decrypt Impl.Modes.Arm.cbcDecChained Impl.Modes.Arm.cbcDecW)
      Scrub.frameOk_960 _)

/-- `vg_seed_cfb128_encrypt`. -/
theorem cfbEncrypt :
    VerifiedScrubbed target Impl.Seed.Arm.Fn.cfbEncrypt (cfbEncryptContract Arm.abi 832) 0 :=
  verifiedScrubbedF (api := cfbEncryptApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cfbEncrypt
      verified := Proof.Seed.Arm.cfbEncrypt_framed }
    (Scrub.cfbEncryptOut _)
    (scrubSideF_of (Scrub.seq_framed_scrub Impl.Modes.Arm.cfbEnc) Scrub.frameOk_832 _)

/-- `vg_seed_cfb128_decrypt`. -/
theorem cfbDecrypt :
    VerifiedScrubbed target Impl.Seed.Arm.Fn.cfbDecrypt (cfbDecryptContract Arm.abi 960) 0 :=
  verifiedScrubbedF (api := cfbDecryptApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cfbDecrypt
      verified := Proof.Seed.Arm.cfbDecrypt_framed }
    (Scrub.cfbDecryptOut _)
    (scrubSideF_of (Scrub.seq8_framed_scrub .encrypt Impl.Modes.Arm.cfbDec Impl.Modes.Arm.cfbDecW)
      Scrub.frameOk_960 _)

/-- `vg_seed_cfb128_encrypt_final`. -/
theorem cfbEncryptFinal :
    VerifiedScrubbed target Impl.Seed.Arm.Fn.cfbEncryptFinal (cfbEncryptFinalContract Arm.abi 832) 0 :=
  verifiedScrubbedF (api := cfbEncryptFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cfbEncryptFinal
      verified := Proof.Seed.Arm.cfbEncryptFinal_framed }
    (Scrub.cfbEncryptFinalOut _)
    (scrubSideF_of (Scrub.seqFinal_framed_scrub Impl.Modes.Arm.cfbEnc) Scrub.frameOk_832 _)

/-- `vg_seed_cfb128_decrypt_final`. -/
theorem cfbDecryptFinal :
    VerifiedScrubbed target Impl.Seed.Arm.Fn.cfbDecryptFinal (cfbDecryptFinalContract Arm.abi 832) 0 :=
  verifiedScrubbedF (api := cfbDecryptFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cfbDecryptFinal
      verified := Proof.Seed.Arm.cfbDecryptFinal_framed }
    (Scrub.cfbDecryptFinalOut _)
    (scrubSideF_of (Scrub.seqFinal_framed_scrub Impl.Modes.Arm.cfbDecF) Scrub.frameOk_832 _)

/-- `vg_seed_ofb`. -/
theorem ofb : VerifiedScrubbed target Impl.Seed.Arm.Fn.ofb (ofbContract Arm.abi 832) 0 :=
  verifiedScrubbedF (api := ofbApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.ofb
      verified := Proof.Seed.Arm.ofb_framed }
    (Scrub.ofbOut _) (scrubSideF_of (Scrub.seq_framed_scrub Impl.Modes.Arm.ofb) Scrub.frameOk_832 _)

/-- `vg_seed_ofb_final`. -/
theorem ofbFinal : VerifiedScrubbed target Impl.Seed.Arm.Fn.ofbFinal (ofbFinalContract Arm.abi 832) 0 :=
  verifiedScrubbedF (api := ofbFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.ofbFinal
      verified := Proof.Seed.Arm.ofbFinal_framed }
    (Scrub.ofbFinalOut _) (scrubSideF_of (Scrub.seqFinal_framed_scrub Impl.Modes.Arm.ofb) Scrub.frameOk_832 _)

end VG.Proof.Seed.Arm.Fn
