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
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# SEED on ARMv7, without secret residue

Every public function of SEED on ARMv7 keeps its working space in a frame,
left as it is: key expansion's 752 bytes (`withRegScratch`), and the modes'
80 bytes of their own (`withStackScratch`) around the 752 of the ECB core
they call (`Impl.Seed.Arm.ecbCore`, `ModeCore.lean`), with the groups' 128
for those in groups of blocks (`Impl/Modes/Arm/Wide.lean`); the ECB
functions call the core in a frame of 8 bytes (`Core.wrap`). None makes an
indirect call, and their postconditions read the memory on return only
within their buffers (`Arm.Scrub.PostOut`, from the lemmas of
`Proof/Seed/Scratch.lean`, `CbcScratch.lean`, `FbScratch.lean` and
`Proof/Modes/CfbFinalScratch.lean` that x86 uses too). Each is emitted
followed by `scrubAll` (`Impl.Seed.Arm.Fn`), which zeroes the stack its
contract reserves in a loop and sets the registers a callee may change and
the flags to constants. `Fn` below states that each returns without secret
residue (`Arm.Scrub.verifiedScrubbedAll`, given that its frames are within
that stack: `CodeOk`), which is what its registration binds.
-/

@[expose] public section

namespace VG.Proof.Seed.Arm.Scrub

open VG VG.Spec.Seed VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Proof.Modes.Arm

/-! ## The postconditions -/

theorem expandKeyOut (stack : Nat) : PostOut (expandKeyContract Arm.abi stack) (expandKeySig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.expandKeyPostOut_local _)

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

/-! ## The stack the functions zeroed in a loop use (`scrubAll`, `Arm.Scrub.CodeOk`) -/

theorem expandKey_code :
    CodeOk (Impl.StackScratch.Arm.withRegScratch 752 .r2 Impl.Seed.Arm.expandKey) 752 := by
  lit_decide

private theorem stackScratch_code {b m n : Nat} {c : Prog isa} (h : CodeOk c n) :
    CodeOk (Impl.StackScratch.Arm.withStackScratch b m c) (n + b) :=
  CodeOk.alloc (CodeOk.seq ((CodeOk.block _).mono (Nat.zero_le _)) h)

private theorem core_code (d : Direction) :
    armStack (Impl.Seed.Arm.ecbCore d).code + callExtraArm (Impl.Seed.Arm.ecbCore d) ≤ 752 ∧
      noIcall (Impl.Seed.Arm.ecbCore d).code = true :=
  ⟨by rw [show callExtraArm (Impl.Seed.Arm.ecbCore d) = 0 from rfl, Nat.add_zero]; exact ecb_stack d,
    by cases d <;> lit_decide⟩

theorem cbcEncrypt_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 80 0 Impl.Seed.Arm.cbcEncryptChained) 832 :=
  stackScratch_code (seq_scrubArm (core_code .encrypt) _)
theorem cfbEncrypt_code : CodeOk (Impl.StackScratch.Arm.withStackScratch 80 0 Impl.Seed.Arm.cfbEncrypt) 832 :=
  stackScratch_code (seq_scrubArm (core_code .encrypt) _)
theorem ofb_code : CodeOk (Impl.StackScratch.Arm.withStackScratch 80 0 Impl.Seed.Arm.ofb) 832 :=
  stackScratch_code (seq_scrubArm (core_code .encrypt) _)
theorem cfbEncryptFinal_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 80 0 Impl.Seed.Arm.cfbEncryptFinal) 832 :=
  stackScratch_code (seqFinal_scrubArm (core_code .encrypt) _)
theorem cfbDecryptFinal_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 80 0 Impl.Seed.Arm.cfbDecryptFinal) 832 :=
  stackScratch_code (seqFinal_scrubArm (core_code .encrypt) _)
theorem ofbFinal_code : CodeOk (Impl.StackScratch.Arm.withStackScratch 80 0 Impl.Seed.Arm.ofbFinal) 832 :=
  stackScratch_code (seqFinal_scrubArm (core_code .encrypt) _)
theorem cbcDecrypt_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 80 0 Impl.Seed.Arm.cbcDecryptChained) 960 := by
  lit_decide
theorem cfbDecrypt_code : CodeOk (Impl.StackScratch.Arm.withStackScratch 80 0 Impl.Seed.Arm.cfbDecrypt) 960 := by
  lit_decide

end VG.Proof.Seed.Arm.Scrub

namespace VG.Proof.Seed.Arm.Fn

open VG VG.Spec.Seed VG.Arm VG.Arm.Scrub

/-- `vg_seed_expand_key`. -/
theorem expandKey :
    VerifiedScrubbed target Impl.Seed.Arm.Fn.expandKey (expandKeyContract Arm.abi 752) 0 :=
  verifiedScrubbedAll (api := expandKeyApi)
    { code := Impl.StackScratch.Arm.withRegScratch 752 .r2 Impl.Seed.Arm.expandKey
      verified := Proof.Seed.Arm.expandKey_framed }
    (Scrub.expandKeyOut _)
    (scrubSideF_of Scrub.expandKey_code (by decide) _)

/-- `vg_seed_cbc_encrypt_chained`. -/
theorem cbcEncrypt :
    VerifiedScrubbed target Impl.Seed.Arm.Fn.cbcEncrypt (cbcEncryptChainedContract Arm.abi 832) 0 :=
  verifiedScrubbedAll (api := cbcEncryptChainedApi)
    { code := Impl.StackScratch.Arm.withStackScratch 80 0 Impl.Seed.Arm.cbcEncryptChained
      verified := Proof.Seed.Arm.cbcEncryptChained_framed }
    (Scrub.cbcEncryptOut _)
    (scrubSideF_of Scrub.cbcEncrypt_code (by decide) _)

/-- `vg_seed_cbc_decrypt_chained`. -/
theorem cbcDecrypt :
    VerifiedScrubbed target Impl.Seed.Arm.Fn.cbcDecrypt (cbcDecryptChainedContract Arm.abi 960) 0 :=
  verifiedScrubbedAll (api := cbcDecryptChainedApi)
    { code := Impl.StackScratch.Arm.withStackScratch 80 0 Impl.Seed.Arm.cbcDecryptChained
      verified := Proof.Seed.Arm.cbcDecryptChained_framed }
    (Scrub.cbcDecryptOut _)
    (scrubSideF_of Scrub.cbcDecrypt_code (by decide) _)

/-- `vg_seed_cfb128_encrypt`. -/
theorem cfbEncrypt :
    VerifiedScrubbed target Impl.Seed.Arm.Fn.cfbEncrypt (cfbEncryptContract Arm.abi 832) 0 :=
  verifiedScrubbedAll (api := cfbEncryptApi)
    { code := Impl.StackScratch.Arm.withStackScratch 80 0 Impl.Seed.Arm.cfbEncrypt
      verified := Proof.Seed.Arm.cfbEncrypt_framed }
    (Scrub.cfbEncryptOut _)
    (scrubSideF_of Scrub.cfbEncrypt_code (by decide) _)

/-- `vg_seed_cfb128_decrypt`. -/
theorem cfbDecrypt :
    VerifiedScrubbed target Impl.Seed.Arm.Fn.cfbDecrypt (cfbDecryptContract Arm.abi 960) 0 :=
  verifiedScrubbedAll (api := cfbDecryptApi)
    { code := Impl.StackScratch.Arm.withStackScratch 80 0 Impl.Seed.Arm.cfbDecrypt
      verified := Proof.Seed.Arm.cfbDecrypt_framed }
    (Scrub.cfbDecryptOut _)
    (scrubSideF_of Scrub.cfbDecrypt_code (by decide) _)

/-- `vg_seed_cfb128_encrypt_final`. -/
theorem cfbEncryptFinal :
    VerifiedScrubbed target Impl.Seed.Arm.Fn.cfbEncryptFinal (cfbEncryptFinalContract Arm.abi 832) 0 :=
  verifiedScrubbedAll (api := cfbEncryptFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratch 80 0 Impl.Seed.Arm.cfbEncryptFinal
      verified := Proof.Seed.Arm.cfbEncryptFinal_framed }
    (Scrub.cfbEncryptFinalOut _)
    (scrubSideF_of Scrub.cfbEncryptFinal_code (by decide) _)

/-- `vg_seed_cfb128_decrypt_final`. -/
theorem cfbDecryptFinal :
    VerifiedScrubbed target Impl.Seed.Arm.Fn.cfbDecryptFinal (cfbDecryptFinalContract Arm.abi 832) 0 :=
  verifiedScrubbedAll (api := cfbDecryptFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratch 80 0 Impl.Seed.Arm.cfbDecryptFinal
      verified := Proof.Seed.Arm.cfbDecryptFinal_framed }
    (Scrub.cfbDecryptFinalOut _)
    (scrubSideF_of Scrub.cfbDecryptFinal_code (by decide) _)

/-- `vg_seed_ofb`. -/
theorem ofb : VerifiedScrubbed target Impl.Seed.Arm.Fn.ofb (ofbContract Arm.abi 832) 0 :=
  verifiedScrubbedAll (api := ofbApi)
    { code := Impl.StackScratch.Arm.withStackScratch 80 0 Impl.Seed.Arm.ofb
      verified := Proof.Seed.Arm.ofb_framed }
    (Scrub.ofbOut _)
    (scrubSideF_of Scrub.ofb_code (by decide) _)

/-- `vg_seed_ofb_final`. -/
theorem ofbFinal : VerifiedScrubbed target Impl.Seed.Arm.Fn.ofbFinal (ofbFinalContract Arm.abi 832) 0 :=
  verifiedScrubbedAll (api := ofbFinalApi)
    { code := Impl.StackScratch.Arm.withStackScratch 80 0 Impl.Seed.Arm.ofbFinal
      verified := Proof.Seed.Arm.ofbFinal_framed }
    (Scrub.ofbFinalOut _)
    (scrubSideF_of Scrub.ofbFinal_code (by decide) _)

end VG.Proof.Seed.Arm.Fn
