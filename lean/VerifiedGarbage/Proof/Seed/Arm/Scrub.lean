module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Framework.Arm.ScrubSel
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
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubSel
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

Every public function of SEED on ARMv7 keeps its working space in a frame:
key expansion's and ECB's 752 bytes (`withRegScratchWiped`), and the modes
80 bytes of their own around ECB's 752, with the groups' 128 for those in
groups of blocks (`Impl/Modes/Arm/Wide.lean`). None makes an indirect call,
and their postconditions read the memory on return only within their
buffers (`Arm.Scrub.PostOut`, from the lemmas of `Proof/Seed/Scratch.lean`,
`CbcScratch.lean`, `FbScratch.lean` and `Proof/Modes/CfbFinalScratch.lean`
that x86 uses too). Each wipes its own working space, and is
emitted followed by a wipe of only the words of the stack its contract
reserves that the residue analysis finds may differ between two runs
(`Impl.Scrub.Arm.scrubSel`), and by instructions that set the
registers a callee may change and the flags to constants
(`Impl.Seed.Arm.Fn`). `Fn` below states that each returns without secret
residue (`Arm.Scrub.verifiedScrubbedSel`, whose analysis, `Arm.rtaint`, the
kernel evaluates here: `taint_decide_ct`), which is what its registration
binds.

The modes call the ECB artifacts as they are emitted, cleanup included
(`Impl.Seed.Arm.ecbCore`), whose theorems are in `ModeCore.lean`: the
analysis of each mode covers the frame of that call.
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

end VG.Proof.Seed.Arm.Scrub

namespace VG.Proof.Seed.Arm.Fn

open VG VG.Spec.Seed VG.Arm VG.Arm.Scrub

/-- `vg_seed_expand_key`. -/
theorem expandKey :
    VerifiedScrubbed target Impl.Seed.Arm.Fn.expandKey (expandKeyContract Arm.abi 752) 0 :=
  verifiedScrubbedSel (api := expandKeyApi) (W := 752)
    { code := Impl.StackScratch.Arm.withRegScratchWiped 752 .r2 188 Impl.Seed.Arm.expandKey
      verified := Proof.Seed.Arm.expandKey_framed }
    Impl.Seed.Arm.Fn.noWords []
    (Scrub.expandKeyOut _)
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_seed_cbc_encrypt_chained`. -/
theorem cbcEncrypt :
    VerifiedScrubbed target Impl.Seed.Arm.Fn.cbcEncrypt (cbcEncryptChainedContract Arm.abi 832) 0 :=
  verifiedScrubbedSel (api := cbcEncryptChainedApi) (W := 832)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cbcEncryptChained
      verified := Proof.Seed.Arm.cbcEncryptChained_framed }
    Impl.Seed.Arm.Fn.modeWords []
    (Scrub.cbcEncryptOut _)
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_seed_cbc_decrypt_chained`. -/
theorem cbcDecrypt :
    VerifiedScrubbed target Impl.Seed.Arm.Fn.cbcDecrypt (cbcDecryptChainedContract Arm.abi 960) 0 :=
  verifiedScrubbedSel (api := cbcDecryptChainedApi) (W := 960)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cbcDecryptChained
      verified := Proof.Seed.Arm.cbcDecryptChained_framed }
    Impl.Seed.Arm.Fn.wideWords []
    (Scrub.cbcDecryptOut _)
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_seed_cfb128_encrypt`. -/
theorem cfbEncrypt :
    VerifiedScrubbed target Impl.Seed.Arm.Fn.cfbEncrypt (cfbEncryptContract Arm.abi 832) 0 :=
  verifiedScrubbedSel (api := cfbEncryptApi) (W := 832)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cfbEncrypt
      verified := Proof.Seed.Arm.cfbEncrypt_framed }
    Impl.Seed.Arm.Fn.modeWords []
    (Scrub.cfbEncryptOut _)
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_seed_cfb128_decrypt`. -/
theorem cfbDecrypt :
    VerifiedScrubbed target Impl.Seed.Arm.Fn.cfbDecrypt (cfbDecryptContract Arm.abi 960) 0 :=
  verifiedScrubbedSel (api := cfbDecryptApi) (W := 960)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cfbDecrypt
      verified := Proof.Seed.Arm.cfbDecrypt_framed }
    Impl.Seed.Arm.Fn.wideWords []
    (Scrub.cfbDecryptOut _)
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_seed_cfb128_encrypt_final`. -/
theorem cfbEncryptFinal :
    VerifiedScrubbed target Impl.Seed.Arm.Fn.cfbEncryptFinal (cfbEncryptFinalContract Arm.abi 832) 0 :=
  verifiedScrubbedSel (api := cfbEncryptFinalApi) (W := 832)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cfbEncryptFinal
      verified := Proof.Seed.Arm.cfbEncryptFinal_framed }
    Impl.Seed.Arm.Fn.modeWords []
    (Scrub.cfbEncryptFinalOut _)
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_seed_cfb128_decrypt_final`. -/
theorem cfbDecryptFinal :
    VerifiedScrubbed target Impl.Seed.Arm.Fn.cfbDecryptFinal (cfbDecryptFinalContract Arm.abi 832) 0 :=
  verifiedScrubbedSel (api := cfbDecryptFinalApi) (W := 832)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cfbDecryptFinal
      verified := Proof.Seed.Arm.cfbDecryptFinal_framed }
    Impl.Seed.Arm.Fn.modeWords []
    (Scrub.cfbDecryptFinalOut _)
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_seed_ofb`. -/
theorem ofb : VerifiedScrubbed target Impl.Seed.Arm.Fn.ofb (ofbContract Arm.abi 832) 0 :=
  verifiedScrubbedSel (api := ofbApi) (W := 832)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.ofb
      verified := Proof.Seed.Arm.ofb_framed }
    Impl.Seed.Arm.Fn.modeWords []
    (Scrub.ofbOut _)
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

/-- `vg_seed_ofb_final`. -/
theorem ofbFinal : VerifiedScrubbed target Impl.Seed.Arm.Fn.ofbFinal (ofbFinalContract Arm.abi 832) 0 :=
  verifiedScrubbedSel (api := ofbFinalApi) (W := 832)
    { code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.ofbFinal
      verified := Proof.Seed.Arm.ofbFinal_framed }
    Impl.Seed.Arm.Fn.modeWords []
    (Scrub.ofbFinalOut _)
    (by decide) hbp_nil ⟨_, by taint_decide_ct⟩

end VG.Proof.Seed.Arm.Fn
