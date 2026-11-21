module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubSel
public import VerifiedGarbage.Impl.Sm4.X86_64.Fn
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Spec.Sm4.Contract
public import VerifiedGarbage.Spec.Sm4.Cbc
public import VerifiedGarbage.Spec.Sm4.Cfb
public import VerifiedGarbage.Spec.Sm4.CfbFinal
public import VerifiedGarbage.Spec.Sm4.Ofb
public import VerifiedGarbage.Spec.Sm4.OfbFinal
public import VerifiedGarbage.Spec.Sm4.Ctr
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sm4.X86_64.Verified
public import VerifiedGarbage.Proof.Sm4.X86_64.CbcVerified
public import VerifiedGarbage.Proof.Sm4.X86_64.FbFinalVerified
public import VerifiedGarbage.Proof.Sm4.X86_64.CtrVerified
public import VerifiedGarbage.Proof.Sm4.X86_64.CtrFinal
public import VerifiedGarbage.Spec.Sm4.CtrFinal
public import VerifiedGarbage.Proof.Sm4.X86_64.KeyVerified
import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Sm4.CbcScratch
import VerifiedGarbage.Proof.Sm4.FbScratch
import VerifiedGarbage.Proof.Modes.CfbFinalScratch
import VerifiedGarbage.Proof.Sm4.X86_64.Lit
import VerifiedGarbage.Proof.Sm4.X86_64.ModesLit
import VerifiedGarbage.Proof.Sm4.X86_64.FbFinalLit
meta import VerifiedGarbage.Spec.Sm4.Contract
meta import VerifiedGarbage.Spec.Sm4.Cbc
meta import VerifiedGarbage.Spec.Sm4.Cfb
meta import VerifiedGarbage.Spec.Sm4.CfbFinal
meta import VerifiedGarbage.Spec.Sm4.Ofb
meta import VerifiedGarbage.Spec.Sm4.OfbFinal
meta import VerifiedGarbage.Spec.Sm4.Ctr
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Sm4.X86_64.Verified
meta import VerifiedGarbage.Proof.Sm4.X86_64.CbcVerified
meta import VerifiedGarbage.Proof.Sm4.X86_64.FbFinalVerified
meta import VerifiedGarbage.Proof.Sm4.X86_64.CtrVerified
meta import VerifiedGarbage.Proof.Sm4.X86_64.CtrFinal
meta import VerifiedGarbage.Spec.Sm4.CtrFinal
meta import VerifiedGarbage.Proof.Sm4.X86_64.KeyVerified
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Sm4.CbcScratch
meta import VerifiedGarbage.Proof.Sm4.FbScratch
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Proof.Sm4.X86_64.Lit
meta import VerifiedGarbage.Proof.Sm4.X86_64.ModesLit
meta import VerifiedGarbage.Proof.Sm4.X86_64.FbFinalLit

/-!
# SM4 on x86-64, without secret residue

Key expansion and the ECB, CBC, CFB128, OFB and CTR functions, each followed by
`Impl.Scrub.X86_64.scrubSel` (`X86_64.Scrub.verifiedScrubbedSel`), which clears every
caller-saved register and the granules of its stack that the residue analysis
(`X86_64.RTaint`) finds may hold secrets. Their postconditions read the
memory on return only within the buffers (`X86_64.Scrub.PostOut`), as the
frames that keep their working space on the stack already show
(`X86_64.Verified.stackScratchWiped`'s `hpost`).

`vg_sm4_ctr_final`, whose analysis does not succeed, is followed by
`Impl.Scrub.X86_64.scrubAll` (`X86_64.Scrub.verifiedScrubbedAll`), which wipes
every granule of its stack: it calls `vg_sm4_ctr`'s code as the internal
`vg_sm4_ctr_core` (`Impl.Sm4.X86_64.ctrFramed`), which restores the callee-saved
registers from slots of its frame the analysis loses track of. SM4-GCM calls
`vg_sm4_expand_key`'s code as the internal `vg_sm4_expand_key_core`
(`Impl.Sm4Gcm.X86_64.keyFn`).
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub

/-! ## Postconditions -/

theorem expandKeyOut : PostOut (Spec.Sm4.expandKeyContract X86_64.abi 3144) (Spec.Sm4.expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.expandKeyPostOut_local _)

theorem ecbEncryptOut : PostOut (Spec.Sm4.ecbContract X86_64.abi .encrypt 3144) (Spec.Sm4.ecbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ecbPostOut_local _ .encrypt)

theorem ecbDecryptOut : PostOut (Spec.Sm4.ecbContract X86_64.abi .decrypt 3144) (Spec.Sm4.ecbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ecbPostOut_local _ .decrypt)

theorem cbcEncryptOut : PostOut (Spec.Sm4.cbcEncryptChainedContract X86_64.abi 3216) (Spec.Sm4.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cbcEncChainedPostOut_local _)

theorem cbcDecryptOut : PostOut (Spec.Sm4.cbcDecryptChainedContract X86_64.abi 3216) (Spec.Sm4.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cbcDecChainedPostOut_local _)

theorem cfbEncryptOut : PostOut (Spec.Sm4.cfbEncryptContract X86_64.abi 3216) (Spec.Sm4.cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cfbEncPostOut_local _)

theorem cfbEncryptFinalOut : PostOut (Spec.Sm4.cfbEncryptFinalContract X86_64.abi 3216) (Spec.Sm4.cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.encFinalPost_local _)

theorem cfbDecryptOut : PostOut (Spec.Sm4.cfbDecryptContract X86_64.abi 3216) (Spec.Sm4.cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.cfbDecPostOut_local _)

theorem cfbDecryptFinalOut : PostOut (Spec.Sm4.cfbDecryptFinalContract X86_64.abi 3216) (Spec.Sm4.cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.decFinalPost_local _)

theorem ofbOut : PostOut (Spec.Sm4.ofbContract X86_64.abi 3216) (Spec.Sm4.ofbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ofbPostOut_local _)

theorem ofbFinalOut : PostOut (Spec.Sm4.ofbFinalContract X86_64.abi 3216) (Spec.Sm4.ofbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.ofbFinalPost_local _)

theorem ctrOut : PostOut (Spec.Sm4.ctrContract X86_64.abi 3216) (Spec.Sm4.ctrSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ctrPostOut_local _)

theorem ctrFinalOut : PostOut (Spec.Sm4.ctrFinalContract X86_64.abi 3296) (Spec.Sm4.ctrFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.ctrFinalPostOut_local _)

/-! ## The registrations -/

/-- `vg_sm4_expand_key`'s code. -/
abbrev expandKeyCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3144 .rdx 392 Impl.Sm4.X86_64.expandKey

/-- `vg_sm4_ecb_encrypt`'s code. -/
abbrev ecbEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3144 .rcx 392 (Impl.Sm4.X86_64.ecb .encrypt)

/-- `vg_sm4_ecb_decrypt`'s code. -/
abbrev ecbDecryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3144 .rcx 392 (Impl.Sm4.X86_64.ecb .decrypt)

/-- `vg_sm4_cbc_encrypt_chained`'s code. -/
abbrev cbcEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cbcEncryptChained

/-- `vg_sm4_cbc_decrypt_chained`'s code. -/
abbrev cbcDecryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cbcDecryptChained

/-- `vg_sm4_cfb128_encrypt`'s code. -/
abbrev cfbEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cfbEncrypt

/-- `vg_sm4_cfb128_encrypt_final`'s code. -/
abbrev cfbEncryptFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cfbEncryptFinal

/-- `vg_sm4_cfb128_decrypt`'s code. -/
abbrev cfbDecryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cfbDecrypt

/-- `vg_sm4_cfb128_decrypt_final`'s code. -/
abbrev cfbDecryptFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cfbDecryptFinal

/-- `vg_sm4_ofb`'s code. -/
abbrev ofbCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.ofb

/-- `vg_sm4_ofb_final`'s code. -/
abbrev ofbFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.ofbFinal

/-- `vg_sm4_ctr`'s code. -/
abbrev ctrCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.ctr

/-! ## The functions as emitted -/

theorem expandKey_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 3144 .rdx 392 Impl.Sm4.X86_64.expandKey).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Sm4.expandKeyApi`'s function as emitted (`Impl.Sm4.X86_64.Fn.expandKey`) meets its contract in
constant time and returns without secret residue. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed target Impl.Sm4.X86_64.Fn.expandKey (Spec.Sm4.expandKeyApi.contract X86_64.abi 3144) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.expandKeyApi)
    { code := expandKeyCode
      stack := 3144
      verified := Proof.Sm4.X86_64.expandKey_framed
      spSafe := expandKey_codeSp }
    .sse [(0, 1)] expandKeyOut (RScrub.pubOk_nil _) (by taint_decide)

theorem expandKey_spSafe : Impl.Sm4.X86_64.Fn.expandKey.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe expandKey_codeSp

theorem ecbEncrypt_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 3144 .rcx 392 (Impl.Sm4.X86_64.ecb .encrypt)).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Sm4.ecbEncryptApi`'s function as emitted (`Impl.Sm4.X86_64.Fn.ecbEncrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem ecbEncrypt_scrubbed :
    VerifiedScrubbed target Impl.Sm4.X86_64.Fn.ecbEncrypt (Spec.Sm4.ecbEncryptApi.contract X86_64.abi 3144) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.ecbEncryptApi)
    { code := ecbEncryptCode
      stack := 3144
      verified := Proof.Sm4.X86_64.ecb_framed .encrypt
      spSafe := ecbEncrypt_codeSp }
    .sse [(0, 1)] ecbEncryptOut (RScrub.pubOk_nil _) (by taint_decide)

theorem ecbEncrypt_spSafe : Impl.Sm4.X86_64.Fn.ecbEncrypt.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ecbEncrypt_codeSp

theorem ecbDecrypt_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 3144 .rcx 392 (Impl.Sm4.X86_64.ecb .decrypt)).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Sm4.ecbDecryptApi`'s function as emitted (`Impl.Sm4.X86_64.Fn.ecbDecrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem ecbDecrypt_scrubbed :
    VerifiedScrubbed target Impl.Sm4.X86_64.Fn.ecbDecrypt (Spec.Sm4.ecbDecryptApi.contract X86_64.abi 3144) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.ecbDecryptApi)
    { code := ecbDecryptCode
      stack := 3144
      verified := Proof.Sm4.X86_64.ecb_framed .decrypt
      spSafe := ecbDecrypt_codeSp }
    .sse [(0, 1)] ecbDecryptOut (RScrub.pubOk_nil _) (by taint_decide)

theorem ecbDecrypt_spSafe : Impl.Sm4.X86_64.Fn.ecbDecrypt.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ecbDecrypt_codeSp

theorem cbcEncrypt_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cbcEncryptChained).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Sm4.cbcEncryptChainedApi`'s function as emitted (`Impl.Sm4.X86_64.Fn.cbcEncrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cbcEncrypt_scrubbed :
    VerifiedScrubbed target Impl.Sm4.X86_64.Fn.cbcEncrypt (Spec.Sm4.cbcEncryptChainedApi.contract X86_64.abi 3216) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.cbcEncryptChainedApi)
    { code := cbcEncryptCode
      stack := 3216
      verified := Proof.Sm4.X86_64.cbcEncryptChained_framed
      spSafe := cbcEncrypt_codeSp }
    .sse [(8, 1)] cbcEncryptOut (RScrub.pubOk_nil _) (by taint_decide)

theorem cbcEncrypt_spSafe : Impl.Sm4.X86_64.Fn.cbcEncrypt.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cbcEncrypt_codeSp

theorem cbcDecrypt_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cbcDecryptChained).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Sm4.cbcDecryptChainedApi`'s function as emitted (`Impl.Sm4.X86_64.Fn.cbcDecrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cbcDecrypt_scrubbed :
    VerifiedScrubbed target Impl.Sm4.X86_64.Fn.cbcDecrypt (Spec.Sm4.cbcDecryptChainedApi.contract X86_64.abi 3216) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.cbcDecryptChainedApi)
    { code := cbcDecryptCode
      stack := 3216
      verified := Proof.Sm4.X86_64.cbcDecryptChained_framed
      spSafe := cbcDecrypt_codeSp }
    .sse [(8, 1)] cbcDecryptOut (RScrub.pubOk_nil _) (by taint_decide)

theorem cbcDecrypt_spSafe : Impl.Sm4.X86_64.Fn.cbcDecrypt.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cbcDecrypt_codeSp

theorem cfbEncrypt_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cfbEncrypt).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Sm4.cfbEncryptApi`'s function as emitted (`Impl.Sm4.X86_64.Fn.cfbEncrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed target Impl.Sm4.X86_64.Fn.cfbEncrypt (Spec.Sm4.cfbEncryptApi.contract X86_64.abi 3216) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.cfbEncryptApi)
    { code := cfbEncryptCode
      stack := 3216
      verified := Proof.Sm4.X86_64.cfbEncrypt_framed
      spSafe := cfbEncrypt_codeSp }
    .sse [(8, 1)] cfbEncryptOut (RScrub.pubOk_nil _) (by taint_decide)

theorem cfbEncrypt_spSafe : Impl.Sm4.X86_64.Fn.cfbEncrypt.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cfbEncrypt_codeSp

theorem cfbEncryptFinal_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cfbEncryptFinal).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Sm4.cfbEncryptFinalApi`'s function as emitted (`Impl.Sm4.X86_64.Fn.cfbEncryptFinal`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed target Impl.Sm4.X86_64.Fn.cfbEncryptFinal (Spec.Sm4.cfbEncryptFinalApi.contract X86_64.abi 3216) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.cfbEncryptFinalApi)
    { code := cfbEncryptFinalCode
      stack := 3216
      verified := Proof.Sm4.X86_64.cfbEncryptFinal_framed
      spSafe := cfbEncryptFinal_codeSp }
    .sse [(8, 1)] cfbEncryptFinalOut (RScrub.pubOk_nil _) (by taint_decide)

theorem cfbEncryptFinal_spSafe : Impl.Sm4.X86_64.Fn.cfbEncryptFinal.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cfbEncryptFinal_codeSp

theorem cfbDecrypt_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cfbDecrypt).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Sm4.cfbDecryptApi`'s function as emitted (`Impl.Sm4.X86_64.Fn.cfbDecrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed target Impl.Sm4.X86_64.Fn.cfbDecrypt (Spec.Sm4.cfbDecryptApi.contract X86_64.abi 3216) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.cfbDecryptApi)
    { code := cfbDecryptCode
      stack := 3216
      verified := Proof.Sm4.X86_64.cfbDecrypt_framed
      spSafe := cfbDecrypt_codeSp }
    .sse [(8, 1)] cfbDecryptOut (RScrub.pubOk_nil _) (by taint_decide)

theorem cfbDecrypt_spSafe : Impl.Sm4.X86_64.Fn.cfbDecrypt.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cfbDecrypt_codeSp

theorem cfbDecryptFinal_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cfbDecryptFinal).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Sm4.cfbDecryptFinalApi`'s function as emitted (`Impl.Sm4.X86_64.Fn.cfbDecryptFinal`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed target Impl.Sm4.X86_64.Fn.cfbDecryptFinal (Spec.Sm4.cfbDecryptFinalApi.contract X86_64.abi 3216) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.cfbDecryptFinalApi)
    { code := cfbDecryptFinalCode
      stack := 3216
      verified := Proof.Sm4.X86_64.cfbDecryptFinal_framed
      spSafe := cfbDecryptFinal_codeSp }
    .sse [(8, 1)] cfbDecryptFinalOut (RScrub.pubOk_nil _) (by taint_decide)

theorem cfbDecryptFinal_spSafe : Impl.Sm4.X86_64.Fn.cfbDecryptFinal.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cfbDecryptFinal_codeSp

theorem ofb_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.ofb).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Sm4.ofbApi`'s function as emitted (`Impl.Sm4.X86_64.Fn.ofb`) meets its contract in
constant time and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed target Impl.Sm4.X86_64.Fn.ofb (Spec.Sm4.ofbApi.contract X86_64.abi 3216) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.ofbApi)
    { code := ofbCode
      stack := 3216
      verified := Proof.Sm4.X86_64.ofb_framed
      spSafe := ofb_codeSp }
    .sse [(8, 1)] ofbOut (RScrub.pubOk_nil _) (by taint_decide)

theorem ofb_spSafe : Impl.Sm4.X86_64.Fn.ofb.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ofb_codeSp

theorem ofbFinal_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.ofbFinal).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Sm4.ofbFinalApi`'s function as emitted (`Impl.Sm4.X86_64.Fn.ofbFinal`) meets its contract in
constant time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed target Impl.Sm4.X86_64.Fn.ofbFinal (Spec.Sm4.ofbFinalApi.contract X86_64.abi 3216) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.ofbFinalApi)
    { code := ofbFinalCode
      stack := 3216
      verified := Proof.Sm4.X86_64.ofbFinal_framed
      spSafe := ofbFinal_codeSp }
    .sse [(8, 1)] ofbFinalOut (RScrub.pubOk_nil _) (by taint_decide)

theorem ofbFinal_spSafe : Impl.Sm4.X86_64.Fn.ofbFinal.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ofbFinal_codeSp

theorem ctr_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.ctr).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Sm4.ctrApi`'s function as emitted (`Impl.Sm4.X86_64.Fn.ctr`) meets its contract in
constant time and returns without secret residue. -/
theorem ctr_scrubbed :
    VerifiedScrubbed target Impl.Sm4.X86_64.Fn.ctr (Spec.Sm4.ctrApi.contract X86_64.abi 3216) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.ctrApi)
    { code := ctrCode
      stack := 3216
      verified := Proof.Sm4.X86_64.ctr_framed
      spSafe := ctr_codeSp }
    .sse [(8, 1)] ctrOut (RScrub.pubOk_nil _) (by taint_decide)

theorem ctr_spSafe : Impl.Sm4.X86_64.Fn.ctr.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ctr_codeSp

theorem ctrFinal_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 72 .r8 8 Impl.Sm4.X86_64.ctrFinal).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Sm4.ctrFinalApi`'s function as emitted (`Impl.Sm4.X86_64.Fn.ctrFinal`) meets its contract in
constant time and returns without secret residue. -/
theorem ctrFinal_scrubbed :
    VerifiedScrubbed target Impl.Sm4.X86_64.Fn.ctrFinal (Spec.Sm4.ctrFinalApi.contract X86_64.abi 3296) 0 :=
  verifiedScrubbedAll (api := Spec.Sm4.ctrFinalApi)
    { code := Impl.StackScratch.X86_64.withStackScratchWiped 72 .r8 8 Impl.Sm4.X86_64.ctrFinal
      stack := 3296
      verified := Proof.Sm4.X86_64.ctrFinal_framed
      spSafe := ctrFinal_codeSp }
    .sse ctrFinalOut

theorem ctrFinal_spSafe : Impl.Sm4.X86_64.Fn.ctrFinal.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ctrFinal_codeSp
end VG.Proof.Sm4.X86_64.Scrub
