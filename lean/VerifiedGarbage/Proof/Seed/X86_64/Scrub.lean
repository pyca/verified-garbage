module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubSel
public import VerifiedGarbage.Impl.Seed.X86_64.Fn
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Spec.Seed.Contract
public import VerifiedGarbage.Spec.Seed.Cbc
public import VerifiedGarbage.Spec.Seed.Cfb
public import VerifiedGarbage.Spec.Seed.CfbFinal
public import VerifiedGarbage.Spec.Seed.Ofb
public import VerifiedGarbage.Spec.Seed.OfbFinal
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Seed.X86_64.Frame
public import VerifiedGarbage.Proof.Seed.X86_64.ModeCore
public import VerifiedGarbage.Proof.Seed.X86_64.CbcVerified
public import VerifiedGarbage.Proof.Seed.X86_64.FbVerified
public import VerifiedGarbage.Proof.Seed.X86_64.FbFinalVerified
import VerifiedGarbage.Proof.Seed.Scratch
import VerifiedGarbage.Proof.Seed.CbcScratch
import VerifiedGarbage.Proof.Seed.FbScratch
import VerifiedGarbage.Proof.Modes.CfbFinalScratch
import VerifiedGarbage.Proof.Seed.X86_64.Lit
import VerifiedGarbage.Proof.Seed.X86_64.ModesLit
import VerifiedGarbage.Proof.Seed.X86_64.FbFinalLit
meta import VerifiedGarbage.Spec.Seed.Contract
meta import VerifiedGarbage.Spec.Seed.Cbc
meta import VerifiedGarbage.Spec.Seed.Cfb
meta import VerifiedGarbage.Spec.Seed.CfbFinal
meta import VerifiedGarbage.Spec.Seed.Ofb
meta import VerifiedGarbage.Spec.Seed.OfbFinal
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Seed.X86_64.Frame
meta import VerifiedGarbage.Proof.Seed.X86_64.ModeCore
meta import VerifiedGarbage.Proof.Seed.X86_64.CbcVerified
meta import VerifiedGarbage.Proof.Seed.X86_64.FbVerified
meta import VerifiedGarbage.Proof.Seed.X86_64.FbFinalVerified
meta import VerifiedGarbage.Proof.Seed.Scratch
meta import VerifiedGarbage.Proof.Seed.CbcScratch
meta import VerifiedGarbage.Proof.Seed.FbScratch
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Proof.Seed.X86_64.Lit
meta import VerifiedGarbage.Proof.Seed.X86_64.ModesLit
meta import VerifiedGarbage.Proof.Seed.X86_64.FbFinalLit

/-!
# SEED on x86-64, without secret residue

Key expansion and the ECB, CBC, CFB128 and OFB functions, each followed by
`Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`), which clears the
registers and the granules of its stack that the residue analysis
(`X86_64.RTaint`) finds may hold secrets. Their postconditions read the
memory on return only within the buffers (`X86_64.Scrub.PostOut`), as the
frames that keep their working space on the stack already show
(`X86_64.Verified.stackScratchWiped`'s `hpost`).
-/

@[expose] public section

namespace VG.Proof.Seed.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub

/-! ## Postconditions -/

theorem expandKeyOut : PostOut (Spec.Seed.expandKeyContract X86_64.abi 1064) (Spec.Seed.expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.expandKeyPostOut_local _)

theorem ecbEncryptOut : PostOut (Spec.Seed.ecbContract X86_64.abi .encrypt 1104) (Spec.Seed.ecbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.ecbPostOut_local _ .encrypt)

theorem ecbDecryptOut : PostOut (Spec.Seed.ecbContract X86_64.abi .decrypt 1104) (Spec.Seed.ecbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.ecbPostOut_local _ .decrypt)

theorem cbcEncryptOut : PostOut (Spec.Seed.cbcEncryptChainedContract X86_64.abi 1552) (Spec.Seed.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.cbcEncChainedPostOut_local _)

theorem cbcDecryptOut : PostOut (Spec.Seed.cbcDecryptChainedContract X86_64.abi 1552) (Spec.Seed.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.cbcDecChainedPostOut_local _)

theorem cfbEncryptOut : PostOut (Spec.Seed.cfbEncryptContract X86_64.abi 1552) (Spec.Seed.cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.cfbEncPostOut_local _)

theorem cfbEncryptFinalOut : PostOut (Spec.Seed.cfbEncryptFinalContract X86_64.abi 1552) (Spec.Seed.cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.encFinalPost_local _)

theorem cfbDecryptOut : PostOut (Spec.Seed.cfbDecryptContract X86_64.abi 1552) (Spec.Seed.cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.cfbDecPostOut_local _)

theorem cfbDecryptFinalOut : PostOut (Spec.Seed.cfbDecryptFinalContract X86_64.abi 1552) (Spec.Seed.cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.decFinalPost_local _)

theorem ofbOut : PostOut (Spec.Seed.ofbContract X86_64.abi 1552) (Spec.Seed.ofbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Seed.ofbPostOut_local _)

theorem ofbFinalOut : PostOut (Spec.Seed.ofbFinalContract X86_64.abi 1552) (Spec.Seed.ofbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.ofbFinalPost_local _)

/-! ## The registrations -/

/-- `vg_seed_expand_key`'s code. -/
abbrev expandKeyCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 1064 .rdx 132 Impl.Seed.X86_64.expandKey

/-- `vg_seed_ecb_encrypt`'s code. -/
abbrev ecbEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 1096 .rcx 136 (Impl.Seed.X86_64.ecbCall .encrypt)

/-- `vg_seed_ecb_decrypt`'s code. -/
abbrev ecbDecryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 1096 .rcx 136 (Impl.Seed.X86_64.ecbCall .decrypt)

/-- `vg_seed_cbc_encrypt_chained`'s code. -/
abbrev cbcEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cbcEncryptChained

/-- `vg_seed_cbc_decrypt_chained`'s code. -/
abbrev cbcDecryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cbcDecryptChained

/-- `vg_seed_cfb128_encrypt`'s code. -/
abbrev cfbEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cfbEncrypt

/-- `vg_seed_cfb128_encrypt_final`'s code. -/
abbrev cfbEncryptFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cfbEncryptFinal

/-- `vg_seed_cfb128_decrypt`'s code. -/
abbrev cfbDecryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cfbDecrypt

/-- `vg_seed_cfb128_decrypt_final`'s code. -/
abbrev cfbDecryptFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cfbDecryptFinal

/-- `vg_seed_ofb`'s code. -/
abbrev ofbCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.ofb

/-- `vg_seed_ofb_final`'s code. -/
abbrev ofbFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.ofbFinal

/-! ## The functions as emitted -/

theorem expandKey_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 1064 .rdx 132 Impl.Seed.X86_64.expandKey).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Seed.expandKeyApi`'s function as emitted (`Impl.Seed.X86_64.Fn.expandKey`) meets its contract in
constant time and returns without secret residue. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed target Impl.Seed.X86_64.Fn.expandKey (Spec.Seed.expandKeyApi.contract X86_64.abi 1064) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.expandKeyApi)
    { code := expandKeyCode
      stack := 1064
      verified := Proof.Seed.X86_64.expandKey_framed
      spSafe := expandKey_codeSp }
    .sse [(0, 1)] expandKeyOut (RScrub.pubOk_nil _) (by taint_decide)

theorem expandKey_spSafe : Impl.Seed.X86_64.Fn.expandKey.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe expandKey_codeSp

theorem ecbEncrypt_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 1096 .rcx 136 (Impl.Seed.X86_64.ecbCall .encrypt)).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Seed.ecbEncryptApi`'s function as emitted (`Impl.Seed.X86_64.Fn.ecbEncrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem ecbEncrypt_scrubbed :
    VerifiedScrubbed target Impl.Seed.X86_64.Fn.ecbEncrypt (Spec.Seed.ecbEncryptApi.contract X86_64.abi 1104) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.ecbEncryptApi)
    { code := ecbEncryptCode
      stack := 1104
      verified := Proof.Seed.X86_64.ecbCall_framed .encrypt
      spSafe := ecbEncrypt_codeSp }
    .sse [(8, 1)] ecbEncryptOut (RScrub.pubOk_nil _) (by taint_decide)

theorem ecbEncrypt_spSafe : Impl.Seed.X86_64.Fn.ecbEncrypt.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ecbEncrypt_codeSp

theorem ecbDecrypt_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 1096 .rcx 136 (Impl.Seed.X86_64.ecbCall .decrypt)).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Seed.ecbDecryptApi`'s function as emitted (`Impl.Seed.X86_64.Fn.ecbDecrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem ecbDecrypt_scrubbed :
    VerifiedScrubbed target Impl.Seed.X86_64.Fn.ecbDecrypt (Spec.Seed.ecbDecryptApi.contract X86_64.abi 1104) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.ecbDecryptApi)
    { code := ecbDecryptCode
      stack := 1104
      verified := Proof.Seed.X86_64.ecbCall_framed .decrypt
      spSafe := ecbDecrypt_codeSp }
    .sse [(8, 1)] ecbDecryptOut (RScrub.pubOk_nil _) (by taint_decide)

theorem ecbDecrypt_spSafe : Impl.Seed.X86_64.Fn.ecbDecrypt.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ecbDecrypt_codeSp

theorem cbcEncrypt_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cbcEncryptChained).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Seed.cbcEncryptChainedApi`'s function as emitted (`Impl.Seed.X86_64.Fn.cbcEncrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cbcEncrypt_scrubbed :
    VerifiedScrubbed target Impl.Seed.X86_64.Fn.cbcEncrypt (Spec.Seed.cbcEncryptChainedApi.contract X86_64.abi 1552) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.cbcEncryptChainedApi)
    { code := cbcEncryptCode
      stack := 1552
      verified := Proof.Seed.X86_64.cbcEncryptChained_framed
      spSafe := cbcEncrypt_codeSp }
    .sse [(8, 1)] cbcEncryptOut (RScrub.pubOk_nil _) (by taint_decide)

theorem cbcEncrypt_spSafe : Impl.Seed.X86_64.Fn.cbcEncrypt.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cbcEncrypt_codeSp

theorem cbcDecrypt_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cbcDecryptChained).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Seed.cbcDecryptChainedApi`'s function as emitted (`Impl.Seed.X86_64.Fn.cbcDecrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cbcDecrypt_scrubbed :
    VerifiedScrubbed target Impl.Seed.X86_64.Fn.cbcDecrypt (Spec.Seed.cbcDecryptChainedApi.contract X86_64.abi 1552) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.cbcDecryptChainedApi)
    { code := cbcDecryptCode
      stack := 1552
      verified := Proof.Seed.X86_64.cbcDecryptChained_framed
      spSafe := cbcDecrypt_codeSp }
    .sse [(8, 1)] cbcDecryptOut (RScrub.pubOk_nil _) (by taint_decide)

theorem cbcDecrypt_spSafe : Impl.Seed.X86_64.Fn.cbcDecrypt.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cbcDecrypt_codeSp

theorem cfbEncrypt_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cfbEncrypt).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Seed.cfbEncryptApi`'s function as emitted (`Impl.Seed.X86_64.Fn.cfbEncrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed target Impl.Seed.X86_64.Fn.cfbEncrypt (Spec.Seed.cfbEncryptApi.contract X86_64.abi 1552) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.cfbEncryptApi)
    { code := cfbEncryptCode
      stack := 1552
      verified := Proof.Seed.X86_64.cfbEncrypt_framed
      spSafe := cfbEncrypt_codeSp }
    .sse [(8, 1)] cfbEncryptOut (RScrub.pubOk_nil _) (by taint_decide)

theorem cfbEncrypt_spSafe : Impl.Seed.X86_64.Fn.cfbEncrypt.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cfbEncrypt_codeSp

theorem cfbEncryptFinal_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cfbEncryptFinal).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Seed.cfbEncryptFinalApi`'s function as emitted (`Impl.Seed.X86_64.Fn.cfbEncryptFinal`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed target Impl.Seed.X86_64.Fn.cfbEncryptFinal (Spec.Seed.cfbEncryptFinalApi.contract X86_64.abi 1552) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.cfbEncryptFinalApi)
    { code := cfbEncryptFinalCode
      stack := 1552
      verified := Proof.Seed.X86_64.cfbEncryptFinal_framed
      spSafe := cfbEncryptFinal_codeSp }
    .sse [(8, 1)] cfbEncryptFinalOut (RScrub.pubOk_nil _) (by taint_decide)

theorem cfbEncryptFinal_spSafe : Impl.Seed.X86_64.Fn.cfbEncryptFinal.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cfbEncryptFinal_codeSp

theorem cfbDecrypt_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cfbDecrypt).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Seed.cfbDecryptApi`'s function as emitted (`Impl.Seed.X86_64.Fn.cfbDecrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed target Impl.Seed.X86_64.Fn.cfbDecrypt (Spec.Seed.cfbDecryptApi.contract X86_64.abi 1552) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.cfbDecryptApi)
    { code := cfbDecryptCode
      stack := 1552
      verified := Proof.Seed.X86_64.cfbDecrypt_framed
      spSafe := cfbDecrypt_codeSp }
    .sse [(8, 1)] cfbDecryptOut (RScrub.pubOk_nil _) (by taint_decide)

theorem cfbDecrypt_spSafe : Impl.Seed.X86_64.Fn.cfbDecrypt.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cfbDecrypt_codeSp

theorem cfbDecryptFinal_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cfbDecryptFinal).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Seed.cfbDecryptFinalApi`'s function as emitted (`Impl.Seed.X86_64.Fn.cfbDecryptFinal`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed target Impl.Seed.X86_64.Fn.cfbDecryptFinal (Spec.Seed.cfbDecryptFinalApi.contract X86_64.abi 1552) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.cfbDecryptFinalApi)
    { code := cfbDecryptFinalCode
      stack := 1552
      verified := Proof.Seed.X86_64.cfbDecryptFinal_framed
      spSafe := cfbDecryptFinal_codeSp }
    .sse [(8, 1)] cfbDecryptFinalOut (RScrub.pubOk_nil _) (by taint_decide)

theorem cfbDecryptFinal_spSafe : Impl.Seed.X86_64.Fn.cfbDecryptFinal.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cfbDecryptFinal_codeSp

theorem ofb_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.ofb).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Seed.ofbApi`'s function as emitted (`Impl.Seed.X86_64.Fn.ofb`) meets its contract in
constant time and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed target Impl.Seed.X86_64.Fn.ofb (Spec.Seed.ofbApi.contract X86_64.abi 1552) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.ofbApi)
    { code := ofbCode
      stack := 1552
      verified := Proof.Seed.X86_64.ofb_framed
      spSafe := ofb_codeSp }
    .sse [(8, 1)] ofbOut (RScrub.pubOk_nil _) (by taint_decide)

theorem ofb_spSafe : Impl.Seed.X86_64.Fn.ofb.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ofb_codeSp

theorem ofbFinal_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.ofbFinal).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Seed.ofbFinalApi`'s function as emitted (`Impl.Seed.X86_64.Fn.ofbFinal`) meets its contract in
constant time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed target Impl.Seed.X86_64.Fn.ofbFinal (Spec.Seed.ofbFinalApi.contract X86_64.abi 1552) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.ofbFinalApi)
    { code := ofbFinalCode
      stack := 1552
      verified := Proof.Seed.X86_64.ofbFinal_framed
      spSafe := ofbFinal_codeSp }
    .sse [(8, 1)] ofbFinalOut (RScrub.pubOk_nil _) (by taint_decide)

theorem ofbFinal_spSafe : Impl.Seed.X86_64.Fn.ofbFinal.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ofbFinal_codeSp
end VG.Proof.Seed.X86_64.Scrub

