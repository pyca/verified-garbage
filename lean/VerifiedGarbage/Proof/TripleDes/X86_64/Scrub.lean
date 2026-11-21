module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubSel
public import VerifiedGarbage.Impl.TripleDes.X86_64.Fn
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Spec.TripleDes.Contract
public import VerifiedGarbage.Spec.TripleDes.Cbc
public import VerifiedGarbage.Spec.TripleDes.Cfb
public import VerifiedGarbage.Spec.TripleDes.Cfb8
public import VerifiedGarbage.Spec.TripleDes.CfbFinal
public import VerifiedGarbage.Spec.TripleDes.Ofb
public import VerifiedGarbage.Spec.TripleDes.OfbFinal
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.TripleDes.X86_64.Frame
public import VerifiedGarbage.Proof.TripleDes.X86_64.CbcVerified
public import VerifiedGarbage.Proof.TripleDes.X86_64.FbVerified
public import VerifiedGarbage.Proof.TripleDes.X86_64.FbFinalVerified
public import VerifiedGarbage.Proof.TripleDes.X86_64.Batch.Call
import VerifiedGarbage.Proof.TripleDes.Scratch
import VerifiedGarbage.Proof.TripleDes.CbcScratch
import VerifiedGarbage.Proof.TripleDes.FbScratch
import VerifiedGarbage.Proof.Modes.CfbFinalScratch
import VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.X86_64.CbcLit
import VerifiedGarbage.Proof.TripleDes.X86_64.FbLit
import VerifiedGarbage.Proof.TripleDes.X86_64.FbFinalLit
import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Lit
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.SboxLit
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.SboxLit
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.SboxLit
import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.SboxLit
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.Lit
meta import VerifiedGarbage.Spec.TripleDes.Contract
meta import VerifiedGarbage.Spec.TripleDes.Cbc
meta import VerifiedGarbage.Spec.TripleDes.Cfb
meta import VerifiedGarbage.Spec.TripleDes.Cfb8
meta import VerifiedGarbage.Spec.TripleDes.CfbFinal
meta import VerifiedGarbage.Spec.TripleDes.Ofb
meta import VerifiedGarbage.Spec.TripleDes.OfbFinal
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.TripleDes.X86_64.Frame
meta import VerifiedGarbage.Proof.TripleDes.X86_64.CbcVerified
meta import VerifiedGarbage.Proof.TripleDes.X86_64.FbVerified
meta import VerifiedGarbage.Proof.TripleDes.X86_64.FbFinalVerified
meta import VerifiedGarbage.Proof.TripleDes.X86_64.Batch.Call
meta import VerifiedGarbage.Proof.TripleDes.Scratch
meta import VerifiedGarbage.Proof.TripleDes.CbcScratch
meta import VerifiedGarbage.Proof.TripleDes.FbScratch
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.CbcLit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.FbLit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.FbFinalLit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Lit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.SboxLit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.SboxLit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.SboxLit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.Lit

/-!
# Triple DES on x86-64, without secret residue

Key expansion and the ECB, CBC encryption, CFB64 encryption, CFB8, OFB and
final functions, each followed by `Impl.Scrub.X86_64.scrubTail`
(`X86_64.Scrub.withScrub`), which clears the registers and the granules of
its stack that the residue analysis (`X86_64.RTaint`) finds may hold secrets.
Their postconditions read the memory on return only within the buffers
(`X86_64.Scrub.PostOut`), as the frames that keep their working space on the
stack already show (`X86_64.Verified.stackScratchWiped`'s `hpost`).

The batched CBC and CFB64 decryption call the ECB functions' code as
internal functions of their own (`Batch.EcbImpl.name`,
`vg_triple_des_ecb_<direction><suffix>_core`). That batched decryption is not
here
(`vg_triple_des_cbc_decrypt_chained`, `vg_triple_des_cfb64_decrypt` and their
variants): the analysis loses every base register across the call of the ECB
function, and then fails on the XOR that follows it.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub

/-! ## Postconditions -/

theorem expandKeyOut : PostOut (Spec.TripleDes.expandKeyContract X86_64.abi 520) (Spec.TripleDes.expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.expandKeyPostOut_local _)

theorem cbcEncryptOut : PostOut (Spec.TripleDes.cbcEncryptChainedContract X86_64.abi 984) (Spec.TripleDes.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cbcEncChainedPostOut_local _)

theorem cfbEncryptOut : PostOut (Spec.TripleDes.cfbEncryptContract X86_64.abi 984) (Spec.TripleDes.cfbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cfbEncPostOut_local _)

theorem cfbEncryptFinalOut : PostOut (Spec.TripleDes.cfbEncryptFinalContract X86_64.abi 984) (Spec.TripleDes.cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.encFinalPost_local _)

theorem cfbDecryptFinalOut : PostOut (Spec.TripleDes.cfbDecryptFinalContract X86_64.abi 984) (Spec.TripleDes.cfbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.decFinalPost_local _)

theorem cfb8EncryptOut : PostOut (Spec.TripleDes.cfb8EncryptContract X86_64.abi 984) (Spec.TripleDes.cfb8Sig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cfb8EncPostOut_local _)

theorem cfb8DecryptOut : PostOut (Spec.TripleDes.cfb8DecryptContract X86_64.abi 984) (Spec.TripleDes.cfb8Sig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cfb8DecPostOut_local _)

theorem ofbOut : PostOut (Spec.TripleDes.ofbContract X86_64.abi 984) (Spec.TripleDes.ofbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.ofbPostOut_local _)

theorem ofbFinalOut : PostOut (Spec.TripleDes.ofbFinalContract X86_64.abi 984) (Spec.TripleDes.ofbFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.ofbFinalPost_local _)

theorem ecbOut (d : Spec.TripleDes.Direction) :
    PostOut (Spec.TripleDes.ecbContract X86_64.abi d 1040) (Spec.TripleDes.ecbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.ecbPostOut_local _ d)

/-! ## The registrations -/

/-- `vg_triple_des_expand_key`'s code. -/
abbrev expandKeyCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 520 .rcx 64 Impl.TripleDes.X86_64.Key.expandKey

/-- `vg_triple_des_cbc_encrypt_chained`'s code. -/
abbrev cbcEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cbcEncryptChained

/-- `vg_triple_des_cfb64_encrypt`'s code. -/
abbrev cfbEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfbEncrypt

/-- `vg_triple_des_cfb64_encrypt_final`'s code. -/
abbrev cfbEncryptFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfbEncryptFinal

/-- `vg_triple_des_cfb64_decrypt_final`'s code. -/
abbrev cfbDecryptFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfbDecryptFinal

/-- `vg_triple_des_cfb8_encrypt`'s code. -/
abbrev cfb8EncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfb8Encrypt

/-- `vg_triple_des_cfb8_decrypt`'s code. -/
abbrev cfb8DecryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfb8Decrypt

/-- `vg_triple_des_ofb`'s code. -/
abbrev ofbCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.ofb

/-- `vg_triple_des_ofb_final`'s code. -/
abbrev ofbFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.ofbFinal

/-- `vg_triple_des_ecb_encrypt_avx512`'s code. -/
abbrev ecbEncryptAvx512Code : Prog isa := Batch.avx512.code .encrypt

/-- `vg_triple_des_ecb_encrypt_avx2`'s code. -/
abbrev ecbEncryptAvx2Code : Prog isa := Batch.avx2.code .encrypt

/-- `vg_triple_des_ecb_encrypt`'s code. -/
abbrev ecbEncryptSseCode : Prog isa := Batch.sse.code .encrypt

/-- `vg_triple_des_ecb_decrypt_avx512`'s code. -/
abbrev ecbDecryptAvx512Code : Prog isa := Batch.avx512.code .decrypt

/-- `vg_triple_des_ecb_decrypt_avx2`'s code. -/
abbrev ecbDecryptAvx2Code : Prog isa := Batch.avx2.code .decrypt

/-- `vg_triple_des_ecb_decrypt`'s code. -/
abbrev ecbDecryptSseCode : Prog isa := Batch.sse.code .decrypt

/-! ## The functions as emitted -/

theorem expandKey_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 520 .rcx 64 Impl.TripleDes.X86_64.Key.expandKey).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.TripleDes.expandKeyApi`'s function as emitted (`Impl.TripleDes.X86_64.Fn.expandKey`) meets its contract in
constant time and returns without secret residue. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed target Impl.TripleDes.X86_64.Fn.expandKey (Spec.TripleDes.expandKeyApi.contract X86_64.abi 520) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.expandKeyApi)
    { code := expandKeyCode
      stack := 520
      verified := Proof.TripleDes.X86_64.expandKey_framed
      spSafe := expandKey_codeSp }
    .sse [(0, 1)] expandKeyOut (RScrub.pubOk_nil _) (by taint_decide)

theorem expandKey_spSafe : Impl.TripleDes.X86_64.Fn.expandKey.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe expandKey_codeSp

theorem cbcEncrypt_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cbcEncryptChained).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.TripleDes.cbcEncryptChainedApi`'s function as emitted (`Impl.TripleDes.X86_64.Fn.cbcEncrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cbcEncrypt_scrubbed :
    VerifiedScrubbed target Impl.TripleDes.X86_64.Fn.cbcEncrypt (Spec.TripleDes.cbcEncryptChainedApi.contract X86_64.abi 984) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cbcEncryptChainedApi)
    { code := cbcEncryptCode
      stack := 984
      verified := Proof.TripleDes.X86_64.cbcEncryptChained_framed
      spSafe := cbcEncrypt_codeSp }
    .sse [(0, 1)] cbcEncryptOut (RScrub.pubOk_nil _) (by taint_decide)

theorem cbcEncrypt_spSafe : Impl.TripleDes.X86_64.Fn.cbcEncrypt.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cbcEncrypt_codeSp

theorem cfbEncrypt_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfbEncrypt).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.TripleDes.cfbEncryptApi`'s function as emitted (`Impl.TripleDes.X86_64.Fn.cfbEncrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed target Impl.TripleDes.X86_64.Fn.cfbEncrypt (Spec.TripleDes.cfbEncryptApi.contract X86_64.abi 984) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cfbEncryptApi)
    { code := cfbEncryptCode
      stack := 984
      verified := Proof.TripleDes.X86_64.cfbEncrypt_framed
      spSafe := cfbEncrypt_codeSp }
    .sse [(0, 1)] cfbEncryptOut (RScrub.pubOk_nil _) (by taint_decide)

theorem cfbEncrypt_spSafe : Impl.TripleDes.X86_64.Fn.cfbEncrypt.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cfbEncrypt_codeSp

theorem cfbEncryptFinal_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfbEncryptFinal).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.TripleDes.cfbEncryptFinalApi`'s function as emitted (`Impl.TripleDes.X86_64.Fn.cfbEncryptFinal`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed target Impl.TripleDes.X86_64.Fn.cfbEncryptFinal (Spec.TripleDes.cfbEncryptFinalApi.contract X86_64.abi 984) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cfbEncryptFinalApi)
    { code := cfbEncryptFinalCode
      stack := 984
      verified := Proof.TripleDes.X86_64.cfbEncryptFinal_framed
      spSafe := cfbEncryptFinal_codeSp }
    .sse [(0, 1)] cfbEncryptFinalOut (RScrub.pubOk_nil _) (by taint_decide)

theorem cfbEncryptFinal_spSafe : Impl.TripleDes.X86_64.Fn.cfbEncryptFinal.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cfbEncryptFinal_codeSp

theorem cfbDecryptFinal_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfbDecryptFinal).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.TripleDes.cfbDecryptFinalApi`'s function as emitted (`Impl.TripleDes.X86_64.Fn.cfbDecryptFinal`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed target Impl.TripleDes.X86_64.Fn.cfbDecryptFinal (Spec.TripleDes.cfbDecryptFinalApi.contract X86_64.abi 984) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cfbDecryptFinalApi)
    { code := cfbDecryptFinalCode
      stack := 984
      verified := Proof.TripleDes.X86_64.cfbDecryptFinal_framed
      spSafe := cfbDecryptFinal_codeSp }
    .sse [(0, 1)] cfbDecryptFinalOut (RScrub.pubOk_nil _) (by taint_decide)

theorem cfbDecryptFinal_spSafe : Impl.TripleDes.X86_64.Fn.cfbDecryptFinal.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cfbDecryptFinal_codeSp

theorem cfb8Encrypt_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfb8Encrypt).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.TripleDes.cfb8EncryptApi`'s function as emitted (`Impl.TripleDes.X86_64.Fn.cfb8Encrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cfb8Encrypt_scrubbed :
    VerifiedScrubbed target Impl.TripleDes.X86_64.Fn.cfb8Encrypt (Spec.TripleDes.cfb8EncryptApi.contract X86_64.abi 984) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cfb8EncryptApi)
    { code := cfb8EncryptCode
      stack := 984
      verified := Proof.TripleDes.X86_64.cfb8Encrypt_framed
      spSafe := cfb8Encrypt_codeSp }
    .sse [(0, 1)] cfb8EncryptOut (RScrub.pubOk_nil _) (by taint_decide)

theorem cfb8Encrypt_spSafe : Impl.TripleDes.X86_64.Fn.cfb8Encrypt.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cfb8Encrypt_codeSp

theorem cfb8Decrypt_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfb8Decrypt).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.TripleDes.cfb8DecryptApi`'s function as emitted (`Impl.TripleDes.X86_64.Fn.cfb8Decrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cfb8Decrypt_scrubbed :
    VerifiedScrubbed target Impl.TripleDes.X86_64.Fn.cfb8Decrypt (Spec.TripleDes.cfb8DecryptApi.contract X86_64.abi 984) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cfb8DecryptApi)
    { code := cfb8DecryptCode
      stack := 984
      verified := Proof.TripleDes.X86_64.cfb8Decrypt_framed
      spSafe := cfb8Decrypt_codeSp }
    .sse [(0, 1)] cfb8DecryptOut (RScrub.pubOk_nil _) (by taint_decide)

theorem cfb8Decrypt_spSafe : Impl.TripleDes.X86_64.Fn.cfb8Decrypt.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cfb8Decrypt_codeSp

theorem ofb_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.ofb).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.TripleDes.ofbApi`'s function as emitted (`Impl.TripleDes.X86_64.Fn.ofb`) meets its contract in
constant time and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed target Impl.TripleDes.X86_64.Fn.ofb (Spec.TripleDes.ofbApi.contract X86_64.abi 984) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.ofbApi)
    { code := ofbCode
      stack := 984
      verified := Proof.TripleDes.X86_64.ofb_framed
      spSafe := ofb_codeSp }
    .sse [(0, 1)] ofbOut (RScrub.pubOk_nil _) (by taint_decide)

theorem ofb_spSafe : Impl.TripleDes.X86_64.Fn.ofb.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ofb_codeSp

theorem ofbFinal_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.ofbFinal).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.TripleDes.ofbFinalApi`'s function as emitted (`Impl.TripleDes.X86_64.Fn.ofbFinal`) meets its contract in
constant time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed target Impl.TripleDes.X86_64.Fn.ofbFinal (Spec.TripleDes.ofbFinalApi.contract X86_64.abi 984) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.ofbFinalApi)
    { code := ofbFinalCode
      stack := 984
      verified := Proof.TripleDes.X86_64.ofbFinal_framed
      spSafe := ofbFinal_codeSp }
    .sse [(0, 1)] ofbFinalOut (RScrub.pubOk_nil _) (by taint_decide)

theorem ofbFinal_spSafe : Impl.TripleDes.X86_64.Fn.ofbFinal.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ofbFinal_codeSp

/-- `Spec.TripleDes.ecbEncryptApi`'s function as emitted (`Impl.TripleDes.X86_64.Fn.ecbEncryptAvx512`) meets its contract in
constant time and returns without secret residue. -/
theorem ecbEncryptAvx512_scrubbed :
    VerifiedScrubbed target Impl.TripleDes.X86_64.Fn.ecbEncryptAvx512 (Spec.TripleDes.ecbEncryptApi.contract X86_64.abi 1040) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.ecbEncryptApi)
    { code := ecbEncryptAvx512Code
      stack := 1040
      verified := Batch.avx512.verified .encrypt
      suffix := "_avx512"
      spSafe := Proof.TripleDes.X86_64.ecb_spSafe (EcbCall.avx512_sp .encrypt) }
    .avx [(8, 1)] (ecbOut .encrypt) (RScrub.pubOk_nil _) (by taint_decide)

theorem ecbEncryptAvx512_spSafe : Impl.TripleDes.X86_64.Fn.ecbEncryptAvx512.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.TripleDes.X86_64.ecb_spSafe (EcbCall.avx512_sp .encrypt))

/-- `Spec.TripleDes.ecbEncryptApi`'s function as emitted (`Impl.TripleDes.X86_64.Fn.ecbEncryptAvx2`) meets its contract in
constant time and returns without secret residue. -/
theorem ecbEncryptAvx2_scrubbed :
    VerifiedScrubbed target Impl.TripleDes.X86_64.Fn.ecbEncryptAvx2 (Spec.TripleDes.ecbEncryptApi.contract X86_64.abi 1040) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.ecbEncryptApi)
    { code := ecbEncryptAvx2Code
      stack := 1040
      verified := Batch.avx2.verified .encrypt
      suffix := "_avx2"
      spSafe := Proof.TripleDes.X86_64.ecb_spSafe (EcbCall.avx2_sp .encrypt) }
    .avx [(8, 1)] (ecbOut .encrypt) (RScrub.pubOk_nil _) (by taint_decide)

theorem ecbEncryptAvx2_spSafe : Impl.TripleDes.X86_64.Fn.ecbEncryptAvx2.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.TripleDes.X86_64.ecb_spSafe (EcbCall.avx2_sp .encrypt))

/-- `Spec.TripleDes.ecbEncryptApi`'s function as emitted (`Impl.TripleDes.X86_64.Fn.ecbEncryptSse`) meets its contract in
constant time and returns without secret residue. -/
theorem ecbEncryptSse_scrubbed :
    VerifiedScrubbed target Impl.TripleDes.X86_64.Fn.ecbEncryptSse (Spec.TripleDes.ecbEncryptApi.contract X86_64.abi 1040) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.ecbEncryptApi)
    { code := ecbEncryptSseCode
      stack := 1040
      verified := Batch.sse.verified .encrypt
      suffix := ""
      spSafe := Proof.TripleDes.X86_64.ecb_spSafe (EcbCall.sse_sp .encrypt) }
    .sse [(8, 1)] (ecbOut .encrypt) (RScrub.pubOk_nil _) (by taint_decide)

theorem ecbEncryptSse_spSafe : Impl.TripleDes.X86_64.Fn.ecbEncryptSse.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.TripleDes.X86_64.ecb_spSafe (EcbCall.sse_sp .encrypt))

/-- `Spec.TripleDes.ecbDecryptApi`'s function as emitted (`Impl.TripleDes.X86_64.Fn.ecbDecryptAvx512`) meets its contract in
constant time and returns without secret residue. -/
theorem ecbDecryptAvx512_scrubbed :
    VerifiedScrubbed target Impl.TripleDes.X86_64.Fn.ecbDecryptAvx512 (Spec.TripleDes.ecbDecryptApi.contract X86_64.abi 1040) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.ecbDecryptApi)
    { code := ecbDecryptAvx512Code
      stack := 1040
      verified := Batch.avx512.verified .decrypt
      suffix := "_avx512"
      spSafe := Proof.TripleDes.X86_64.ecb_spSafe (EcbCall.avx512_sp .decrypt) }
    .avx [(8, 1)] (ecbOut .decrypt) (RScrub.pubOk_nil _) (by taint_decide)

theorem ecbDecryptAvx512_spSafe : Impl.TripleDes.X86_64.Fn.ecbDecryptAvx512.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.TripleDes.X86_64.ecb_spSafe (EcbCall.avx512_sp .decrypt))

/-- `Spec.TripleDes.ecbDecryptApi`'s function as emitted (`Impl.TripleDes.X86_64.Fn.ecbDecryptAvx2`) meets its contract in
constant time and returns without secret residue. -/
theorem ecbDecryptAvx2_scrubbed :
    VerifiedScrubbed target Impl.TripleDes.X86_64.Fn.ecbDecryptAvx2 (Spec.TripleDes.ecbDecryptApi.contract X86_64.abi 1040) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.ecbDecryptApi)
    { code := ecbDecryptAvx2Code
      stack := 1040
      verified := Batch.avx2.verified .decrypt
      suffix := "_avx2"
      spSafe := Proof.TripleDes.X86_64.ecb_spSafe (EcbCall.avx2_sp .decrypt) }
    .avx [(8, 1)] (ecbOut .decrypt) (RScrub.pubOk_nil _) (by taint_decide)

theorem ecbDecryptAvx2_spSafe : Impl.TripleDes.X86_64.Fn.ecbDecryptAvx2.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.TripleDes.X86_64.ecb_spSafe (EcbCall.avx2_sp .decrypt))

/-- `Spec.TripleDes.ecbDecryptApi`'s function as emitted (`Impl.TripleDes.X86_64.Fn.ecbDecryptSse`) meets its contract in
constant time and returns without secret residue. -/
theorem ecbDecryptSse_scrubbed :
    VerifiedScrubbed target Impl.TripleDes.X86_64.Fn.ecbDecryptSse (Spec.TripleDes.ecbDecryptApi.contract X86_64.abi 1040) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.ecbDecryptApi)
    { code := ecbDecryptSseCode
      stack := 1040
      verified := Batch.sse.verified .decrypt
      suffix := ""
      spSafe := Proof.TripleDes.X86_64.ecb_spSafe (EcbCall.sse_sp .decrypt) }
    .sse [(8, 1)] (ecbOut .decrypt) (RScrub.pubOk_nil _) (by taint_decide)

theorem ecbDecryptSse_spSafe : Impl.TripleDes.X86_64.Fn.ecbDecryptSse.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.TripleDes.X86_64.ecb_spSafe (EcbCall.sse_sp .decrypt))
end VG.Proof.TripleDes.X86_64.Scrub
