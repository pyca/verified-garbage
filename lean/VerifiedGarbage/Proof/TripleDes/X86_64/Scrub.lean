module

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

def expandKeyKs : List Nat := keep_for% Spec.TripleDes.expandKeyApi.sig 520 expandKeyCode []

theorem expandKeyOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.TripleDes.expandKeyApi.sig 520 []) expandKeyCode
      h).any (RScrub.resOkB · 520 expandKeyKs (Impl.Scrub.X86_64.chunks 520)) = true :=
  RScrub.Analysed.ok_of expandKeyKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_triple_des_expand_key`. -/
def expandKeyReg : Registration Spec.TripleDes.expandKeyApi X86_64.target :=
  withScrub {
    code := expandKeyCode
    stack := 520
    verified := Proof.TripleDes.X86_64.expandKey_framed } expandKeyOut [] (pubOk_nil _) (some ⟨expandKeyKs, expandKeyOk⟩)

/-- `vg_triple_des_cbc_encrypt_chained`'s code. -/
abbrev cbcEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cbcEncryptChained

def cbcEncryptKs : List Nat := keep_for% Spec.TripleDes.cbcEncryptChainedApi.sig 984 cbcEncryptCode []

theorem cbcEncryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.TripleDes.cbcEncryptChainedApi.sig 984 []) cbcEncryptCode
      h).any (RScrub.resOkB · 984 cbcEncryptKs (Impl.Scrub.X86_64.chunks 984)) = true :=
  RScrub.Analysed.ok_of cbcEncryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_triple_des_cbc_encrypt_chained`. -/
def cbcEncryptReg : Registration Spec.TripleDes.cbcEncryptChainedApi X86_64.target :=
  withScrub {
    code := cbcEncryptCode
    stack := 984
    verified := Proof.TripleDes.X86_64.cbcEncryptChained_framed } cbcEncryptOut [] (pubOk_nil _) (some ⟨cbcEncryptKs, cbcEncryptOk⟩)

/-- `vg_triple_des_cfb64_encrypt`'s code. -/
abbrev cfbEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfbEncrypt

def cfbEncryptKs : List Nat := keep_for% Spec.TripleDes.cfbEncryptApi.sig 984 cfbEncryptCode []

theorem cfbEncryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.TripleDes.cfbEncryptApi.sig 984 []) cfbEncryptCode
      h).any (RScrub.resOkB · 984 cfbEncryptKs (Impl.Scrub.X86_64.chunks 984)) = true :=
  RScrub.Analysed.ok_of cfbEncryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_triple_des_cfb64_encrypt`. -/
def cfbEncryptReg : Registration Spec.TripleDes.cfbEncryptApi X86_64.target :=
  withScrub {
    code := cfbEncryptCode
    stack := 984
    verified := Proof.TripleDes.X86_64.cfbEncrypt_framed } cfbEncryptOut [] (pubOk_nil _) (some ⟨cfbEncryptKs, cfbEncryptOk⟩)

/-- `vg_triple_des_cfb64_encrypt_final`'s code. -/
abbrev cfbEncryptFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfbEncryptFinal

def cfbEncryptFinalKs : List Nat := keep_for% Spec.TripleDes.cfbEncryptFinalApi.sig 984 cfbEncryptFinalCode []

theorem cfbEncryptFinalOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.TripleDes.cfbEncryptFinalApi.sig 984 []) cfbEncryptFinalCode
      h).any (RScrub.resOkB · 984 cfbEncryptFinalKs (Impl.Scrub.X86_64.chunks 984)) = true :=
  RScrub.Analysed.ok_of cfbEncryptFinalKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_triple_des_cfb64_encrypt_final`. -/
def cfbEncryptFinalReg : Registration Spec.TripleDes.cfbEncryptFinalApi X86_64.target :=
  withScrub {
    code := cfbEncryptFinalCode
    stack := 984
    verified := Proof.TripleDes.X86_64.cfbEncryptFinal_framed } cfbEncryptFinalOut [] (pubOk_nil _) (some ⟨cfbEncryptFinalKs, cfbEncryptFinalOk⟩)

/-- `vg_triple_des_cfb64_decrypt_final`'s code. -/
abbrev cfbDecryptFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfbDecryptFinal

def cfbDecryptFinalKs : List Nat := keep_for% Spec.TripleDes.cfbDecryptFinalApi.sig 984 cfbDecryptFinalCode []

theorem cfbDecryptFinalOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.TripleDes.cfbDecryptFinalApi.sig 984 []) cfbDecryptFinalCode
      h).any (RScrub.resOkB · 984 cfbDecryptFinalKs (Impl.Scrub.X86_64.chunks 984)) = true :=
  RScrub.Analysed.ok_of cfbDecryptFinalKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_triple_des_cfb64_decrypt_final`. -/
def cfbDecryptFinalReg : Registration Spec.TripleDes.cfbDecryptFinalApi X86_64.target :=
  withScrub {
    code := cfbDecryptFinalCode
    stack := 984
    verified := Proof.TripleDes.X86_64.cfbDecryptFinal_framed } cfbDecryptFinalOut [] (pubOk_nil _) (some ⟨cfbDecryptFinalKs, cfbDecryptFinalOk⟩)

/-- `vg_triple_des_cfb8_encrypt`'s code. -/
abbrev cfb8EncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfb8Encrypt

def cfb8EncryptKs : List Nat := keep_for% Spec.TripleDes.cfb8EncryptApi.sig 984 cfb8EncryptCode []

theorem cfb8EncryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.TripleDes.cfb8EncryptApi.sig 984 []) cfb8EncryptCode
      h).any (RScrub.resOkB · 984 cfb8EncryptKs (Impl.Scrub.X86_64.chunks 984)) = true :=
  RScrub.Analysed.ok_of cfb8EncryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_triple_des_cfb8_encrypt`. -/
def cfb8EncryptReg : Registration Spec.TripleDes.cfb8EncryptApi X86_64.target :=
  withScrub {
    code := cfb8EncryptCode
    stack := 984
    verified := Proof.TripleDes.X86_64.cfb8Encrypt_framed } cfb8EncryptOut [] (pubOk_nil _) (some ⟨cfb8EncryptKs, cfb8EncryptOk⟩)

/-- `vg_triple_des_cfb8_decrypt`'s code. -/
abbrev cfb8DecryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfb8Decrypt

def cfb8DecryptKs : List Nat := keep_for% Spec.TripleDes.cfb8DecryptApi.sig 984 cfb8DecryptCode []

theorem cfb8DecryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.TripleDes.cfb8DecryptApi.sig 984 []) cfb8DecryptCode
      h).any (RScrub.resOkB · 984 cfb8DecryptKs (Impl.Scrub.X86_64.chunks 984)) = true :=
  RScrub.Analysed.ok_of cfb8DecryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_triple_des_cfb8_decrypt`. -/
def cfb8DecryptReg : Registration Spec.TripleDes.cfb8DecryptApi X86_64.target :=
  withScrub {
    code := cfb8DecryptCode
    stack := 984
    verified := Proof.TripleDes.X86_64.cfb8Decrypt_framed } cfb8DecryptOut [] (pubOk_nil _) (some ⟨cfb8DecryptKs, cfb8DecryptOk⟩)

/-- `vg_triple_des_ofb`'s code. -/
abbrev ofbCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.ofb

def ofbKs : List Nat := keep_for% Spec.TripleDes.ofbApi.sig 984 ofbCode []

theorem ofbOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.TripleDes.ofbApi.sig 984 []) ofbCode
      h).any (RScrub.resOkB · 984 ofbKs (Impl.Scrub.X86_64.chunks 984)) = true :=
  RScrub.Analysed.ok_of ofbKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_triple_des_ofb`. -/
def ofbReg : Registration Spec.TripleDes.ofbApi X86_64.target :=
  withScrub {
    code := ofbCode
    stack := 984
    verified := Proof.TripleDes.X86_64.ofb_framed } ofbOut [] (pubOk_nil _) (some ⟨ofbKs, ofbOk⟩)

/-- `vg_triple_des_ofb_final`'s code. -/
abbrev ofbFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.ofbFinal

def ofbFinalKs : List Nat := keep_for% Spec.TripleDes.ofbFinalApi.sig 984 ofbFinalCode []

theorem ofbFinalOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.TripleDes.ofbFinalApi.sig 984 []) ofbFinalCode
      h).any (RScrub.resOkB · 984 ofbFinalKs (Impl.Scrub.X86_64.chunks 984)) = true :=
  RScrub.Analysed.ok_of ofbFinalKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_triple_des_ofb_final`. -/
def ofbFinalReg : Registration Spec.TripleDes.ofbFinalApi X86_64.target :=
  withScrub {
    code := ofbFinalCode
    stack := 984
    verified := Proof.TripleDes.X86_64.ofbFinal_framed } ofbFinalOut [] (pubOk_nil _) (some ⟨ofbFinalKs, ofbFinalOk⟩)

/-- `vg_triple_des_ecb_encrypt_avx512`'s code. -/
abbrev ecbEncryptAvx512Code : Prog isa := Batch.avx512.code .encrypt

def ecbEncryptAvx512Ks : List Nat := keep_for% Spec.TripleDes.ecbEncryptApi.sig 1040 ecbEncryptAvx512Code []

theorem ecbEncryptAvx512Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.TripleDes.ecbEncryptApi.sig 1040 []) ecbEncryptAvx512Code
      h).any (RScrub.resOkB · 1040 ecbEncryptAvx512Ks (Impl.Scrub.X86_64.chunks 1040)) = true :=
  RScrub.Analysed.ok_of ecbEncryptAvx512Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_triple_des_ecb_encrypt_avx512`. -/
def ecbEncryptAvx512Reg : Registration Spec.TripleDes.ecbEncryptApi X86_64.target :=
  withScrub {
    suffix := "_avx512"
    code := ecbEncryptAvx512Code
    stack := 1040
    verified := Batch.avx512.verified .encrypt
    spSafe := Proof.TripleDes.X86_64.ecb_spSafe (EcbCall.avx512_sp .encrypt) } (ecbOut .encrypt) [] (pubOk_nil _)
    (some ⟨ecbEncryptAvx512Ks, ecbEncryptAvx512Ok⟩)

/-- `vg_triple_des_ecb_encrypt_avx2`'s code. -/
abbrev ecbEncryptAvx2Code : Prog isa := Batch.avx2.code .encrypt

def ecbEncryptAvx2Ks : List Nat := keep_for% Spec.TripleDes.ecbEncryptApi.sig 1040 ecbEncryptAvx2Code []

theorem ecbEncryptAvx2Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.TripleDes.ecbEncryptApi.sig 1040 []) ecbEncryptAvx2Code
      h).any (RScrub.resOkB · 1040 ecbEncryptAvx2Ks (Impl.Scrub.X86_64.chunks 1040)) = true :=
  RScrub.Analysed.ok_of ecbEncryptAvx2Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_triple_des_ecb_encrypt_avx2`. -/
def ecbEncryptAvx2Reg : Registration Spec.TripleDes.ecbEncryptApi X86_64.target :=
  withScrub {
    suffix := "_avx2"
    code := ecbEncryptAvx2Code
    stack := 1040
    verified := Batch.avx2.verified .encrypt
    spSafe := Proof.TripleDes.X86_64.ecb_spSafe (EcbCall.avx2_sp .encrypt) } (ecbOut .encrypt) [] (pubOk_nil _)
    (some ⟨ecbEncryptAvx2Ks, ecbEncryptAvx2Ok⟩)

/-- `vg_triple_des_ecb_encrypt`'s code. -/
abbrev ecbEncryptSseCode : Prog isa := Batch.sse.code .encrypt

def ecbEncryptSseKs : List Nat := keep_for% Spec.TripleDes.ecbEncryptApi.sig 1040 ecbEncryptSseCode []

theorem ecbEncryptSseOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.TripleDes.ecbEncryptApi.sig 1040 []) ecbEncryptSseCode
      h).any (RScrub.resOkB · 1040 ecbEncryptSseKs (Impl.Scrub.X86_64.chunks 1040)) = true :=
  RScrub.Analysed.ok_of ecbEncryptSseKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_triple_des_ecb_encrypt`. -/
def ecbEncryptSseReg : Registration Spec.TripleDes.ecbEncryptApi X86_64.target :=
  withScrub {
    suffix := ""
    code := ecbEncryptSseCode
    stack := 1040
    verified := Batch.sse.verified .encrypt
    spSafe := Proof.TripleDes.X86_64.ecb_spSafe (EcbCall.sse_sp .encrypt) } (ecbOut .encrypt) [] (pubOk_nil _)
    (some ⟨ecbEncryptSseKs, ecbEncryptSseOk⟩)

/-- `vg_triple_des_ecb_decrypt_avx512`'s code. -/
abbrev ecbDecryptAvx512Code : Prog isa := Batch.avx512.code .decrypt

def ecbDecryptAvx512Ks : List Nat := keep_for% Spec.TripleDes.ecbDecryptApi.sig 1040 ecbDecryptAvx512Code []

theorem ecbDecryptAvx512Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.TripleDes.ecbDecryptApi.sig 1040 []) ecbDecryptAvx512Code
      h).any (RScrub.resOkB · 1040 ecbDecryptAvx512Ks (Impl.Scrub.X86_64.chunks 1040)) = true :=
  RScrub.Analysed.ok_of ecbDecryptAvx512Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_triple_des_ecb_decrypt_avx512`. -/
def ecbDecryptAvx512Reg : Registration Spec.TripleDes.ecbDecryptApi X86_64.target :=
  withScrub {
    suffix := "_avx512"
    code := ecbDecryptAvx512Code
    stack := 1040
    verified := Batch.avx512.verified .decrypt
    spSafe := Proof.TripleDes.X86_64.ecb_spSafe (EcbCall.avx512_sp .decrypt) } (ecbOut .decrypt) [] (pubOk_nil _)
    (some ⟨ecbDecryptAvx512Ks, ecbDecryptAvx512Ok⟩)

/-- `vg_triple_des_ecb_decrypt_avx2`'s code. -/
abbrev ecbDecryptAvx2Code : Prog isa := Batch.avx2.code .decrypt

def ecbDecryptAvx2Ks : List Nat := keep_for% Spec.TripleDes.ecbDecryptApi.sig 1040 ecbDecryptAvx2Code []

theorem ecbDecryptAvx2Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.TripleDes.ecbDecryptApi.sig 1040 []) ecbDecryptAvx2Code
      h).any (RScrub.resOkB · 1040 ecbDecryptAvx2Ks (Impl.Scrub.X86_64.chunks 1040)) = true :=
  RScrub.Analysed.ok_of ecbDecryptAvx2Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_triple_des_ecb_decrypt_avx2`. -/
def ecbDecryptAvx2Reg : Registration Spec.TripleDes.ecbDecryptApi X86_64.target :=
  withScrub {
    suffix := "_avx2"
    code := ecbDecryptAvx2Code
    stack := 1040
    verified := Batch.avx2.verified .decrypt
    spSafe := Proof.TripleDes.X86_64.ecb_spSafe (EcbCall.avx2_sp .decrypt) } (ecbOut .decrypt) [] (pubOk_nil _)
    (some ⟨ecbDecryptAvx2Ks, ecbDecryptAvx2Ok⟩)

/-- `vg_triple_des_ecb_decrypt`'s code. -/
abbrev ecbDecryptSseCode : Prog isa := Batch.sse.code .decrypt

def ecbDecryptSseKs : List Nat := keep_for% Spec.TripleDes.ecbDecryptApi.sig 1040 ecbDecryptSseCode []

theorem ecbDecryptSseOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.TripleDes.ecbDecryptApi.sig 1040 []) ecbDecryptSseCode
      h).any (RScrub.resOkB · 1040 ecbDecryptSseKs (Impl.Scrub.X86_64.chunks 1040)) = true :=
  RScrub.Analysed.ok_of ecbDecryptSseKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_triple_des_ecb_decrypt`. -/
def ecbDecryptSseReg : Registration Spec.TripleDes.ecbDecryptApi X86_64.target :=
  withScrub {
    suffix := ""
    code := ecbDecryptSseCode
    stack := 1040
    verified := Batch.sse.verified .decrypt
    spSafe := Proof.TripleDes.X86_64.ecb_spSafe (EcbCall.sse_sp .decrypt) } (ecbOut .decrypt) [] (pubOk_nil _)
    (some ⟨ecbDecryptSseKs, ecbDecryptSseOk⟩)

end VG.Proof.TripleDes.X86_64.Scrub
