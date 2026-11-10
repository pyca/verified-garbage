module

public import VerifiedGarbage.Spec.Sm4.Contract
public import VerifiedGarbage.Spec.Sm4.Cbc
public import VerifiedGarbage.Spec.Sm4.Cfb
public import VerifiedGarbage.Spec.Sm4.CfbFinal
public import VerifiedGarbage.Spec.Sm4.Ofb
public import VerifiedGarbage.Spec.Sm4.OfbFinal
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sm4.X86_64.Verified
public import VerifiedGarbage.Proof.Sm4.X86_64.CbcVerified
public import VerifiedGarbage.Proof.Sm4.X86_64.FbVerified
public import VerifiedGarbage.Proof.Sm4.X86_64.FbFinalVerified
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
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Sm4.X86_64.Verified
meta import VerifiedGarbage.Proof.Sm4.X86_64.CbcVerified
meta import VerifiedGarbage.Proof.Sm4.X86_64.FbVerified
meta import VerifiedGarbage.Proof.Sm4.X86_64.FbFinalVerified
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Sm4.CbcScratch
meta import VerifiedGarbage.Proof.Sm4.FbScratch
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Proof.Sm4.X86_64.Lit
meta import VerifiedGarbage.Proof.Sm4.X86_64.ModesLit
meta import VerifiedGarbage.Proof.Sm4.X86_64.FbFinalLit

/-!
# SM4 on x86-64, without secret residue

The ECB, CBC, CFB128 and OFB functions, each followed by
`Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`), which clears the
registers and the granules of its stack that the residue analysis
(`X86_64.RTaint`) finds may hold secrets. Their postconditions read the
memory on return only within the buffers (`X86_64.Scrub.PostOut`), as the
frames that keep their working space on the stack already show
(`X86_64.Verified.stackScratchWiped`'s `hpost`).

CTR is not here: `vg_sm4_ctr_final` calls `vg_sm4_ctr` by name with its code
as it is, and the analysis of `vg_sm4_ctr_final` does not succeed. Nor is key
expansion: SM4-GCM calls `vg_sm4_expand_key` by name with its code as it is.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub

/-! ## Postconditions -/

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

/-! ## The registrations -/

/-- `vg_sm4_ecb_encrypt`'s code. -/
abbrev ecbEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3144 .rcx 392 (Impl.Sm4.X86_64.ecb .encrypt)

def ecbEncryptKs : List Nat := keep_for% Spec.Sm4.ecbEncryptApi.sig 3144 ecbEncryptCode []

theorem ecbEncryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sm4.ecbEncryptApi.sig 3144 []) ecbEncryptCode
      h).any (RScrub.resOkB · 3144 ecbEncryptKs (Impl.Scrub.X86_64.chunks 3144)) = true :=
  RScrub.Analysed.ok_of ecbEncryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_sm4_ecb_encrypt`. -/
def ecbEncryptReg : Registration Spec.Sm4.ecbEncryptApi X86_64.target :=
  withScrub {
    code := ecbEncryptCode
    stack := 3144
    verified := Proof.Sm4.X86_64.ecb_framed .encrypt } ecbEncryptOut [] (pubOk_nil _) (some ⟨ecbEncryptKs, ecbEncryptOk⟩)

/-- `vg_sm4_ecb_decrypt`'s code. -/
abbrev ecbDecryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3144 .rcx 392 (Impl.Sm4.X86_64.ecb .decrypt)

def ecbDecryptKs : List Nat := keep_for% Spec.Sm4.ecbDecryptApi.sig 3144 ecbDecryptCode []

theorem ecbDecryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sm4.ecbDecryptApi.sig 3144 []) ecbDecryptCode
      h).any (RScrub.resOkB · 3144 ecbDecryptKs (Impl.Scrub.X86_64.chunks 3144)) = true :=
  RScrub.Analysed.ok_of ecbDecryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_sm4_ecb_decrypt`. -/
def ecbDecryptReg : Registration Spec.Sm4.ecbDecryptApi X86_64.target :=
  withScrub {
    code := ecbDecryptCode
    stack := 3144
    verified := Proof.Sm4.X86_64.ecb_framed .decrypt } ecbDecryptOut [] (pubOk_nil _) (some ⟨ecbDecryptKs, ecbDecryptOk⟩)

/-- `vg_sm4_cbc_encrypt_chained`'s code. -/
abbrev cbcEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cbcEncryptChained

def cbcEncryptKs : List Nat := keep_for% Spec.Sm4.cbcEncryptChainedApi.sig 3216 cbcEncryptCode []

theorem cbcEncryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sm4.cbcEncryptChainedApi.sig 3216 []) cbcEncryptCode
      h).any (RScrub.resOkB · 3216 cbcEncryptKs (Impl.Scrub.X86_64.chunks 3216)) = true :=
  RScrub.Analysed.ok_of cbcEncryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_sm4_cbc_encrypt_chained`. -/
def cbcEncryptReg : Registration Spec.Sm4.cbcEncryptChainedApi X86_64.target :=
  withScrub {
    code := cbcEncryptCode
    stack := 3216
    verified := Proof.Sm4.X86_64.cbcEncryptChained_framed } cbcEncryptOut [] (pubOk_nil _) (some ⟨cbcEncryptKs, cbcEncryptOk⟩)

/-- `vg_sm4_cbc_decrypt_chained`'s code. -/
abbrev cbcDecryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cbcDecryptChained

def cbcDecryptKs : List Nat := keep_for% Spec.Sm4.cbcDecryptChainedApi.sig 3216 cbcDecryptCode []

theorem cbcDecryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sm4.cbcDecryptChainedApi.sig 3216 []) cbcDecryptCode
      h).any (RScrub.resOkB · 3216 cbcDecryptKs (Impl.Scrub.X86_64.chunks 3216)) = true :=
  RScrub.Analysed.ok_of cbcDecryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_sm4_cbc_decrypt_chained`. -/
def cbcDecryptReg : Registration Spec.Sm4.cbcDecryptChainedApi X86_64.target :=
  withScrub {
    code := cbcDecryptCode
    stack := 3216
    verified := Proof.Sm4.X86_64.cbcDecryptChained_framed } cbcDecryptOut [] (pubOk_nil _) (some ⟨cbcDecryptKs, cbcDecryptOk⟩)

/-- `vg_sm4_cfb128_encrypt`'s code. -/
abbrev cfbEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cfbEncrypt

def cfbEncryptKs : List Nat := keep_for% Spec.Sm4.cfbEncryptApi.sig 3216 cfbEncryptCode []

theorem cfbEncryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sm4.cfbEncryptApi.sig 3216 []) cfbEncryptCode
      h).any (RScrub.resOkB · 3216 cfbEncryptKs (Impl.Scrub.X86_64.chunks 3216)) = true :=
  RScrub.Analysed.ok_of cfbEncryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_sm4_cfb128_encrypt`. -/
def cfbEncryptReg : Registration Spec.Sm4.cfbEncryptApi X86_64.target :=
  withScrub {
    code := cfbEncryptCode
    stack := 3216
    verified := Proof.Sm4.X86_64.cfbEncrypt_framed } cfbEncryptOut [] (pubOk_nil _) (some ⟨cfbEncryptKs, cfbEncryptOk⟩)

/-- `vg_sm4_cfb128_encrypt_final`'s code. -/
abbrev cfbEncryptFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cfbEncryptFinal

def cfbEncryptFinalKs : List Nat := keep_for% Spec.Sm4.cfbEncryptFinalApi.sig 3216 cfbEncryptFinalCode []

theorem cfbEncryptFinalOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sm4.cfbEncryptFinalApi.sig 3216 []) cfbEncryptFinalCode
      h).any (RScrub.resOkB · 3216 cfbEncryptFinalKs (Impl.Scrub.X86_64.chunks 3216)) = true :=
  RScrub.Analysed.ok_of cfbEncryptFinalKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_sm4_cfb128_encrypt_final`. -/
def cfbEncryptFinalReg : Registration Spec.Sm4.cfbEncryptFinalApi X86_64.target :=
  withScrub {
    code := cfbEncryptFinalCode
    stack := 3216
    verified := Proof.Sm4.X86_64.cfbEncryptFinal_framed } cfbEncryptFinalOut [] (pubOk_nil _) (some ⟨cfbEncryptFinalKs, cfbEncryptFinalOk⟩)

/-- `vg_sm4_cfb128_decrypt`'s code. -/
abbrev cfbDecryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cfbDecrypt

def cfbDecryptKs : List Nat := keep_for% Spec.Sm4.cfbDecryptApi.sig 3216 cfbDecryptCode []

theorem cfbDecryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sm4.cfbDecryptApi.sig 3216 []) cfbDecryptCode
      h).any (RScrub.resOkB · 3216 cfbDecryptKs (Impl.Scrub.X86_64.chunks 3216)) = true :=
  RScrub.Analysed.ok_of cfbDecryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_sm4_cfb128_decrypt`. -/
def cfbDecryptReg : Registration Spec.Sm4.cfbDecryptApi X86_64.target :=
  withScrub {
    code := cfbDecryptCode
    stack := 3216
    verified := Proof.Sm4.X86_64.cfbDecrypt_framed } cfbDecryptOut [] (pubOk_nil _) (some ⟨cfbDecryptKs, cfbDecryptOk⟩)

/-- `vg_sm4_cfb128_decrypt_final`'s code. -/
abbrev cfbDecryptFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cfbDecryptFinal

def cfbDecryptFinalKs : List Nat := keep_for% Spec.Sm4.cfbDecryptFinalApi.sig 3216 cfbDecryptFinalCode []

theorem cfbDecryptFinalOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sm4.cfbDecryptFinalApi.sig 3216 []) cfbDecryptFinalCode
      h).any (RScrub.resOkB · 3216 cfbDecryptFinalKs (Impl.Scrub.X86_64.chunks 3216)) = true :=
  RScrub.Analysed.ok_of cfbDecryptFinalKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_sm4_cfb128_decrypt_final`. -/
def cfbDecryptFinalReg : Registration Spec.Sm4.cfbDecryptFinalApi X86_64.target :=
  withScrub {
    code := cfbDecryptFinalCode
    stack := 3216
    verified := Proof.Sm4.X86_64.cfbDecryptFinal_framed } cfbDecryptFinalOut [] (pubOk_nil _) (some ⟨cfbDecryptFinalKs, cfbDecryptFinalOk⟩)

/-- `vg_sm4_ofb`'s code. -/
abbrev ofbCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.ofb

def ofbKs : List Nat := keep_for% Spec.Sm4.ofbApi.sig 3216 ofbCode []

theorem ofbOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sm4.ofbApi.sig 3216 []) ofbCode
      h).any (RScrub.resOkB · 3216 ofbKs (Impl.Scrub.X86_64.chunks 3216)) = true :=
  RScrub.Analysed.ok_of ofbKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_sm4_ofb`. -/
def ofbReg : Registration Spec.Sm4.ofbApi X86_64.target :=
  withScrub {
    code := ofbCode
    stack := 3216
    verified := Proof.Sm4.X86_64.ofb_framed } ofbOut [] (pubOk_nil _) (some ⟨ofbKs, ofbOk⟩)

/-- `vg_sm4_ofb_final`'s code. -/
abbrev ofbFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.ofbFinal

def ofbFinalKs : List Nat := keep_for% Spec.Sm4.ofbFinalApi.sig 3216 ofbFinalCode []

theorem ofbFinalOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sm4.ofbFinalApi.sig 3216 []) ofbFinalCode
      h).any (RScrub.resOkB · 3216 ofbFinalKs (Impl.Scrub.X86_64.chunks 3216)) = true :=
  RScrub.Analysed.ok_of ofbFinalKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_sm4_ofb_final`. -/
def ofbFinalReg : Registration Spec.Sm4.ofbFinalApi X86_64.target :=
  withScrub {
    code := ofbFinalCode
    stack := 3216
    verified := Proof.Sm4.X86_64.ofbFinal_framed } ofbFinalOut [] (pubOk_nil _) (some ⟨ofbFinalKs, ofbFinalOk⟩)

end VG.Proof.Sm4.X86_64.Scrub

