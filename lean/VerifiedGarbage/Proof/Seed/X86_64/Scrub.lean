module

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
public import VerifiedGarbage.Proof.Seed.X86_64.EcbCall
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
meta import VerifiedGarbage.Proof.Seed.X86_64.EcbCall
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

def expandKeyKs : List Nat := keep_for% Spec.Seed.expandKeyApi.sig 1064 expandKeyCode []

theorem expandKeyOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Seed.expandKeyApi.sig 1064 []) expandKeyCode
      h).any (RScrub.resOkB · 1064 expandKeyKs (Impl.Scrub.X86_64.chunks 1064)) = true :=
  RScrub.Analysed.ok_of expandKeyKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_seed_expand_key`. -/
def expandKeyReg : Registration Spec.Seed.expandKeyApi X86_64.target :=
  withScrub {
    code := expandKeyCode
    stack := 1064
    verified := Proof.Seed.X86_64.expandKey_framed } expandKeyOut [] (pubOk_nil _) (some ⟨expandKeyKs, expandKeyOk⟩)

/-- `vg_seed_ecb_encrypt`'s code. -/
abbrev ecbEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 1096 .rcx 136 (Impl.Seed.X86_64.ecbCall .encrypt)

def ecbEncryptKs : List Nat := keep_for% Spec.Seed.ecbEncryptApi.sig 1104 ecbEncryptCode []

theorem ecbEncryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Seed.ecbEncryptApi.sig 1104 []) ecbEncryptCode
      h).any (RScrub.resOkB · 1104 ecbEncryptKs (Impl.Scrub.X86_64.chunks 1104)) = true :=
  RScrub.Analysed.ok_of ecbEncryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_seed_ecb_encrypt`. -/
def ecbEncryptReg : Registration Spec.Seed.ecbEncryptApi X86_64.target :=
  withScrub {
    code := ecbEncryptCode
    stack := 1104
    verified := Proof.Seed.X86_64.ecbCall_framed .encrypt } ecbEncryptOut [] (pubOk_nil _) (some ⟨ecbEncryptKs, ecbEncryptOk⟩)

/-- `vg_seed_ecb_decrypt`'s code. -/
abbrev ecbDecryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 1096 .rcx 136 (Impl.Seed.X86_64.ecbCall .decrypt)

def ecbDecryptKs : List Nat := keep_for% Spec.Seed.ecbDecryptApi.sig 1104 ecbDecryptCode []

theorem ecbDecryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Seed.ecbDecryptApi.sig 1104 []) ecbDecryptCode
      h).any (RScrub.resOkB · 1104 ecbDecryptKs (Impl.Scrub.X86_64.chunks 1104)) = true :=
  RScrub.Analysed.ok_of ecbDecryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_seed_ecb_decrypt`. -/
def ecbDecryptReg : Registration Spec.Seed.ecbDecryptApi X86_64.target :=
  withScrub {
    code := ecbDecryptCode
    stack := 1104
    verified := Proof.Seed.X86_64.ecbCall_framed .decrypt } ecbDecryptOut [] (pubOk_nil _) (some ⟨ecbDecryptKs, ecbDecryptOk⟩)

/-- `vg_seed_cbc_encrypt_chained`'s code. -/
abbrev cbcEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cbcEncryptChained

def cbcEncryptKs : List Nat := keep_for% Spec.Seed.cbcEncryptChainedApi.sig 1552 cbcEncryptCode []

theorem cbcEncryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Seed.cbcEncryptChainedApi.sig 1552 []) cbcEncryptCode
      h).any (RScrub.resOkB · 1552 cbcEncryptKs (Impl.Scrub.X86_64.chunks 1552)) = true :=
  RScrub.Analysed.ok_of cbcEncryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_seed_cbc_encrypt_chained`. -/
def cbcEncryptReg : Registration Spec.Seed.cbcEncryptChainedApi X86_64.target :=
  withScrub {
    code := cbcEncryptCode
    stack := 1552
    verified := Proof.Seed.X86_64.cbcEncryptChained_framed } cbcEncryptOut [] (pubOk_nil _) (some ⟨cbcEncryptKs, cbcEncryptOk⟩)

/-- `vg_seed_cbc_decrypt_chained`'s code. -/
abbrev cbcDecryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cbcDecryptChained

def cbcDecryptKs : List Nat := keep_for% Spec.Seed.cbcDecryptChainedApi.sig 1552 cbcDecryptCode []

theorem cbcDecryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Seed.cbcDecryptChainedApi.sig 1552 []) cbcDecryptCode
      h).any (RScrub.resOkB · 1552 cbcDecryptKs (Impl.Scrub.X86_64.chunks 1552)) = true :=
  RScrub.Analysed.ok_of cbcDecryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_seed_cbc_decrypt_chained`. -/
def cbcDecryptReg : Registration Spec.Seed.cbcDecryptChainedApi X86_64.target :=
  withScrub {
    code := cbcDecryptCode
    stack := 1552
    verified := Proof.Seed.X86_64.cbcDecryptChained_framed } cbcDecryptOut [] (pubOk_nil _) (some ⟨cbcDecryptKs, cbcDecryptOk⟩)

/-- `vg_seed_cfb128_encrypt`'s code. -/
abbrev cfbEncryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cfbEncrypt

def cfbEncryptKs : List Nat := keep_for% Spec.Seed.cfbEncryptApi.sig 1552 cfbEncryptCode []

theorem cfbEncryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Seed.cfbEncryptApi.sig 1552 []) cfbEncryptCode
      h).any (RScrub.resOkB · 1552 cfbEncryptKs (Impl.Scrub.X86_64.chunks 1552)) = true :=
  RScrub.Analysed.ok_of cfbEncryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_seed_cfb128_encrypt`. -/
def cfbEncryptReg : Registration Spec.Seed.cfbEncryptApi X86_64.target :=
  withScrub {
    code := cfbEncryptCode
    stack := 1552
    verified := Proof.Seed.X86_64.cfbEncrypt_framed } cfbEncryptOut [] (pubOk_nil _) (some ⟨cfbEncryptKs, cfbEncryptOk⟩)

/-- `vg_seed_cfb128_encrypt_final`'s code. -/
abbrev cfbEncryptFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cfbEncryptFinal

def cfbEncryptFinalKs : List Nat := keep_for% Spec.Seed.cfbEncryptFinalApi.sig 1552 cfbEncryptFinalCode []

theorem cfbEncryptFinalOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Seed.cfbEncryptFinalApi.sig 1552 []) cfbEncryptFinalCode
      h).any (RScrub.resOkB · 1552 cfbEncryptFinalKs (Impl.Scrub.X86_64.chunks 1552)) = true :=
  RScrub.Analysed.ok_of cfbEncryptFinalKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_seed_cfb128_encrypt_final`. -/
def cfbEncryptFinalReg : Registration Spec.Seed.cfbEncryptFinalApi X86_64.target :=
  withScrub {
    code := cfbEncryptFinalCode
    stack := 1552
    verified := Proof.Seed.X86_64.cfbEncryptFinal_framed } cfbEncryptFinalOut [] (pubOk_nil _) (some ⟨cfbEncryptFinalKs, cfbEncryptFinalOk⟩)

/-- `vg_seed_cfb128_decrypt`'s code. -/
abbrev cfbDecryptCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cfbDecrypt

def cfbDecryptKs : List Nat := keep_for% Spec.Seed.cfbDecryptApi.sig 1552 cfbDecryptCode []

theorem cfbDecryptOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Seed.cfbDecryptApi.sig 1552 []) cfbDecryptCode
      h).any (RScrub.resOkB · 1552 cfbDecryptKs (Impl.Scrub.X86_64.chunks 1552)) = true :=
  RScrub.Analysed.ok_of cfbDecryptKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_seed_cfb128_decrypt`. -/
def cfbDecryptReg : Registration Spec.Seed.cfbDecryptApi X86_64.target :=
  withScrub {
    code := cfbDecryptCode
    stack := 1552
    verified := Proof.Seed.X86_64.cfbDecrypt_framed } cfbDecryptOut [] (pubOk_nil _) (some ⟨cfbDecryptKs, cfbDecryptOk⟩)

/-- `vg_seed_cfb128_decrypt_final`'s code. -/
abbrev cfbDecryptFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cfbDecryptFinal

def cfbDecryptFinalKs : List Nat := keep_for% Spec.Seed.cfbDecryptFinalApi.sig 1552 cfbDecryptFinalCode []

theorem cfbDecryptFinalOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Seed.cfbDecryptFinalApi.sig 1552 []) cfbDecryptFinalCode
      h).any (RScrub.resOkB · 1552 cfbDecryptFinalKs (Impl.Scrub.X86_64.chunks 1552)) = true :=
  RScrub.Analysed.ok_of cfbDecryptFinalKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_seed_cfb128_decrypt_final`. -/
def cfbDecryptFinalReg : Registration Spec.Seed.cfbDecryptFinalApi X86_64.target :=
  withScrub {
    code := cfbDecryptFinalCode
    stack := 1552
    verified := Proof.Seed.X86_64.cfbDecryptFinal_framed } cfbDecryptFinalOut [] (pubOk_nil _) (some ⟨cfbDecryptFinalKs, cfbDecryptFinalOk⟩)

/-- `vg_seed_ofb`'s code. -/
abbrev ofbCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.ofb

def ofbKs : List Nat := keep_for% Spec.Seed.ofbApi.sig 1552 ofbCode []

theorem ofbOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Seed.ofbApi.sig 1552 []) ofbCode
      h).any (RScrub.resOkB · 1552 ofbKs (Impl.Scrub.X86_64.chunks 1552)) = true :=
  RScrub.Analysed.ok_of ofbKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_seed_ofb`. -/
def ofbReg : Registration Spec.Seed.ofbApi X86_64.target :=
  withScrub {
    code := ofbCode
    stack := 1552
    verified := Proof.Seed.X86_64.ofb_framed } ofbOut [] (pubOk_nil _) (some ⟨ofbKs, ofbOk⟩)

/-- `vg_seed_ofb_final`'s code. -/
abbrev ofbFinalCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.ofbFinal

def ofbFinalKs : List Nat := keep_for% Spec.Seed.ofbFinalApi.sig 1552 ofbFinalCode []

theorem ofbFinalOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Seed.ofbFinalApi.sig 1552 []) ofbFinalCode
      h).any (RScrub.resOkB · 1552 ofbFinalKs (Impl.Scrub.X86_64.chunks 1552)) = true :=
  RScrub.Analysed.ok_of ofbFinalKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_seed_ofb_final`. -/
def ofbFinalReg : Registration Spec.Seed.ofbFinalApi X86_64.target :=
  withScrub {
    code := ofbFinalCode
    stack := 1552
    verified := Proof.Seed.X86_64.ofbFinal_framed } ofbFinalOut [] (pubOk_nil _) (some ⟨ofbFinalKs, ofbFinalOk⟩)

end VG.Proof.Seed.X86_64.Scrub

