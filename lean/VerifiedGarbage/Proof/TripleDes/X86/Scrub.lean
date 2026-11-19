module

public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.TripleDes.X86.Frame
public import VerifiedGarbage.Proof.TripleDes.X86.CbcVerified
public import VerifiedGarbage.Proof.TripleDes.X86.FbVerified
public import VerifiedGarbage.Proof.TripleDes.X86.FbFinalVerified
import VerifiedGarbage.Proof.TripleDes.Scratch
import VerifiedGarbage.Proof.TripleDes.CbcScratch
import VerifiedGarbage.Proof.TripleDes.FbScratch
import VerifiedGarbage.Proof.Modes.CfbFinalScratch
import VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.X86.Bitsliced.SboxLit
import VerifiedGarbage.Proof.TripleDes.X86.CbcLit
import VerifiedGarbage.Proof.TripleDes.X86.FbLit
import VerifiedGarbage.Proof.TripleDes.X86.FbFinalLit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Triple DES on x86 (32-bit), without secret residue

Key expansion, ECB and the CBC, CFB64, CFB8 and OFB functions run with their
working space in a frame on the stack (`withStackScratchWiped`), and the
modes call the block function or the batched ECB code directly. Each is
scrubbed with `X86.Scrub.scrubFOf`, which zeroes the stack its contract
reserves below `esp` (532 bytes for key expansion, 1060 for ECB, 984 for the
modes one block at a time and 1248 for the batched CBC and CFB64
decryption) and clears the registers a callee may change. What the scrub
needs of the code is one Boolean (`X86.Scrub.scrubFSide`), proved by
evaluating the code once (`lit_decide`). Their postconditions read the
memory on return only within their buffers, by the lemmas of
`Proof/TripleDes/Scratch.lean`, `CbcScratch.lean`, `FbScratch.lean` and
`Proof/Modes/CfbFinalScratch.lean` that the other targets use too.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86.Scrub

open VG.X86 VG.X86.Scrub

/-! ## The postconditions -/

theorem expandKeyOut : PostOut (Spec.TripleDes.expandKeyContract X86.abi 532) (Spec.TripleDes.expandKeySig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.expandKeyPostOut_local _)

theorem ecbOut (d : Spec.TripleDes.Direction) :
    PostOut (Spec.TripleDes.ecbContract X86.abi d 1060) (Spec.TripleDes.ecbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.ecbPostOut_local _ d)

theorem cbcEncryptOut :
    PostOut (Spec.TripleDes.cbcEncryptChainedContract X86.abi 984) (Spec.TripleDes.cbcChainedSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cbcEncChainedPostOut_local _)

theorem cbcDecryptOut :
    PostOut (Spec.TripleDes.cbcDecryptChainedContract X86.abi 1248) (Spec.TripleDes.cbcChainedSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cbcDecChainedPostOut_local _)

theorem cfbEncryptOut : PostOut (Spec.TripleDes.cfbEncryptContract X86.abi 984) (Spec.TripleDes.cfbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cfbEncPostOut_local _)

theorem cfbDecryptOut : PostOut (Spec.TripleDes.cfbDecryptContract X86.abi 1248) (Spec.TripleDes.cfbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cfbDecPostOut_local _)

theorem cfbEncryptFinalOut :
    PostOut (Spec.TripleDes.cfbEncryptFinalContract X86.abi 984) (Spec.TripleDes.cfbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.encFinalPost_local _)

theorem cfbDecryptFinalOut :
    PostOut (Spec.TripleDes.cfbDecryptFinalContract X86.abi 984) (Spec.TripleDes.cfbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.decFinalPost_local _)

theorem cfb8EncryptOut : PostOut (Spec.TripleDes.cfb8EncryptContract X86.abi 984) (Spec.TripleDes.cfb8Sig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cfb8EncPostOut_local _)

theorem cfb8DecryptOut : PostOut (Spec.TripleDes.cfb8DecryptContract X86.abi 984) (Spec.TripleDes.cfb8Sig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cfb8DecPostOut_local _)

theorem ofbOut : PostOut (Spec.TripleDes.ofbContract X86.abi 984) (Spec.TripleDes.ofbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.ofbPostOut_local _)

theorem ofbFinalOut : PostOut (Spec.TripleDes.ofbFinalContract X86.abi 984) (Spec.TripleDes.ofbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.ofbFinalPost_local _)

/-! ## The registrations -/

/-- `vg_triple_des_expand_key`. -/
def expandKeyReg : Registration Spec.TripleDes.expandKeyApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratchWiped 532 3 128 Impl.TripleDes.X86.Key.expandKey
      verified := Proof.TripleDes.X86.expandKey_framed }
    expandKeyOut

/-- `vg_triple_des_ecb_encrypt`. -/
def ecbEncryptReg : Registration Spec.TripleDes.ecbEncryptApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratchWiped 1044 3 256 Impl.TripleDes.X86.Ecb.encrypt
      verified := Proof.TripleDes.X86.ecb_framed .encrypt }
    (ecbOut .encrypt)

/-- `vg_triple_des_ecb_decrypt`. -/
def ecbDecryptReg : Registration Spec.TripleDes.ecbDecryptApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratchWiped 1044 3 256 Impl.TripleDes.X86.Ecb.decrypt
      verified := Proof.TripleDes.X86.ecb_framed .decrypt }
    (ecbOut .decrypt)

/-- `vg_triple_des_cbc_encrypt_chained`. -/
def cbcEncryptChainedReg : Registration Spec.TripleDes.cbcEncryptChainedApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cbcEncryptChained
      verified := Proof.TripleDes.X86.Cbc.cbcEncryptChained_framed }
    cbcEncryptOut

/-- `vg_triple_des_cbc_decrypt_chained`. -/
def cbcDecryptChainedReg : Registration Spec.TripleDes.cbcDecryptChainedApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratchWiped 1232 4 302 Impl.TripleDes.X86.cbcDecryptChained
      verified := Proof.TripleDes.X86.Cbc.cbcDecryptChained_framed }
    cbcDecryptOut

/-- `vg_triple_des_cfb64_encrypt`. -/
def cfbEncryptReg : Registration Spec.TripleDes.cfbEncryptApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cfbEncrypt
      verified := Proof.TripleDes.X86.Fb.cfbEncrypt_framed }
    cfbEncryptOut

/-- `vg_triple_des_cfb64_decrypt`. -/
def cfbDecryptReg : Registration Spec.TripleDes.cfbDecryptApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratchWiped 1232 4 302 Impl.TripleDes.X86.cfbDecrypt
      verified := Proof.TripleDes.X86.Fb.cfbDecrypt_framed }
    cfbDecryptOut

/-- `vg_triple_des_cfb64_encrypt_final`. -/
def cfbEncryptFinalReg : Registration Spec.TripleDes.cfbEncryptFinalApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cfbEncryptFinal
      verified := Proof.TripleDes.X86.FbFinal.cfbEncryptFinal_framed }
    cfbEncryptFinalOut

/-- `vg_triple_des_cfb64_decrypt_final`. -/
def cfbDecryptFinalReg : Registration Spec.TripleDes.cfbDecryptFinalApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cfbDecryptFinal
      verified := Proof.TripleDes.X86.FbFinal.cfbDecryptFinal_framed }
    cfbDecryptFinalOut

/-- `vg_triple_des_cfb8_encrypt`. -/
def cfb8EncryptReg : Registration Spec.TripleDes.cfb8EncryptApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cfb8Encrypt
      verified := Proof.TripleDes.X86.Fb.cfb8Encrypt_framed }
    cfb8EncryptOut

/-- `vg_triple_des_cfb8_decrypt`. -/
def cfb8DecryptReg : Registration Spec.TripleDes.cfb8DecryptApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cfb8Decrypt
      verified := Proof.TripleDes.X86.Fb.cfb8Decrypt_framed }
    cfb8DecryptOut

/-- `vg_triple_des_ofb`. -/
def ofbReg : Registration Spec.TripleDes.ofbApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.ofb
      verified := Proof.TripleDes.X86.Fb.ofb_framed }
    ofbOut

/-- `vg_triple_des_ofb_final`. -/
def ofbFinalReg : Registration Spec.TripleDes.ofbFinalApi X86.target :=
  scrubFOf {
      code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.ofbFinal
      verified := Proof.TripleDes.X86.FbFinal.ofbFinal_framed }
    ofbFinalOut

end VG.Proof.TripleDes.X86.Scrub
