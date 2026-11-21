module

public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.X86.ScrubWiped
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Impl.TripleDes.X86.Fn
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
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Proof.Framework.X86.ScrubWiped
meta import VerifiedGarbage.Proof.Framework.X86.ScrubSel
meta import VerifiedGarbage.Impl.TripleDes.X86.Fn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.TripleDes.X86.Frame
meta import VerifiedGarbage.Proof.TripleDes.X86.CbcVerified
meta import VerifiedGarbage.Proof.TripleDes.X86.FbVerified
meta import VerifiedGarbage.Proof.TripleDes.X86.FbFinalVerified
meta import VerifiedGarbage.Proof.TripleDes.Scratch
meta import VerifiedGarbage.Proof.TripleDes.CbcScratch
meta import VerifiedGarbage.Proof.TripleDes.FbScratch
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit
meta import VerifiedGarbage.Proof.TripleDes.X86.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.TripleDes.X86.CbcLit
meta import VerifiedGarbage.Proof.TripleDes.X86.FbLit
meta import VerifiedGarbage.Proof.TripleDes.X86.FbFinalLit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.TripleDes.X86.Modes

/-!
# Triple DES on x86 (32-bit), without secret residue

Key expansion, ECB and the CBC, CFB64, CFB8 and OFB functions run with their
working space in a frame on the stack (`withStackScratchWiped`), and the
modes call the block function or the batched ECB code directly. Key
expansion calls nothing in its frame, which it wipes itself: as emitted
(`Impl.TripleDes.X86.Fn.expandKey`) it then clears the registers alone
(`X86.Scrub.verifiedScrubbedWiped`). As emitted, each of the others then
zeroes, of the stack its contract reserves below `esp` (1060 for ECB, 984
for the modes one block at a time and 1248 for the batched CBC and CFB64
decryption), only the eight to ten doublewords that the residue analysis
(`X86.rtaint`) finds it may leave different in two runs: the header of its
working space's frame (its copies of the arguments, which the modes may
overwrite, and the buffer's address) and the frames of the calls below it.
It clears the registers a callee may change, and returns without secret
residue (`X86.Scrub.verifiedScrubbedSel`), the kernel evaluating the
analysis of the code with its cleanup (`taint_decide_ct`). Their postconditions read the
memory on return only within their buffers, by the lemmas of
`Proof/TripleDes/Scratch.lean`, `CbcScratch.lean`, `FbScratch.lean` and
`Proof/Modes/CfbFinalScratch.lean` that the other targets use too.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86.Scrub

open VG.X86 VG.X86.Scrub

/-! ## The postconditions -/

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

/-! ## The functions as emitted -/

/-- `Spec.TripleDes.expandKeyApi` as emitted (`Impl.TripleDes.X86.Fn.expandKey`) meets its contract
in constant time and returns without secret residue. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed X86.target Impl.TripleDes.X86.Fn.expandKey (Spec.TripleDes.expandKeyContract X86.abi 532) 0 :=
  verifiedScrubbedWiped (sig := Spec.TripleDes.expandKeySig) (nm := "scratch") (e := .u64) (n := 64)
    (pre := Spec.TripleDes.expandKeyPre X86.abi.ptrBits) (post := Spec.TripleDes.expandKeyPost X86.abi.ptrBits)
    (bytes := 532) (words := 128) Proof.TripleDes.X86.Key.verified (by decide) (by decide) (by lit_decide)
    (Proof.TripleDes.expandKeyPre_local _) (Proof.TripleDes.expandKeyPost_local _)
    (Proof.TripleDes.expandKeyPostOut_local _) Proof.TripleDes.X86.expandKeyFrameSat_pre rfl

/-- `Spec.TripleDes.ecbEncryptApi` as emitted (`Impl.TripleDes.X86.Fn.ecbEncrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem ecbEncrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.TripleDes.X86.Fn.ecbEncrypt (Spec.TripleDes.ecbContract X86.abi Spec.TripleDes.Direction.encrypt 1060) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.ecbEncryptApi) (W := 1060)
    { code := Impl.StackScratch.X86.withStackScratchWiped 1044 3 256 Impl.TripleDes.X86.Ecb.encrypt
      verified := Proof.TripleDes.X86.ecb_framed .encrypt }
    Impl.TripleDes.X86.Fn.ecbWords (ecbOut .encrypt) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.TripleDes.ecbDecryptApi` as emitted (`Impl.TripleDes.X86.Fn.ecbDecrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem ecbDecrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.TripleDes.X86.Fn.ecbDecrypt (Spec.TripleDes.ecbContract X86.abi Spec.TripleDes.Direction.decrypt 1060) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.ecbDecryptApi) (W := 1060)
    { code := Impl.StackScratch.X86.withStackScratchWiped 1044 3 256 Impl.TripleDes.X86.Ecb.decrypt
      verified := Proof.TripleDes.X86.ecb_framed .decrypt }
    Impl.TripleDes.X86.Fn.ecbWords (ecbOut .decrypt) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.TripleDes.cbcEncryptChainedApi` as emitted (`Impl.TripleDes.X86.Fn.cbcEncryptChained`) meets its contract
in constant time and returns without secret residue. -/
theorem cbcEncryptChained_scrubbed :
    VerifiedScrubbed X86.target Impl.TripleDes.X86.Fn.cbcEncryptChained (Spec.TripleDes.cbcEncryptChainedContract X86.abi 984) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cbcEncryptChainedApi) (W := 984)
    { code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cbcEncryptChained
      verified := Proof.TripleDes.X86.Cbc.cbcEncryptChained_framed }
    Impl.TripleDes.X86.Fn.blockWords cbcEncryptOut (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.TripleDes.cbcDecryptChainedApi` as emitted (`Impl.TripleDes.X86.Fn.cbcDecryptChained`) meets its contract
in constant time and returns without secret residue. -/
theorem cbcDecryptChained_scrubbed :
    VerifiedScrubbed X86.target Impl.TripleDes.X86.Fn.cbcDecryptChained (Spec.TripleDes.cbcDecryptChainedContract X86.abi 1248) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cbcDecryptChainedApi) (W := 1248)
    { code := Impl.StackScratch.X86.withStackScratchWiped 1232 4 302 Impl.TripleDes.X86.cbcDecryptChained
      verified := Proof.TripleDes.X86.Cbc.cbcDecryptChained_framed }
    Impl.TripleDes.X86.Fn.batchWords cbcDecryptOut (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.TripleDes.cfbEncryptApi` as emitted (`Impl.TripleDes.X86.Fn.cfbEncrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.TripleDes.X86.Fn.cfbEncrypt (Spec.TripleDes.cfbEncryptContract X86.abi 984) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cfbEncryptApi) (W := 984)
    { code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cfbEncrypt
      verified := Proof.TripleDes.X86.Fb.cfbEncrypt_framed }
    Impl.TripleDes.X86.Fn.blockWords cfbEncryptOut (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.TripleDes.cfbDecryptApi` as emitted (`Impl.TripleDes.X86.Fn.cfbDecrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.TripleDes.X86.Fn.cfbDecrypt (Spec.TripleDes.cfbDecryptContract X86.abi 1248) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cfbDecryptApi) (W := 1248)
    { code := Impl.StackScratch.X86.withStackScratchWiped 1232 4 302 Impl.TripleDes.X86.cfbDecrypt
      verified := Proof.TripleDes.X86.Fb.cfbDecrypt_framed }
    Impl.TripleDes.X86.Fn.batchWords cfbDecryptOut (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.TripleDes.cfbEncryptFinalApi` as emitted (`Impl.TripleDes.X86.Fn.cfbEncryptFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.TripleDes.X86.Fn.cfbEncryptFinal (Spec.TripleDes.cfbEncryptFinalContract X86.abi 984) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cfbEncryptFinalApi) (W := 984)
    { code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cfbEncryptFinal
      verified := Proof.TripleDes.X86.FbFinal.cfbEncryptFinal_framed }
    Impl.TripleDes.X86.Fn.blockWords cfbEncryptFinalOut (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.TripleDes.cfbDecryptFinalApi` as emitted (`Impl.TripleDes.X86.Fn.cfbDecryptFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.TripleDes.X86.Fn.cfbDecryptFinal (Spec.TripleDes.cfbDecryptFinalContract X86.abi 984) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cfbDecryptFinalApi) (W := 984)
    { code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cfbDecryptFinal
      verified := Proof.TripleDes.X86.FbFinal.cfbDecryptFinal_framed }
    Impl.TripleDes.X86.Fn.blockWords cfbDecryptFinalOut (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.TripleDes.cfb8EncryptApi` as emitted (`Impl.TripleDes.X86.Fn.cfb8Encrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem cfb8Encrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.TripleDes.X86.Fn.cfb8Encrypt (Spec.TripleDes.cfb8EncryptContract X86.abi 984) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cfb8EncryptApi) (W := 984)
    { code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cfb8Encrypt
      verified := Proof.TripleDes.X86.Fb.cfb8Encrypt_framed }
    Impl.TripleDes.X86.Fn.blockWords cfb8EncryptOut (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.TripleDes.cfb8DecryptApi` as emitted (`Impl.TripleDes.X86.Fn.cfb8Decrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem cfb8Decrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.TripleDes.X86.Fn.cfb8Decrypt (Spec.TripleDes.cfb8DecryptContract X86.abi 984) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cfb8DecryptApi) (W := 984)
    { code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cfb8Decrypt
      verified := Proof.TripleDes.X86.Fb.cfb8Decrypt_framed }
    Impl.TripleDes.X86.Fn.blockWords cfb8DecryptOut (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.TripleDes.ofbApi` as emitted (`Impl.TripleDes.X86.Fn.ofb`) meets its contract
in constant time and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed X86.target Impl.TripleDes.X86.Fn.ofb (Spec.TripleDes.ofbContract X86.abi 984) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.ofbApi) (W := 984)
    { code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.ofb
      verified := Proof.TripleDes.X86.Fb.ofb_framed }
    Impl.TripleDes.X86.Fn.blockWords ofbOut (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.TripleDes.ofbFinalApi` as emitted (`Impl.TripleDes.X86.Fn.ofbFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed X86.target Impl.TripleDes.X86.Fn.ofbFinal (Spec.TripleDes.ofbFinalContract X86.abi 984) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.ofbFinalApi) (W := 984)
    { code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.ofbFinal
      verified := Proof.TripleDes.X86.FbFinal.ofbFinal_framed }
    Impl.TripleDes.X86.Fn.blockWords ofbFinalOut (by decide) ⟨_, by taint_decide_ct⟩

end VG.Proof.TripleDes.X86.Scrub
