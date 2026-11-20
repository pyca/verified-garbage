module

public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Seed.Contract
public import VerifiedGarbage.Spec.Seed.Cbc
public import VerifiedGarbage.Spec.Seed.Cfb
public import VerifiedGarbage.Spec.Seed.CfbFinal
public import VerifiedGarbage.Spec.Seed.Ofb
public import VerifiedGarbage.Spec.Seed.OfbFinal
public import VerifiedGarbage.Impl.Seed.X86.Fn
public import VerifiedGarbage.Proof.Seed.X86.KeyVerified
public import VerifiedGarbage.Proof.Seed.X86.EcbCall
public import VerifiedGarbage.Proof.Seed.X86.CbcVerified
public import VerifiedGarbage.Proof.Seed.X86.FbVerified
public import VerifiedGarbage.Proof.Seed.X86.FbFinalVerified
import VerifiedGarbage.Proof.Seed.Scratch
import VerifiedGarbage.Proof.Seed.CbcScratch
import VerifiedGarbage.Proof.Seed.FbScratch
import VerifiedGarbage.Proof.Modes.CfbFinalScratch
import VerifiedGarbage.Proof.Seed.X86.Lit
import VerifiedGarbage.Proof.Seed.X86.CbcLit
import VerifiedGarbage.Proof.Seed.X86.FbLit
import VerifiedGarbage.Proof.Seed.X86.FbFinalLit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Seed.Contract
meta import VerifiedGarbage.Spec.Seed.Cbc
meta import VerifiedGarbage.Spec.Seed.Cfb
meta import VerifiedGarbage.Spec.Seed.CfbFinal
meta import VerifiedGarbage.Spec.Seed.Ofb
meta import VerifiedGarbage.Spec.Seed.OfbFinal
meta import VerifiedGarbage.Impl.Seed.X86.Fn
meta import VerifiedGarbage.Proof.Seed.X86.KeyVerified
meta import VerifiedGarbage.Proof.Seed.X86.EcbCall
meta import VerifiedGarbage.Proof.Seed.X86.CbcVerified
meta import VerifiedGarbage.Proof.Seed.X86.FbVerified
meta import VerifiedGarbage.Proof.Seed.X86.FbFinalVerified
meta import VerifiedGarbage.Proof.Seed.Scratch
meta import VerifiedGarbage.Proof.Seed.CbcScratch
meta import VerifiedGarbage.Proof.Seed.FbScratch
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Proof.Seed.X86.Lit
meta import VerifiedGarbage.Proof.Seed.X86.CbcLit
meta import VerifiedGarbage.Proof.Seed.X86.FbLit
meta import VerifiedGarbage.Proof.Seed.X86.FbFinalLit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SEED on x86 (32-bit), without secret residue

Key expansion and the ECB, CBC, CFB128 and OFB functions run with their
working space in a frame on the stack, wiped before they return
(`withStackScratchWiped`). The code as emitted (`Impl.Seed.X86.Fn`) then
zeroes the stack their contracts reserve below `esp` and clears the
registers a callee may change, and returns without secret residue
(`X86.Scrub.verifiedScrubbedF`), given that its postcondition reads the
memory on return only within the buffers (`Proof/Seed/Scratch.lean`,
`CbcScratch.lean`, `FbScratch.lean` and `Proof/Modes/CfbFinalScratch.lean`,
for any pointer width). What the cleanup needs of the code is one Boolean
(`X86.Scrub.scrubFSide`), proved by evaluating the code once
(`lit_decide`).
-/

@[expose] public section

namespace VG.Proof.Seed.X86.Scrub

open VG.X86 VG.X86.Scrub
open Impl.StackScratch.X86 (withStackScratchWiped)

/-! ## Postconditions -/

theorem expandKeyOut : PostOut (Spec.Seed.expandKeyContract X86.abi 840) (Spec.Seed.expandKeySig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Seed.expandKeyPostOut_local _)

theorem ecbOut (d : Spec.Seed.Direction) :
    PostOut (Spec.Seed.ecbContract X86.abi d 1132) (Spec.Seed.ecbSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Seed.ecbPostOut_local _ d)

theorem cbcEncryptOut : PostOut (Spec.Seed.cbcEncryptChainedContract X86.abi 1188) (Spec.Seed.cbcChainedSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Seed.cbcEncChainedPostOut_local _)

theorem cbcDecryptOut : PostOut (Spec.Seed.cbcDecryptChainedContract X86.abi 1188) (Spec.Seed.cbcChainedSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Seed.cbcDecChainedPostOut_local _)

theorem cfbEncryptOut : PostOut (Spec.Seed.cfbEncryptContract X86.abi 1188) (Spec.Seed.cfbSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Seed.cfbEncPostOut_local _)

theorem cfbDecryptOut : PostOut (Spec.Seed.cfbDecryptContract X86.abi 1188) (Spec.Seed.cfbSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Seed.cfbDecPostOut_local _)

theorem cfbEncryptFinalOut : PostOut (Spec.Seed.cfbEncryptFinalContract X86.abi 1188) (Spec.Seed.cfbFinalSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Modes.encFinalPost_local _)

theorem cfbDecryptFinalOut : PostOut (Spec.Seed.cfbDecryptFinalContract X86.abi 1188) (Spec.Seed.cfbFinalSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Modes.decFinalPost_local _)

theorem ofbOut : PostOut (Spec.Seed.ofbContract X86.abi 1188) (Spec.Seed.ofbSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Seed.ofbPostOut_local _)

theorem ofbFinalOut : PostOut (Spec.Seed.ofbFinalContract X86.abi 1188) (Spec.Seed.ofbFinalSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Modes.ofbFinalPost_local _)

/-! ## The functions as emitted -/

/-- `vg_seed_expand_key` as emitted (`Impl.Seed.X86.Fn.expandKey`) meets its contract in
constant time and returns without secret residue. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed target Impl.Seed.X86.Fn.expandKey (Spec.Seed.expandKeyContract X86.abi 840) 0 :=
  verifiedScrubbedF (api := Spec.Seed.expandKeyApi)
    { code := withStackScratchWiped 840 2 206 Impl.Seed.X86.expandKey
      verified := Proof.Seed.X86.expandKey_framed }
    expandKeyOut

/-- `vg_seed_ecb_encrypt` as emitted (`Impl.Seed.X86.Fn.ecb .encrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem ecbEncrypt_scrubbed :
    VerifiedScrubbed target (Impl.Seed.X86.Fn.ecb .encrypt) (Spec.Seed.ecbContract X86.abi .encrypt 1132) 0 :=
  verifiedScrubbedF (api := Spec.Seed.ecbEncryptApi)
    { code := withStackScratchWiped 1108 3 272 (Impl.Seed.X86.ecbCall .encrypt)
      verified := Proof.Seed.X86.ecbCall_framed .encrypt }
    (ecbOut _)

/-- `vg_seed_ecb_decrypt` as emitted (`Impl.Seed.X86.Fn.ecb .decrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem ecbDecrypt_scrubbed :
    VerifiedScrubbed target (Impl.Seed.X86.Fn.ecb .decrypt) (Spec.Seed.ecbContract X86.abi .decrypt 1132) 0 :=
  verifiedScrubbedF (api := Spec.Seed.ecbDecryptApi)
    { code := withStackScratchWiped 1108 3 272 (Impl.Seed.X86.ecbCall .decrypt)
      verified := Proof.Seed.X86.ecbCall_framed .decrypt }
    (ecbOut _)

/-- `vg_seed_cbc_encrypt_chained` as emitted meets its contract in constant
time and returns without secret residue. -/
theorem cbcEncryptChained_scrubbed :
    VerifiedScrubbed target Impl.Seed.X86.Fn.cbcEncryptChained
      (Spec.Seed.cbcEncryptChainedContract X86.abi 1188) 0 :=
  verifiedScrubbedF (api := Spec.Seed.cbcEncryptChainedApi)
    { code := withStackScratchWiped 1168 4 286 Impl.Seed.X86.cbcEncryptChained
      verified := Proof.Seed.X86.Cbc.cbcEncryptChained_framed }
    cbcEncryptOut

/-- `vg_seed_cbc_decrypt_chained` as emitted meets its contract in constant
time and returns without secret residue. -/
theorem cbcDecryptChained_scrubbed :
    VerifiedScrubbed target Impl.Seed.X86.Fn.cbcDecryptChained
      (Spec.Seed.cbcDecryptChainedContract X86.abi 1188) 0 :=
  verifiedScrubbedF (api := Spec.Seed.cbcDecryptChainedApi)
    { code := withStackScratchWiped 1168 4 286 Impl.Seed.X86.cbcDecryptChained
      verified := Proof.Seed.X86.Cbc.cbcDecryptChained_framed }
    cbcDecryptOut

/-- `vg_seed_cfb128_encrypt` as emitted meets its contract in constant time
and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed target Impl.Seed.X86.Fn.cfbEncrypt (Spec.Seed.cfbEncryptContract X86.abi 1188) 0 :=
  verifiedScrubbedF (api := Spec.Seed.cfbEncryptApi)
    { code := withStackScratchWiped 1168 4 286 Impl.Seed.X86.cfbEncrypt
      verified := Proof.Seed.X86.Fb.cfbEncrypt_framed }
    cfbEncryptOut

/-- `vg_seed_cfb128_decrypt` as emitted meets its contract in constant time
and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed target Impl.Seed.X86.Fn.cfbDecrypt (Spec.Seed.cfbDecryptContract X86.abi 1188) 0 :=
  verifiedScrubbedF (api := Spec.Seed.cfbDecryptApi)
    { code := withStackScratchWiped 1168 4 286 Impl.Seed.X86.cfbDecrypt
      verified := Proof.Seed.X86.Fb.cfbDecrypt_framed }
    cfbDecryptOut

/-- `vg_seed_cfb128_encrypt_final` as emitted meets its contract in constant
time and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed target Impl.Seed.X86.Fn.cfbEncryptFinal
      (Spec.Seed.cfbEncryptFinalContract X86.abi 1188) 0 :=
  verifiedScrubbedF (api := Spec.Seed.cfbEncryptFinalApi)
    { code := withStackScratchWiped 1168 4 286 Impl.Seed.X86.cfbEncryptFinal
      verified := Proof.Seed.X86.FbFinal.cfbEncryptFinal_framed }
    cfbEncryptFinalOut

/-- `vg_seed_cfb128_decrypt_final` as emitted meets its contract in constant
time and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed target Impl.Seed.X86.Fn.cfbDecryptFinal
      (Spec.Seed.cfbDecryptFinalContract X86.abi 1188) 0 :=
  verifiedScrubbedF (api := Spec.Seed.cfbDecryptFinalApi)
    { code := withStackScratchWiped 1168 4 286 Impl.Seed.X86.cfbDecryptFinal
      verified := Proof.Seed.X86.FbFinal.cfbDecryptFinal_framed }
    cfbDecryptFinalOut

/-- `vg_seed_ofb` as emitted meets its contract in constant time and returns
without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed target Impl.Seed.X86.Fn.ofb (Spec.Seed.ofbContract X86.abi 1188) 0 :=
  verifiedScrubbedF (api := Spec.Seed.ofbApi)
    { code := withStackScratchWiped 1168 4 286 Impl.Seed.X86.ofb
      verified := Proof.Seed.X86.Fb.ofb_framed }
    ofbOut

/-- `vg_seed_ofb_final` as emitted meets its contract in constant time and
returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed target Impl.Seed.X86.Fn.ofbFinal (Spec.Seed.ofbFinalContract X86.abi 1188) 0 :=
  verifiedScrubbedF (api := Spec.Seed.ofbFinalApi)
    { code := withStackScratchWiped 1168 4 286 Impl.Seed.X86.ofbFinal
      verified := Proof.Seed.X86.FbFinal.ofbFinal_framed }
    ofbFinalOut

end VG.Proof.Seed.X86.Scrub
