module

import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFn
public import VerifiedGarbage.Impl.Rc2.X86_64.Fn
public import VerifiedGarbage.Spec.Rc2.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Frame
public import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Chained
import VerifiedGarbage.Proof.Rc2.Scratch
import VerifiedGarbage.Proof.Rc2.CbcScratch
import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Lit
import VerifiedGarbage.Proof.Rc2.X86_64.Lit
import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Lit
meta import VerifiedGarbage.Spec.Rc2.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Frame
meta import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Chained
meta import VerifiedGarbage.Proof.Rc2.Scratch
meta import VerifiedGarbage.Proof.Rc2.CbcScratch
meta import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Lit
meta import VerifiedGarbage.Proof.Rc2.X86_64.Lit
meta import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Lit

/-!
# RC2 on x86-64, without secret residue

`vg_rc2_cbc_init`, `vg_rc2_cbc_encrypt_chained` and
`vg_rc2_cbc_decrypt_chained`, each followed by `Impl.Scrub.X86_64.scrubTail`
(`X86_64.Scrub.withScrub`), which clears the registers and the granules of
its stack that the residue analysis (`X86_64.RTaint`) finds may hold secrets.
Their postconditions read the memory on return only within their buffers
(`X86_64.Scrub.PostOut`), as their frames already show
(`X86_64.Verified.stackArgScratchWiped`'s and
`X86_64.Verified.stackScratchWiped`'s `hpost`).
-/

@[expose] public section

namespace VG.Proof.Rc2.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub

/-! ## Postconditions -/

theorem cbcInitOut : PostOut (Spec.Rc2.cbcInitContract X86_64.abi 600) (Spec.Rc2.cbcInitSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Rc2.cbcInitPostOut_local _)

theorem cbcEncryptChainedOut :
    PostOut (Spec.Rc2.cbcEncryptChainedContract X86_64.abi 528) (Spec.Rc2.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Rc2.cbcEncChainedPostOut_local (pb := 64))

theorem cbcDecryptChainedOut :
    PostOut (Spec.Rc2.cbcDecryptChainedContract X86_64.abi 528) (Spec.Rc2.cbcChainedSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Rc2.cbcDecChainedPostOut_local (pb := 64))

/-! ## The functions as emitted -/

/-- `vg_rc2_cbc_init` as emitted (`Impl.Rc2.X86_64.Fn.cbcInit`) meets its
contract in constant time and returns without secret residue. -/
theorem cbcInit_scrubbed :
    VerifiedScrubbed target Impl.Rc2.X86_64.Fn.cbcInit (Spec.Rc2.cbcInitApi.contract X86_64.abi 600) 32 :=
  verifiedScrubbedSel (api := Spec.Rc2.cbcInitApi)
    { code := Impl.StackScratch.X86_64.withStackArgScratchWiped 592 0 72 Impl.Rc2.X86_64.Stream.init
      stack := 600
      verified := Proof.Rc2.X86_64.Stream.init_framed } .sse [(0, 2)] cbcInitOut (RScrub.pubOk_nil _)
    (by taint_decide)

/-- `vg_rc2_cbc_encrypt_chained` as emitted (`Impl.Rc2.X86_64.Fn.cbcEncryptChained`). -/
theorem cbcEncryptChained_scrubbed :
    VerifiedScrubbed target Impl.Rc2.X86_64.Fn.cbcEncryptChained
      (Spec.Rc2.cbcEncryptChainedContract X86_64.abi 528) 0 :=
  verifiedScrubbedSel (api := Spec.Rc2.cbcEncryptChainedApi)
    { code := Impl.StackScratch.X86_64.withStackScratchWiped 520 .r8 64 Impl.Rc2.X86_64.Cbc.encrypt
      stack := 528
      verified := Proof.Rc2.X86_64.Cbc.encryptChained_framed } .sse [(8, 1)] cbcEncryptChainedOut
    (RScrub.pubOk_nil _) (by taint_decide)

/-- `vg_rc2_cbc_decrypt_chained` as emitted (`Impl.Rc2.X86_64.Fn.cbcDecryptChained`). -/
theorem cbcDecryptChained_scrubbed :
    VerifiedScrubbed target Impl.Rc2.X86_64.Fn.cbcDecryptChained
      (Spec.Rc2.cbcDecryptChainedContract X86_64.abi 528) 0 :=
  verifiedScrubbedSel (api := Spec.Rc2.cbcDecryptChainedApi)
    { code := Impl.StackScratch.X86_64.withStackScratchWiped 520 .r8 64 Impl.Rc2.X86_64.Cbc.decrypt
      stack := 528
      verified := Proof.Rc2.X86_64.Cbc.decryptChained_framed } .sse [(8, 1)] cbcDecryptChainedOut
    (RScrub.pubOk_nil _) (by taint_decide)

end VG.Proof.Rc2.X86_64.Scrub
