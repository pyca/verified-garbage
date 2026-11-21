module

public import VerifiedGarbage.Spec.Rc2.Contract
public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Impl.Rc2.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rc2.X86.Stream.Frame
public import VerifiedGarbage.Proof.Rc2.X86.Cbc.Chained
import VerifiedGarbage.Proof.Rc2.Scratch
import VerifiedGarbage.Proof.Rc2.CbcScratch
import VerifiedGarbage.Proof.Rc2.X86.Lit
import VerifiedGarbage.Proof.Rc2.X86.Stream.Lit
import VerifiedGarbage.Proof.Rc2.X86.Cbc.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Spec.Rc2.Contract
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Impl.Rc2.X86.Fn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Rc2.X86.Stream.Frame
meta import VerifiedGarbage.Proof.Rc2.X86.Cbc.Chained
meta import VerifiedGarbage.Proof.Rc2.Scratch
meta import VerifiedGarbage.Proof.Rc2.CbcScratch
meta import VerifiedGarbage.Proof.Rc2.X86.Lit
meta import VerifiedGarbage.Proof.Rc2.X86.Stream.Lit
meta import VerifiedGarbage.Proof.Rc2.X86.Cbc.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# RC2 on x86 (32-bit), without secret residue

`vg_rc2_cbc_init`, `vg_rc2_cbc_encrypt_chained` and
`vg_rc2_cbc_decrypt_chained` as emitted (`Impl.Rc2.X86.Fn`), each followed by
the zeroing of the stack below `esp` that it uses and the clearing of the
registers a callee may change (`X86.Scrub.verifiedScrubbedAll`). Their postconditions read the memory on
return only within their buffers (`Proof.Rc2.cbcInitPostOut_local`,
`Proof.Rc2.cbcEncChainedPostOut_local`,
`Proof.Rc2.cbcDecChainedPostOut_local`).
-/

@[expose] public section

namespace VG.Proof.Rc2.X86.Scrub

open VG.X86 VG.X86.Scrub

/-! ## Postconditions -/

theorem cbcInitOut : PostOut (Spec.Rc2.cbcInitContract X86.abi 632) (Spec.Rc2.cbcInitSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Rc2.cbcInitPostOut_local _)

theorem cbcEncryptChainedOut :
    PostOut (Spec.Rc2.cbcEncryptChainedContract X86.abi 560) (Spec.Rc2.cbcChainedSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Rc2.cbcEncChainedPostOut_local (pb := 32))

theorem cbcDecryptChainedOut :
    PostOut (Spec.Rc2.cbcDecryptChainedContract X86.abi 560) (Spec.Rc2.cbcChainedSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Rc2.cbcDecChainedPostOut_local (pb := 32))

/-! ## The functions as emitted -/

/-- `Spec.Rc2.cbcInitApi` as emitted (`Impl.Rc2.X86.Fn.cbcInit`) meets its contract
in constant time and returns without secret residue. -/
theorem cbcInit_scrubbed :
    VerifiedScrubbed X86.target Impl.Rc2.X86.Fn.cbcInit (Spec.Rc2.cbcInitContract X86.abi 632) 32 :=
  verifiedScrubbedAll (api := Spec.Rc2.cbcInitApi)
    { code := Impl.StackScratch.X86.withStackScratch 608 6 Impl.Rc2.X86.Stream.init
      verified := Proof.Rc2.X86.Stream.init_framed }
    cbcInitOut

/-- `Spec.Rc2.cbcEncryptChainedApi` as emitted (`Impl.Rc2.X86.Fn.cbcEncryptChained`) meets its contract
in constant time and returns without secret residue. -/
theorem cbcEncryptChained_scrubbed :
    VerifiedScrubbed X86.target Impl.Rc2.X86.Fn.cbcEncryptChained (Spec.Rc2.cbcEncryptChainedContract X86.abi 560) 0 :=
  verifiedScrubbedAll (api := Spec.Rc2.cbcEncryptChainedApi)
    { code := Impl.StackScratch.X86.withStackScratch 544 4 Impl.Rc2.X86.Cbc.encrypt
      verified := Proof.Rc2.X86.Cbc.encryptChained_framed }
    cbcEncryptChainedOut

/-- `Spec.Rc2.cbcDecryptChainedApi` as emitted (`Impl.Rc2.X86.Fn.cbcDecryptChained`) meets its contract
in constant time and returns without secret residue. -/
theorem cbcDecryptChained_scrubbed :
    VerifiedScrubbed X86.target Impl.Rc2.X86.Fn.cbcDecryptChained (Spec.Rc2.cbcDecryptChainedContract X86.abi 560) 0 :=
  verifiedScrubbedAll (api := Spec.Rc2.cbcDecryptChainedApi)
    { code := Impl.StackScratch.X86.withStackScratch 544 4 Impl.Rc2.X86.Cbc.decrypt
      verified := Proof.Rc2.X86.Cbc.decryptChained_framed }
    cbcDecryptChainedOut

end VG.Proof.Rc2.X86.Scrub
