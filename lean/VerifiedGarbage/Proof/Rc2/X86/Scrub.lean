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
import VerifiedGarbage.Proof.Rc2.X86.Ssse3Key
import VerifiedGarbage.Proof.Rc2.X86.Ssse3Lit
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Framework.SigEval
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
meta import VerifiedGarbage.Proof.Rc2.X86.Ssse3Key
meta import VerifiedGarbage.Proof.Rc2.X86.Ssse3Lit
meta import VerifiedGarbage.Proof.Framework.X86.StackScratch
meta import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.Rc2.X86.Cbc.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# RC2 on x86 (32-bit), without secret residue

`vg_rc2_cbc_init`, `vg_rc2_cbc_encrypt_chained` and
`vg_rc2_cbc_decrypt_chained` as emitted (`Impl.Rc2.X86.Fn`), each followed by
the zeroing of the stack below `esp` that it uses and the clearing of the
registers a callee may change (`X86.Scrub.verifiedScrubbedAll`); and
`vg_rc2_cbc_init_ssse3` (`Impl.Rc2.X86.Fn.cbcInitSsse3`), `init` over the key
expansion that reads PITABLE by `pshufb` (`Proof.Rc2.X86.Ssse3.key`), which
uses four more bytes of stack. Their postconditions read the memory on
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

theorem cbcInitSsse3Out :
    PostOut (Spec.Rc2.cbcInitContract X86.abi 636) (Spec.Rc2.cbcInitSig.retBits 32) :=
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

/-! ### `init` with PITABLE read by `pshufb` -/

/-- `init` over `vg_rc2_expand_key_ssse3`, with its working space as an argument. -/
theorem initSsse3_verified :
    Verified X86.target Impl.Rc2.X86.Ssse3.init (Proof.Rc2.cbcInitScratchContract X86.abi 28) :=
  Proof.Rc2.X86.Stream.init_verifiedS Proof.Rc2.X86.Ssse3.key Proof.Rc2.X86.Stream.init_implies28

theorem initSsse3FrameSat_pre : ∃ s, (Spec.Rc2.cbcInitContract X86.abi 636).pre s := by
  implies_sat [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, Spec.Rc2.cbcInitPost, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes]
    [Proof.Rc2.X86.Stream.initFrameSat, Proof.Rc2.X86.Stream.initSat, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using Proof.Rc2.X86.Stream.initFrameSat

/-- With its working space in a frame of 608 bytes, as `Proof.Rc2.X86.Stream.init_framed`. -/
theorem initSsse3_framed :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratch 608 6 Impl.Rc2.X86.Ssse3.init)
      (Spec.Rc2.cbcInitContract X86.abi 636) :=
  X86.Verified.stackScratch (sig := Spec.Rc2.cbcInitSig) (nm := "scratch") (e := .u64)
    (n := 72) (post := Spec.Rc2.cbcInitPost X86.abi.ptrBits) (wa := true) (stack := 28)
    (bytes := 608) initSsse3_verified (by decide) (by lit_decide) (by lit_decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Rc2.cbcInitPost_local _)
    (fun vs m m₁ m₂ r hl _ hb h => Proof.Rc2.cbcInitPostOut_local _ vs m m₁ m₂ r hl hb h) initSsse3FrameSat_pre

/-- `Spec.Rc2.cbcInitApi` with PITABLE read by `pshufb`, as emitted
(`Impl.Rc2.X86.Fn.cbcInitSsse3`), meets its contract in constant time and
returns without secret residue. -/
theorem cbcInitSsse3_scrubbed :
    VerifiedScrubbed X86.target Impl.Rc2.X86.Fn.cbcInitSsse3 (Spec.Rc2.cbcInitContract X86.abi 636) 32 :=
  verifiedScrubbedAll (api := Spec.Rc2.cbcInitApi)
    { code := Impl.StackScratch.X86.withStackScratch 608 6 Impl.Rc2.X86.Ssse3.init
      verified := initSsse3_framed }
    cbcInitSsse3Out

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
