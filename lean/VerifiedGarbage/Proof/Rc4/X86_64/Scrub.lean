module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubSel
public import VerifiedGarbage.Impl.Rc4.X86_64.Fn
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Spec.Rc4.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rc4.X86_64.Verified
import VerifiedGarbage.Proof.Rc4.Scratch
import VerifiedGarbage.Proof.Rc4.X86_64.Lit
meta import VerifiedGarbage.Spec.Rc4.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Rc4.X86_64.Verified
meta import VerifiedGarbage.Proof.Rc4.Scratch
meta import VerifiedGarbage.Proof.Rc4.X86_64.Lit

/-!
# RC4 on x86-64, without secret residue

`vg_rc4_init`, followed by `Impl.Scrub.X86_64.scrubTail`
(`X86_64.Scrub.withScrub`), which clears the registers that the residue
analysis (`X86_64.RTaint`) finds may hold secrets. Its postcondition reads
the memory on return only within the context (`X86_64.Scrub.PostOut`,
`Proof.Rc4.initPostOut_local`). `vg_rc4_apply`, which uses no stack, is
followed by the clearing of every register it may write
(`X86_64.Scrub.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.Rc4.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub

/-! ## Postconditions -/

theorem initOut : PostOut (Spec.Rc4.initContract X86_64.abi 0) (Spec.Rc4.initSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Rc4.initPostOut_local _)

theorem applyOut : PostOut (Spec.Rc4.applyContract X86_64.abi 0) (Spec.Rc4.applySig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain (Proof.Rc4.applyPostOut_local _)

/-! ## The registrations -/

/-- `vg_rc4_init`'s code. -/
abbrev initCode : Prog isa :=
  Impl.Rc4.X86_64.init

/-! ## The functions as emitted -/

theorem init_codeSp : (Impl.Rc4.X86_64.init).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Rc4.initApi`'s function as emitted (`Impl.Rc4.X86_64.Fn.init`) meets its contract in
constant time and returns without secret residue. -/
theorem init_scrubbed :
    VerifiedScrubbed target Impl.Rc4.X86_64.Fn.init (Spec.Rc4.initApi.contract X86_64.abi 0) 32 :=
  verifiedScrubbedSel (api := Spec.Rc4.initApi)
    { code := initCode
      verified := Proof.Rc4.X86_64.init_verified
      spSafe := init_codeSp }
    .sse [] initOut (RScrub.pubOk_nil _) (by taint_decide)

theorem init_spSafe : Impl.Rc4.X86_64.Fn.init.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe init_codeSp

theorem apply_codeSp : (Impl.Rc4.X86_64.apply).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Rc4.applyApi`'s function as emitted (`Impl.Rc4.X86_64.Fn.apply`) meets its contract in
constant time and returns without secret residue. -/
theorem apply_scrubbed :
    VerifiedScrubbed target Impl.Rc4.X86_64.Fn.apply (Spec.Rc4.applyApi.contract X86_64.abi 0) 0 :=
  verifiedScrubbedAll (api := Spec.Rc4.applyApi)
    { code := Impl.Rc4.X86_64.apply
      verified := Proof.Rc4.X86_64.apply_verified
      spSafe := apply_codeSp }
    .sse applyOut

theorem apply_spSafe : Impl.Rc4.X86_64.Fn.apply.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe apply_codeSp
end VG.Proof.Rc4.X86_64.Scrub
