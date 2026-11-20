module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFn
public import VerifiedGarbage.Impl.Sm3.X86_64.Fn
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Spec.Sm3.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sm3.X86_64.Shared
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Sm3.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sm3.X86_64.Lit
meta import VerifiedGarbage.Spec.Sm3.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Sm3.X86_64.Shared
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Sm3.Stream
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Sm3.X86_64.Lit
import VerifiedGarbage.Proof.Sm3.PostOut
meta import VerifiedGarbage.Proof.Sm3.PostOut

/-!
# SM3's streaming functions on x86-64, without secret residue

`vg_sm3_init`, `vg_sm3_update` and `vg_sm3_finalize`, each
followed by `Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`), which
clears the registers and the granules of its stack that the residue analysis
(`X86_64.RTaint`) finds may hold secrets. Their postconditions read the
memory on return only within the buffers (`X86_64.Scrub.PostOut`): the
streaming state (`Stream.repr_congr`) and the digest.
-/

@[expose] public section

namespace VG.Proof.Sm3.X86_64

open VG.Spec.Sm3 VG.X86_64 VG.X86_64.Scrub

theorem initOut : PostOut (initContract X86_64.abi) (initSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm3.initPost_out 64)

theorem updateOut (stack : Nat) : PostOut (updateContract X86_64.abi stack) (updateSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm3.updatePost_out 64)

theorem finalizeOut (stack : Nat) : PostOut (finalizeContract X86_64.abi stack) (finalizeSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm3.finalizePost_out 64)

/-! ## The registrations -/

/-- `vg_sm3_update`'s code. -/
abbrev updateCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratch 168 .r8 Impl.Sm3.X86_64.Stream.update

/-- `vg_sm3_finalize`'s code. -/
abbrev finalizeCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratch 168 .rcx Impl.Sm3.X86_64.Stream.finalize

/-! ## The functions as emitted -/

theorem init_codeSp : (Impl.Sm3.X86_64.Stream.init).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Sm3.initApi`'s function as emitted (`Impl.Sm3.X86_64.Fn.init`) meets its contract in
constant time and returns without secret residue. -/
theorem init_scrubbed :
    VerifiedScrubbed target Impl.Sm3.X86_64.Fn.init (Spec.Sm3.initApi.contract X86_64.abi 0) 0 :=
  verifiedScrubbedSel (api := Spec.Sm3.initApi)
    { code := Impl.Sm3.X86_64.Stream.init
      verified := Shared.init
      spSafe := init_codeSp }
    .sse [] initOut (RScrub.pubOk_nil _) (by taint_decide)

theorem init_spSafe : Impl.Sm3.X86_64.Fn.init.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe init_codeSp

theorem update_codeSp : (Impl.StackScratch.X86_64.withStackScratch 168 .r8 Impl.Sm3.X86_64.Stream.update).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Sm3.updateApi`'s function as emitted (`Impl.Sm3.X86_64.Fn.update`) meets its contract in
constant time and returns without secret residue. -/
theorem update_scrubbed :
    VerifiedScrubbed target Impl.Sm3.X86_64.Fn.update (Spec.Sm3.updateApi.contract X86_64.abi 176) 0 :=
  verifiedScrubbedSel (api := Spec.Sm3.updateApi)
    { code := updateCode
      stack := 8 + 168
      verified := Shared.update
      spSafe := update_codeSp }
    .sse [(8, 5)] (updateOut _) (RScrub.pubOk_nil _) (by taint_decide)

theorem update_spSafe : Impl.Sm3.X86_64.Fn.update.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe update_codeSp

theorem finalize_codeSp : (Impl.StackScratch.X86_64.withStackScratch 168 .rcx Impl.Sm3.X86_64.Stream.finalize).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Sm3.finalizeApi`'s function as emitted (`Impl.Sm3.X86_64.Fn.finalize`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize_scrubbed :
    VerifiedScrubbed target Impl.Sm3.X86_64.Fn.finalize (Spec.Sm3.finalizeApi.contract X86_64.abi 176) 0 :=
  verifiedScrubbedSel (api := Spec.Sm3.finalizeApi)
    { code := finalizeCode
      stack := 8 + 168
      verified := Shared.finalize
      spSafe := finalize_codeSp }
    .sse [(8, 5)] (finalizeOut _) (RScrub.pubOk_nil _) (by taint_decide)

theorem finalize_spSafe : Impl.Sm3.X86_64.Fn.finalize.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe finalize_codeSp
end VG.Proof.Sm3.X86_64
