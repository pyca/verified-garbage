module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFn
public import VerifiedGarbage.Impl.Md5.X86_64.Fn
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Spec.Md5.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Md5.X86_64.Shared
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Md5.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Md5.X86_64.Lit
meta import VerifiedGarbage.Spec.Md5.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Md5.X86_64.Shared
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Md5.Stream
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Md5.X86_64.Lit
import VerifiedGarbage.Proof.Md5.PostOut
meta import VerifiedGarbage.Proof.Md5.PostOut

/-!
# MD5's streaming functions on x86-64, without secret residue

`vg_md5_init`, `vg_md5_update` and `vg_md5_finalize`, each followed by
`Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`), which clears the
registers and the granules of its stack that the residue analysis
(`X86_64.RTaint`) finds may hold secrets. HMAC-MD5 and PBKDF2-HMAC-MD5 call
`vg_md5_init`'s code as the internal `vg_md5_init_core`
(`Proof.Pbkdf2.Md.X86_64.Md5.hash`), which clears what it leaves itself. Their postconditions read the memory on
return only within the buffers (`X86_64.Scrub.PostOut`): the streaming state (`Stream.repr_congr`) and the digest.
-/

@[expose] public section

namespace VG.Proof.Md5.X86_64

open VG.Spec.Md5 VG.X86_64 VG.X86_64.Scrub

theorem initOut : PostOut (initContract X86_64.abi) (initSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Md5.initPost_out 64)

theorem updateOut (stack : Nat) : PostOut (updateContract X86_64.abi stack) (updateSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Md5.updatePost_out 64)

theorem finalizeOut (stack : Nat) : PostOut (finalizeContract X86_64.abi stack) (finalizeSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Md5.finalizePost_out 64)

/-! ## The registrations -/

/-- `vg_md5_update`'s code. -/
abbrev updateCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratch 56 .r8 Impl.Md5.X86_64.Stream.update

/-- `vg_md5_finalize`'s code. -/
abbrev finalizeCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratch 56 .rcx Impl.Md5.X86_64.Stream.finalize

/-! ## The functions as emitted -/

theorem init_codeSp : (Impl.Md5.X86_64.Stream.init).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Md5.initApi`'s function as emitted (`Impl.Md5.X86_64.Fn.init`) meets its contract in
constant time and returns without secret residue. -/
theorem init_scrubbed :
    VerifiedScrubbed target Impl.Md5.X86_64.Fn.init (Spec.Md5.initApi.contract X86_64.abi 0) 0 :=
  verifiedScrubbedSel (api := Spec.Md5.initApi)
    { code := Impl.Md5.X86_64.Stream.init
      verified := Shared.init
      spSafe := init_codeSp }
    .sse [] initOut (RScrub.pubOk_nil _) (by taint_decide)

theorem init_spSafe : Impl.Md5.X86_64.Fn.init.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe init_codeSp

theorem update_codeSp : (Impl.StackScratch.X86_64.withStackScratch 56 .r8 Impl.Md5.X86_64.Stream.update).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Md5.updateApi`'s function as emitted (`Impl.Md5.X86_64.Fn.update`) meets its contract in
constant time and returns without secret residue. -/
theorem update_scrubbed :
    VerifiedScrubbed target Impl.Md5.X86_64.Fn.update (Spec.Md5.updateApi.contract X86_64.abi 64) 0 :=
  verifiedScrubbedSel (api := Spec.Md5.updateApi)
    { code := updateCode
      stack := 8 + 56
      verified := Shared.update
      spSafe := update_codeSp }
    .sse [] (updateOut _) (RScrub.pubOk_nil _) (by taint_decide)

theorem update_spSafe : Impl.Md5.X86_64.Fn.update.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe update_codeSp

theorem finalize_codeSp : (Impl.StackScratch.X86_64.withStackScratch 56 .rcx Impl.Md5.X86_64.Stream.finalize).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Md5.finalizeApi`'s function as emitted (`Impl.Md5.X86_64.Fn.finalize`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize_scrubbed :
    VerifiedScrubbed target Impl.Md5.X86_64.Fn.finalize (Spec.Md5.finalizeApi.contract X86_64.abi 64) 0 :=
  verifiedScrubbedSel (api := Spec.Md5.finalizeApi)
    { code := finalizeCode
      stack := 8 + 56
      verified := Shared.finalize
      spSafe := finalize_codeSp }
    .sse [] (finalizeOut _) (RScrub.pubOk_nil _) (by taint_decide)

theorem finalize_spSafe : Impl.Md5.X86_64.Fn.finalize.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe finalize_codeSp
end VG.Proof.Md5.X86_64
