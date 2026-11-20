module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFn
public import VerifiedGarbage.Impl.Blake2.X86_64.Fn
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Proof.Blake2.X86_64.Backend
public import VerifiedGarbage.Proof.Blake2.X86_64.BackendS
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified
import VerifiedGarbage.Proof.Blake2.Scratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.CT
meta import VerifiedGarbage.Proof.Blake2.X86_64.Backend
meta import VerifiedGarbage.Proof.Blake2.X86_64.BackendS
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Framework.X86_64.Registration
meta import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified
meta import VerifiedGarbage.Proof.Blake2.Scratch
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Blake2.X86_64.Stream.CT
import VerifiedGarbage.Proof.Blake2.PostOut
meta import VerifiedGarbage.Proof.Blake2.PostOut

/-!
# BLAKE2b's and BLAKE2s's streaming functions on x86-64, without secret residue

`vg_blake2b_init` and `vg_blake2s_init`, and `vg_blake2b_update`, `vg_blake2b_finalize` and BLAKE2s's, over each backend,
each followed by `Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`)
where the backend gives the residue analysis of its code
(`Backend.updateRes`, `Backend.finalizeRes`). Their postconditions read the
memory on return only within the buffers (`X86_64.Scrub.PostOut`): the
streaming state (`repr_congr'`) and the digest (`bytesAt_congr`).
Argon2 calls `vg_blake2b_init`'s code as the internal `vg_blake2b_init_core`
(`Proof.Argon2.X86_64.HPrime.hash`).
-/

@[expose] public section

namespace VG.Proof.Blake2.X86_64

open VG.X86_64 VG.X86_64.Scrub

theorem updateBOut (stack : Nat) :
    PostOut (Spec.Blake2.updateBContract X86_64.abi stack) (Spec.Blake2.updateBSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (updateBPost_out 64)

theorem finalizeBOut (stack : Nat) :
    PostOut (Spec.Blake2.finalizeBContract X86_64.abi stack) (Spec.Blake2.finalizeBSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (finalizeBPost_out 64)

theorem updateSOut (stack : Nat) :
    PostOut (Spec.Blake2.updateSContract X86_64.abi stack) (Spec.Blake2.updateSSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (updateSPost_out 64)

theorem finalizeSOut (stack : Nat) :
    PostOut (Spec.Blake2.finalizeSContract X86_64.abi stack) (Spec.Blake2.finalizeSSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (finalizeSPost_out 64)

theorem initBOut : PostOut (Spec.Blake2.initBContract X86_64.abi) (Spec.Blake2.initBSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.initBPost_out 64)

theorem initSOut : PostOut (Spec.Blake2.initSContract X86_64.abi) (Spec.Blake2.initSSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.initSPost_out 64)

/-! ## The registrations -/

open VG.X86_64.RScrub in
/-- `vg_blake2b_update` over the backend `v`: without secret residue where `v`
gives its analysis (`Backend.updateRes`). -/
def updateBReg (v : Backend) : Registration Spec.Blake2.updateBApi X86_64.target :=
  withScrub {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 584 .r8 v.update
    stack := 8 + 584
    notWith := v.notWith
    verified := v.update_framed
    spSafe := X86_64.withStackScratch_spSafe_of v.updateSpSafe } (updateBOut _) [] (pubOk_nil _)
    v.updateRes

open VG.X86_64.RScrub in
/-- `vg_blake2b_finalize` over the backend `v` (`Backend.finalizeRes`). -/
def finalizeBReg (v : Backend) : Registration Spec.Blake2.finalizeBApi X86_64.target :=
  withScrub {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 584 .rcx v.finalize
    stack := 8 + 584
    notWith := v.notWith
    verified := v.finalize_framed
    spSafe := X86_64.withStackScratch_spSafe_of v.finalizeSpSafe } (finalizeBOut _) [] (pubOk_nil _)
    v.finalizeRes

open VG.X86_64.RScrub in
/-- `vg_blake2s_update` over the backend `v` (`BackendS.updateRes`). -/
def updateSReg (v : BackendS) : Registration Spec.Blake2.updateSApi X86_64.target :=
  withScrub {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 584 .r8 v.update
    stack := 8 + 584
    notWith := v.notWith
    verified := v.update_framed
    spSafe := X86_64.withStackScratch_spSafe_of v.updateSpSafe } (updateSOut _) [] (pubOk_nil _)
    v.updateRes

open VG.X86_64.RScrub in
/-- `vg_blake2s_finalize` over the backend `v` (`BackendS.finalizeRes`). -/
def finalizeSReg (v : BackendS) : Registration Spec.Blake2.finalizeSApi X86_64.target :=
  withScrub {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 584 .rcx v.finalize
    stack := 8 + 584
    notWith := v.notWith
    verified := v.finalize_framed
    spSafe := X86_64.withStackScratch_spSafe_of v.finalizeSpSafe } (finalizeSOut _) [] (pubOk_nil _)
    v.finalizeRes

/-! ## The functions as emitted -/

theorem initB_codeSp : (Impl.Blake2.X86_64.Stream.init Spec.Blake2.b).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Blake2.initBApi`'s function as emitted (`Impl.Blake2.X86_64.Fn.initB`) meets its contract in
constant time and returns without secret residue. -/
theorem initB_scrubbed :
    VerifiedScrubbed target Impl.Blake2.X86_64.Fn.initB (Spec.Blake2.initBApi.contract X86_64.abi 0) 0 :=
  verifiedScrubbedSel (api := Spec.Blake2.initBApi)
    { code := Impl.Blake2.X86_64.Stream.init Spec.Blake2.b
      verified := Proof.Blake2.X86_64.Stream.initB_verified
      spSafe := initB_codeSp }
    .sse [] initBOut (RScrub.pubOk_nil _) (by taint_decide)

theorem initB_spSafe : Impl.Blake2.X86_64.Fn.initB.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe initB_codeSp

theorem initS_codeSp : (Impl.Blake2.X86_64.Stream.init Spec.Blake2.s).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Blake2.initSApi`'s function as emitted (`Impl.Blake2.X86_64.Fn.initS`) meets its contract in
constant time and returns without secret residue. -/
theorem initS_scrubbed :
    VerifiedScrubbed target Impl.Blake2.X86_64.Fn.initS (Spec.Blake2.initSApi.contract X86_64.abi 0) 0 :=
  verifiedScrubbedSel (api := Spec.Blake2.initSApi)
    { code := Impl.Blake2.X86_64.Stream.init Spec.Blake2.s
      verified := Proof.Blake2.X86_64.Stream.initS_verified
      spSafe := initS_codeSp }
    .sse [] initSOut (RScrub.pubOk_nil _) (by taint_decide)

theorem initS_spSafe : Impl.Blake2.X86_64.Fn.initS.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe initS_codeSp
end VG.Proof.Blake2.X86_64
