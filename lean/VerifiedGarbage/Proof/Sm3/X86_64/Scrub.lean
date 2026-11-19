module

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

def initKs : List Nat := keep_for% Spec.Sm3.initApi.sig (0) Impl.Sm3.X86_64.Stream.init []

theorem initOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sm3.initApi.sig (0) []) Impl.Sm3.X86_64.Stream.init
      h).any (RScrub.resOkB · (0) initKs (Impl.Scrub.X86_64.chunks (0))) = true :=
  RScrub.Analysed.ok_of initKs (by taint_decide)

def updateKs : List Nat := keep_for% Spec.Sm3.updateApi.sig (8 + 168) updateCode []

theorem updateOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sm3.updateApi.sig (8 + 168) []) updateCode
      h).any (RScrub.resOkB · (8 + 168) updateKs (Impl.Scrub.X86_64.chunks (8 + 168))) = true :=
  RScrub.Analysed.ok_of updateKs (by taint_decide)

def finalizeKs : List Nat := keep_for% Spec.Sm3.finalizeApi.sig (8 + 168) finalizeCode []

theorem finalizeOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sm3.finalizeApi.sig (8 + 168) []) finalizeCode
      h).any (RScrub.resOkB · (8 + 168) finalizeKs (Impl.Scrub.X86_64.chunks (8 + 168))) = true :=
  RScrub.Analysed.ok_of finalizeKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_sm3_init`. -/
def initReg : Registration Spec.Sm3.initApi X86_64.target :=
  scrubOf { code := Impl.Sm3.X86_64.Stream.init, verified := Shared.init } .sse false [.r11] initOut [] (pubOk_nil _)
    ⟨initKs, initOk⟩
    (by dsimp only [VG.X86_64.Scrub.retBitsOf]; lit_decide)

open VG.X86_64.RScrub in
/-- `vg_sm3_update`. -/
def updateReg : Registration Spec.Sm3.updateApi X86_64.target :=
  scrubOf {
    code := updateCode
    stack := 8 + 168
    verified := Shared.update } .sse false [.rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] (updateOut _) [] (pubOk_nil _) ⟨updateKs, updateOk⟩
    (by dsimp only [VG.X86_64.Scrub.retBitsOf]; lit_decide)

open VG.X86_64.RScrub in
/-- `vg_sm3_finalize`. -/
def finalizeReg : Registration Spec.Sm3.finalizeApi X86_64.target :=
  scrubOf {
    code := finalizeCode
    stack := 8 + 168
    verified := Shared.finalize } .sse true [.rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] (finalizeOut _) [] (pubOk_nil _) ⟨finalizeKs, finalizeOk⟩
    (by dsimp only [VG.X86_64.Scrub.retBitsOf]; lit_decide)

end VG.Proof.Sm3.X86_64
