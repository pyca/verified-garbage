module

public import VerifiedGarbage.Spec.Rc2.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Frame
import VerifiedGarbage.Proof.Rc2.Scratch
import VerifiedGarbage.Proof.Rc2.X86_64.Lit
import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Lit
meta import VerifiedGarbage.Spec.Rc2.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Frame
meta import VerifiedGarbage.Proof.Rc2.Scratch
meta import VerifiedGarbage.Proof.Rc2.X86_64.Lit
meta import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Lit

/-!
# RC2 on x86-64, without secret residue

`vg_rc2_cbc_init`, followed by `Impl.Scrub.X86_64.scrubTail`
(`X86_64.Scrub.withScrub`), which clears the registers and the granules of
its stack that the residue analysis (`X86_64.RTaint`) finds may hold secrets.
Its postcondition reads the memory on return only within the context
(`X86_64.Scrub.PostOut`), as its frame already shows
(`X86_64.Verified.stackArgScratchWiped`'s `hpost`).

The CBC functions are not here yet: they call the block functions by name.
-/

@[expose] public section

namespace VG.Proof.Rc2.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub

/-! ## Postconditions -/

theorem cbcInitOut : PostOut (Spec.Rc2.cbcInitContract X86_64.abi 600) (Spec.Rc2.cbcInitSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Rc2.cbcInitPostOut_local _)

/-! ## The registrations -/

/-- `vg_rc2_cbc_init`'s code. -/
abbrev cbcInitCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackArgScratchWiped 592 0 72 Impl.Rc2.X86_64.Stream.init

def cbcInitKs : List Nat := keep_for% Spec.Rc2.cbcInitApi.sig 600 cbcInitCode []

theorem cbcInitOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Rc2.cbcInitApi.sig 600 []) cbcInitCode
      h).any (RScrub.resOkB · 600 cbcInitKs (Impl.Scrub.X86_64.chunks 600)) = true :=
  RScrub.Analysed.ok_of cbcInitKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_rc2_cbc_init`. -/
def cbcInitReg : Registration Spec.Rc2.cbcInitApi X86_64.target :=
  withScrub {
    code := cbcInitCode
    stack := 600
    verified := Proof.Rc2.X86_64.Stream.init_framed } cbcInitOut [] (pubOk_nil _) (some ⟨cbcInitKs, cbcInitOk⟩)

end VG.Proof.Rc2.X86_64.Scrub
