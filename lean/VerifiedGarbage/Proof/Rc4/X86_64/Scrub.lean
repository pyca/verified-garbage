module

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

def initKs : List Nat := keep_for% Spec.Rc4.initApi.sig 0 initCode []

theorem initOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Rc4.initApi.sig 0 []) initCode
      h).any (RScrub.resOkB · 0 initKs (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of initKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_rc4_init`. -/
def initReg : Registration Spec.Rc4.initApi X86_64.target :=
  withScrub {
    code := initCode
    verified := Proof.Rc4.X86_64.init_verified } initOut [] (pubOk_nil _) (some ⟨initKs, initOk⟩)

/-- `vg_rc4_apply`, whose leak the residue analysis does not follow: with no
stack, the registers alone cleared (`Scrub.withScrubAll`). -/
def applyReg : Registration Spec.Rc4.applyApi X86_64.target :=
  withScrubAll {
    code := Impl.Rc4.X86_64.apply
    verified := Proof.Rc4.X86_64.apply_verified } applyOut

end VG.Proof.Rc4.X86_64.Scrub
