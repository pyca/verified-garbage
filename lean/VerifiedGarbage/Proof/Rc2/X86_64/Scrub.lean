module

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

/-- `vg_rc2_cbc_encrypt_chained`'s code. -/
abbrev cbcEncryptChainedCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 520 .r8 64 Impl.Rc2.X86_64.Cbc.encrypt

/-- `vg_rc2_cbc_decrypt_chained`'s code. -/
abbrev cbcDecryptChainedCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 520 .r8 64 Impl.Rc2.X86_64.Cbc.decrypt

def cbcEncryptChainedKs : List Nat := keep_for% Spec.Rc2.cbcEncryptChainedApi.sig 528 cbcEncryptChainedCode []

theorem cbcEncryptChainedOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Rc2.cbcEncryptChainedApi.sig 528 []) cbcEncryptChainedCode
      h).any (RScrub.resOkB · 528 cbcEncryptChainedKs (Impl.Scrub.X86_64.chunks 528)) = true :=
  RScrub.Analysed.ok_of cbcEncryptChainedKs (by taint_decide)

def cbcDecryptChainedKs : List Nat := keep_for% Spec.Rc2.cbcDecryptChainedApi.sig 528 cbcDecryptChainedCode []

theorem cbcDecryptChainedOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Rc2.cbcDecryptChainedApi.sig 528 []) cbcDecryptChainedCode
      h).any (RScrub.resOkB · 528 cbcDecryptChainedKs (Impl.Scrub.X86_64.chunks 528)) = true :=
  RScrub.Analysed.ok_of cbcDecryptChainedKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_rc2_cbc_encrypt_chained`. -/
def cbcEncryptChainedReg : Registration Spec.Rc2.cbcEncryptChainedApi X86_64.target :=
  withScrub {
    code := cbcEncryptChainedCode
    stack := 528
    verified := Proof.Rc2.X86_64.Cbc.encryptChained_framed } cbcEncryptChainedOut [] (pubOk_nil _)
    (some ⟨cbcEncryptChainedKs, cbcEncryptChainedOk⟩)

open VG.X86_64.RScrub in
/-- `vg_rc2_cbc_decrypt_chained`. -/
def cbcDecryptChainedReg : Registration Spec.Rc2.cbcDecryptChainedApi X86_64.target :=
  withScrub {
    code := cbcDecryptChainedCode
    stack := 528
    verified := Proof.Rc2.X86_64.Cbc.decryptChained_framed } cbcDecryptChainedOut [] (pubOk_nil _)
    (some ⟨cbcDecryptChainedKs, cbcDecryptChainedOk⟩)

end VG.Proof.Rc2.X86_64.Scrub
