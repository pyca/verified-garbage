module

public import VerifiedGarbage.Proof.Poly1305.X86_64.Init
public import VerifiedGarbage.Proof.Poly1305.X86_64.Frame
public import VerifiedGarbage.Proof.Poly1305.X86_64.UpdateVerified
public import VerifiedGarbage.Proof.Poly1305.X86_64.Variant
public import VerifiedGarbage.Proof.Poly1305.X86_64.ScrubPost
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Poly1305.X86_64.Lit
public meta import VerifiedGarbage.Proof.Poly1305.X86_64.Init
public meta import VerifiedGarbage.Proof.Poly1305.X86_64.Frame
public meta import VerifiedGarbage.Proof.Poly1305.X86_64.UpdateVerified
public meta import VerifiedGarbage.Proof.Poly1305.X86_64.Variant
public meta import VerifiedGarbage.Proof.Poly1305.X86_64.ScrubPost
public meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public meta import VerifiedGarbage.Proof.Framework.Registration
public meta import VerifiedGarbage.Proof.Framework.X86_64.Registration
public meta import VerifiedGarbage.Proof.Poly1305.X86_64.Lit

/-!
# Experiment: Poly1305 without secret residue (x86-64)

`vg_poly1305_init`, `vg_poly1305_update` (the scalar implementation) and
`vg_poly1305_finalize`, scrubbed (`X86_64.Scrub.scrubReg`, with the
granules the residue analysis selects), named with `_scrub`, so that they
are emitted next to the functions they scrub, for measuring.
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64.ScrubExp

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64 VG.X86_64.RScrub

def initR : Registration Spec.Poly1305.initApi X86_64.target where
  suffix := "_scrub"
  code := Impl.Poly1305.X86_64.init
  verified := Proof.Poly1305.X86_64.init_verified

def updR : Registration Spec.Poly1305.updateApi X86_64.target where
  suffix := "_scrub"
  code := Impl.StackScratch.X86_64.withStackScratch 136 .r8 (Impl.Poly1305.X86_64.update Proof.Poly1305.X86_64.BlocksImpl.scalar.name Proof.Poly1305.X86_64.BlocksImpl.scalar.code)
  stack := 160
  verified := Proof.Poly1305.X86_64.update_framed Proof.Poly1305.X86_64.BlocksImpl.scalar
  spSafe := X86_64.withStackScratch_spSafe_of (Proof.Poly1305.X86_64.update_spSafe Proof.Poly1305.X86_64.BlocksImpl.scalar)

def finR : Registration Spec.Poly1305.finalizeApi X86_64.target where
  suffix := "_scrub"
  code := Impl.StackScratch.X86_64.withStackScratch 136 .rcx Impl.Poly1305.X86_64.finalize
  stack := 136
  verified := Proof.Poly1305.X86_64.finalize_framed

def initKs : List Nat := keep_for% Spec.Poly1305.initApi.sig initR.stack initR.code
def updKs : List Nat := keep_for% Spec.Poly1305.updateApi.sig updR.stack updR.code
def finKs : List Nat := keep_for% Spec.Poly1305.finalizeApi.sig finR.stack finR.code

theorem initRes : ResOk initR.code initR.contract initR.stack initKs (chunks initR.stack) :=
  resOk_reg initR initKs (by taint_decide)
theorem updRes : ResOk updR.code updR.contract updR.stack updKs (chunks updR.stack) :=
  resOk_reg updR updKs (by taint_decide)
theorem finRes : ResOk finR.code finR.contract finR.stack finKs (chunks finR.stack) :=
  resOk_reg finR finKs (by taint_decide)

def init := scrubReg initR .sse initKs (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
  (initOut _) initRes rfl
def update := scrubReg updR .sse updKs (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
  (updateOut _) updRes rfl
def finalize := scrubReg finR .sse finKs (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
  (finalizeOut _) finRes rfl

theorem init_noResidue : NoResidue init.code initR.contract (Spec.Poly1305.initSig.retBits 64) :=
  scrubReg_noResidue initR .sse initKs _ _ _ _ _ _ initRes rfl
theorem update_noResidue : NoResidue update.code updR.contract (Spec.Poly1305.updateSig.retBits 64) :=
  scrubReg_noResidue updR .sse updKs _ _ _ _ _ _ updRes rfl
theorem finalize_noResidue : NoResidue finalize.code finR.contract (Spec.Poly1305.finalizeSig.retBits 64) :=
  scrubReg_noResidue finR .sse finKs _ _ _ _ _ _ finRes rfl

end VG.Proof.Poly1305.X86_64.ScrubExp
