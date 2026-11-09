module

public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Spec.Poly1305.Contract
public import VerifiedGarbage.Impl.Poly1305.X86_64.Callee
public import VerifiedGarbage.Impl.Poly1305.X86_64
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Poly1305.X86_64.Lit
public meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public meta import VerifiedGarbage.Spec.Poly1305.Contract
public meta import VerifiedGarbage.Impl.Poly1305.X86_64.Callee
public meta import VerifiedGarbage.Impl.Poly1305.X86_64
public meta import VerifiedGarbage.Impl.StackScratch.X86_64
public meta import VerifiedGarbage.Proof.Poly1305.X86_64.Lit

-- separate module: the residue analysis of `vg_poly1305_update`, which `Variant.lean` gives the
-- scalar implementation, without importing the analysis's tactics into every Poly1305 proof

/-!
# The residue analysis of `vg_poly1305_update` on x86-64

`vg_poly1305_update` over the implementation of `vg_poly1305_blocks` with
code `code` and symbol `name` (its code, `updateCode`), analysed for what it
may leave of secrets (`X86_64.RScrub.Analysed`), for an implementation the
analysis handles: the scalar one (`scalarUpdate`). The vector ones load
MXCSR (`ldmxcsr`), which the analysis does not follow.
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64

open VG.X86_64

/-- `vg_poly1305_update`'s code over `name` and `code`. -/
abbrev updateCode (name : String) (code : Prog isa) : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratch 136 .r8 (Impl.Poly1305.X86_64.update name code)

/-- The granules `scalarUpdate` wipes. -/
def scalarUpdateKs : List Nat := keep_for% Spec.Poly1305.updateApi.sig 160
  (updateCode (Impl.Poly1305.X86_64.Blocks.name .scalar) (Impl.Poly1305.X86_64.Blocks.code .scalar)) []

theorem scalarUpdate_ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Poly1305.updateApi.sig 160 [])
      (updateCode (Impl.Poly1305.X86_64.Blocks.name .scalar) (Impl.Poly1305.X86_64.Blocks.code .scalar))
      h).any (RScrub.resOkB · 160 scalarUpdateKs (Impl.Scrub.X86_64.chunks 160)) = true :=
  RScrub.Analysed.ok_of scalarUpdateKs (by taint_decide)

/-- The analysis of `vg_poly1305_update` over the scalar `vg_poly1305_blocks`. -/
def scalarUpdate : RScrub.Analysed Spec.Poly1305.updateApi.sig 160 []
    (updateCode (Impl.Poly1305.X86_64.Blocks.name .scalar) (Impl.Poly1305.X86_64.Blocks.code .scalar)) :=
  ⟨scalarUpdateKs, scalarUpdate_ok⟩

end VG.Proof.Poly1305.X86_64
