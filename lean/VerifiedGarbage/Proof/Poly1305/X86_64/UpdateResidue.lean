module

public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueMx
public import VerifiedGarbage.Proof.Mcdt.X86_64.Op
public import VerifiedGarbage.Spec.Poly1305.Contract
public import VerifiedGarbage.Impl.Poly1305.X86_64.Callee
public import VerifiedGarbage.Impl.Poly1305.X86_64
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Poly1305.X86_64.Lit
public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Lit
public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Lit
public import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Lit
public meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueMx
public meta import VerifiedGarbage.Proof.Mcdt.X86_64.Op
public meta import VerifiedGarbage.Spec.Poly1305.Contract
public meta import VerifiedGarbage.Impl.Poly1305.X86_64.Callee
public meta import VerifiedGarbage.Impl.Poly1305.X86_64
public meta import VerifiedGarbage.Impl.StackScratch.X86_64
public meta import VerifiedGarbage.Proof.Poly1305.X86_64.Lit
public meta import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Lit
public meta import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Lit
public meta import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Lit

-- separate module: the residue analysis of `vg_poly1305_update`, which `Variant.lean` gives the
-- scalar implementation, without importing the analysis's tactics into every Poly1305 proof

/-!
# The residue analysis of `vg_poly1305_update` on x86-64

`vg_poly1305_update` over the implementation of `vg_poly1305_blocks` with
code `code` and symbol `name` (its code, `updateCode`), analysed for what it
may leave of secrets (`X86_64.RScrub.AnalysedOps`, with MXCSR the same in
both runs and a call of `vg_mcdt_enter` as an operation, `enterOpR`): over
each implementation, whose stores the analysis places in the state, the
frame of saved registers, or the stack below. -/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64

open VG.X86_64

/-- `vg_poly1305_update`'s code over `name` and `code`. -/
abbrev updateCode (name : String) (code : Prog isa) : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratch 136 .r8 (Impl.Poly1305.X86_64.update name code)

/-- The granules `scalarUpdate` wipes. -/
def scalarUpdateKs : List Nat := keep_for_ops% Spec.Poly1305.updateApi.sig 160
  (updateCode (Impl.Poly1305.X86_64.Blocks.name .scalar) (Impl.Poly1305.X86_64.Blocks.code .scalar)) [Mcdt.X86_64.enterOpR]

theorem scalarUpdate_okF : VG.Taint.OpsCheck rtaintMx [Mcdt.X86_64.enterOpR] (RScrub.init Spec.Poly1305.updateApi.sig 160 [])
    (updateCode (Impl.Poly1305.X86_64.Blocks.name .scalar) (Impl.Poly1305.X86_64.Blocks.code .scalar))
    (RScrub.resOkF · 160 scalarUpdateKs (Impl.Scrub.X86_64.chunks 160)) := by
  taint_decide_ops_check

/-- The analysis of `vg_poly1305_update` over `vg_poly1305_blocks`. -/
def scalarUpdate : RScrub.AnalysedOps Spec.Poly1305.updateApi.sig 160 []
    (updateCode (Impl.Poly1305.X86_64.Blocks.name .scalar) (Impl.Poly1305.X86_64.Blocks.code .scalar)) :=
  ⟨scalarUpdateKs, [Mcdt.X86_64.enterOpR], ⟨Mcdt.X86_64.enterOpR_sound, trivial⟩,
    let ⟨h, h₁, h₂⟩ := scalarUpdate_okF; ⟨h, RScrub.any_resOkB h₁, h₂⟩⟩

/-- The granules `avx2Update` wipes. -/
def avx2UpdateKs : List Nat := keep_for_ops% Spec.Poly1305.updateApi.sig 160
  (updateCode (Impl.Poly1305.X86_64.Blocks.name .avx2) (Impl.Poly1305.X86_64.Blocks.code .avx2)) [Mcdt.X86_64.enterOpR]

theorem avx2Update_okF : VG.Taint.OpsCheck rtaintMx [Mcdt.X86_64.enterOpR] (RScrub.init Spec.Poly1305.updateApi.sig 160 [])
    (updateCode (Impl.Poly1305.X86_64.Blocks.name .avx2) (Impl.Poly1305.X86_64.Blocks.code .avx2))
    (RScrub.resOkF · 160 avx2UpdateKs (Impl.Scrub.X86_64.chunks 160)) := by
  taint_decide_ops_check

/-- The analysis of `vg_poly1305_update` over `vg_poly1305_blocks_avx2`. -/
def avx2Update : RScrub.AnalysedOps Spec.Poly1305.updateApi.sig 160 []
    (updateCode (Impl.Poly1305.X86_64.Blocks.name .avx2) (Impl.Poly1305.X86_64.Blocks.code .avx2)) :=
  ⟨avx2UpdateKs, [Mcdt.X86_64.enterOpR], ⟨Mcdt.X86_64.enterOpR_sound, trivial⟩,
    let ⟨h, h₁, h₂⟩ := avx2Update_okF; ⟨h, RScrub.any_resOkB h₁, h₂⟩⟩

/-- The granules `avx512Update` wipes. -/
def avx512UpdateKs : List Nat := keep_for_ops% Spec.Poly1305.updateApi.sig 160
  (updateCode (Impl.Poly1305.X86_64.Blocks.name .avx512) (Impl.Poly1305.X86_64.Blocks.code .avx512)) [Mcdt.X86_64.enterOpR]

theorem avx512Update_okF : VG.Taint.OpsCheck rtaintMx [Mcdt.X86_64.enterOpR] (RScrub.init Spec.Poly1305.updateApi.sig 160 [])
    (updateCode (Impl.Poly1305.X86_64.Blocks.name .avx512) (Impl.Poly1305.X86_64.Blocks.code .avx512))
    (RScrub.resOkF · 160 avx512UpdateKs (Impl.Scrub.X86_64.chunks 160)) := by
  taint_decide_ops_check

/-- The analysis of `vg_poly1305_update` over `vg_poly1305_blocks_avx512`. -/
def avx512Update : RScrub.AnalysedOps Spec.Poly1305.updateApi.sig 160 []
    (updateCode (Impl.Poly1305.X86_64.Blocks.name .avx512) (Impl.Poly1305.X86_64.Blocks.code .avx512)) :=
  ⟨avx512UpdateKs, [Mcdt.X86_64.enterOpR], ⟨Mcdt.X86_64.enterOpR_sound, trivial⟩,
    let ⟨h, h₁, h₂⟩ := avx512Update_okF; ⟨h, RScrub.any_resOkB h₁, h₂⟩⟩

/-- The granules `ifmaUpdate` wipes. -/
def ifmaUpdateKs : List Nat := keep_for_ops% Spec.Poly1305.updateApi.sig 160
  (updateCode (Impl.Poly1305.X86_64.Blocks.name .ifma) (Impl.Poly1305.X86_64.Blocks.code .ifma)) [Mcdt.X86_64.enterOpR]

theorem ifmaUpdate_okF : VG.Taint.OpsCheck rtaintMx [Mcdt.X86_64.enterOpR] (RScrub.init Spec.Poly1305.updateApi.sig 160 [])
    (updateCode (Impl.Poly1305.X86_64.Blocks.name .ifma) (Impl.Poly1305.X86_64.Blocks.code .ifma))
    (RScrub.resOkF · 160 ifmaUpdateKs (Impl.Scrub.X86_64.chunks 160)) := by
  taint_decide_ops_check

/-- The analysis of `vg_poly1305_update` over `vg_poly1305_blocks_ifma`. -/
def ifmaUpdate : RScrub.AnalysedOps Spec.Poly1305.updateApi.sig 160 []
    (updateCode (Impl.Poly1305.X86_64.Blocks.name .ifma) (Impl.Poly1305.X86_64.Blocks.code .ifma)) :=
  ⟨ifmaUpdateKs, [Mcdt.X86_64.enterOpR], ⟨Mcdt.X86_64.enterOpR_sound, trivial⟩,
    let ⟨h, h₁, h₂⟩ := ifmaUpdate_okF; ⟨h, RScrub.any_resOkB h₁, h₂⟩⟩

end VG.Proof.Poly1305.X86_64
