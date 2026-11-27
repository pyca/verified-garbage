module

public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueMx
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
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
public meta import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
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
may leave of secrets (with MXCSR the same in both runs and a call of
`vg_mcdt_enter` as an operation, `enterOpR`): over each implementation,
whose stores the analysis places in the state, the frame of saved
registers, or the stack below. `UpdScrub` is what its cleanup,
`Impl.Poly1305.X86_64.Fn.update`, needs of each: the level of its vector
registers, the runs of granules it wipes (none: no implementation leaves a
secret on the stack), the analysis, and the cleanup's other conditions
(`X86_64.Scrub.scrubSideG`), each evaluated once, here. -/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64

open VG.X86_64

/-- `vg_poly1305_update`'s code over `name` and `code`. -/
abbrev updateCode (name : String) (code : Prog isa) : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratch 136 .r8 (Impl.Poly1305.X86_64.update name code)

/-- What the cleanup of `vg_poly1305_update` over `name` and `code`
(`Impl.Poly1305.X86_64.Fn.update`) needs of it. -/
structure UpdScrub (name : String) (code : Prog isa) where
  /-- The level of its vector registers. -/
  level : Impl.Scrub.X86_64.VecLevel
  /-- The runs of granules that may hold secrets. -/
  runs : List (Nat × Nat)
  /-- The residue analysis, ending with secrets only in `runs`. -/
  ok : ∃ ops : List (VG.Taint.Op isa RTaint.FT), VG.Taint.AllSound rtaintMx ops ∧
    VG.Taint.OpsCheck rtaintMx ops (RScrub.init Spec.Poly1305.updateApi.sig 160 []) (updateCode name code)
      (RScrub.resOkB · 160 (Impl.Scrub.X86_64.runKs runs) (Impl.Scrub.X86_64.chunksA 160))
  /-- The cleanup's other conditions. -/
  side : Scrub.scrubSideG (updateCode name code) 160 0 level true (Impl.Scrub.X86_64.runKs runs)
    (Impl.Scrub.X86_64.chunksA 160) (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs runs)) [] = true

theorem scalarUpdate_okF : VG.Taint.OpsCheck rtaintMx [Mcdt.X86_64.enterOpR] (RScrub.init Spec.Poly1305.updateApi.sig 160 [])
    (updateCode (Impl.Poly1305.X86_64.Blocks.name .scalar) (Impl.Poly1305.X86_64.Blocks.code .scalar))
    (RScrub.resOkF · 160 [] (Impl.Scrub.X86_64.chunksA 160)) := by
  taint_decide_ops_check

theorem scalarUpdate_side : Scrub.scrubSideG (updateCode (Impl.Poly1305.X86_64.Blocks.name .scalar) (Impl.Poly1305.X86_64.Blocks.code .scalar)) 160 0 .sse true []
    (Impl.Scrub.X86_64.chunksA 160) (Impl.Scrub.X86_64.gsAll []) [] = true := by
  lit_decide

/-- The cleanup of `vg_poly1305_update` over `vg_poly1305_blocks`. -/
def scalarUpdate : UpdScrub (Impl.Poly1305.X86_64.Blocks.name .scalar) (Impl.Poly1305.X86_64.Blocks.code .scalar) where
  level := .sse
  runs := []
  ok := ⟨[Mcdt.X86_64.enterOpR], ⟨Mcdt.X86_64.enterOpR_sound, trivial⟩,
    let ⟨h, h₁, h₂⟩ := scalarUpdate_okF; ⟨h, RScrub.any_resOkB h₁, h₂⟩⟩
  side := scalarUpdate_side

theorem avx2Update_okF : VG.Taint.OpsCheck rtaintMx [Mcdt.X86_64.enterOpR] (RScrub.init Spec.Poly1305.updateApi.sig 160 [])
    (updateCode (Impl.Poly1305.X86_64.Blocks.name .avx2) (Impl.Poly1305.X86_64.Blocks.code .avx2))
    (RScrub.resOkF · 160 [] (Impl.Scrub.X86_64.chunksA 160)) := by
  taint_decide_ops_check

theorem avx2Update_side : Scrub.scrubSideG (updateCode (Impl.Poly1305.X86_64.Blocks.name .avx2) (Impl.Poly1305.X86_64.Blocks.code .avx2)) 160 0 .avx true []
    (Impl.Scrub.X86_64.chunksA 160) (Impl.Scrub.X86_64.gsAll []) [] = true := by
  lit_decide

/-- The cleanup of `vg_poly1305_update` over `vg_poly1305_blocks_avx2`. -/
def avx2Update : UpdScrub (Impl.Poly1305.X86_64.Blocks.name .avx2) (Impl.Poly1305.X86_64.Blocks.code .avx2) where
  level := .avx
  runs := []
  ok := ⟨[Mcdt.X86_64.enterOpR], ⟨Mcdt.X86_64.enterOpR_sound, trivial⟩,
    let ⟨h, h₁, h₂⟩ := avx2Update_okF; ⟨h, RScrub.any_resOkB h₁, h₂⟩⟩
  side := avx2Update_side

theorem avx512Update_okF : VG.Taint.OpsCheck rtaintMx [Mcdt.X86_64.enterOpR] (RScrub.init Spec.Poly1305.updateApi.sig 160 [])
    (updateCode (Impl.Poly1305.X86_64.Blocks.name .avx512) (Impl.Poly1305.X86_64.Blocks.code .avx512))
    (RScrub.resOkF · 160 [] (Impl.Scrub.X86_64.chunksA 160)) := by
  taint_decide_ops_check

theorem avx512Update_side : Scrub.scrubSideG (updateCode (Impl.Poly1305.X86_64.Blocks.name .avx512) (Impl.Poly1305.X86_64.Blocks.code .avx512)) 160 0 .avx true []
    (Impl.Scrub.X86_64.chunksA 160) (Impl.Scrub.X86_64.gsAll []) [] = true := by
  lit_decide

/-- The cleanup of `vg_poly1305_update` over `vg_poly1305_blocks_avx512`. -/
def avx512Update : UpdScrub (Impl.Poly1305.X86_64.Blocks.name .avx512) (Impl.Poly1305.X86_64.Blocks.code .avx512) where
  level := .avx
  runs := []
  ok := ⟨[Mcdt.X86_64.enterOpR], ⟨Mcdt.X86_64.enterOpR_sound, trivial⟩,
    let ⟨h, h₁, h₂⟩ := avx512Update_okF; ⟨h, RScrub.any_resOkB h₁, h₂⟩⟩
  side := avx512Update_side

theorem ifmaUpdate_okF : VG.Taint.OpsCheck rtaintMx [Mcdt.X86_64.enterOpR] (RScrub.init Spec.Poly1305.updateApi.sig 160 [])
    (updateCode (Impl.Poly1305.X86_64.Blocks.name .ifma) (Impl.Poly1305.X86_64.Blocks.code .ifma))
    (RScrub.resOkF · 160 [] (Impl.Scrub.X86_64.chunksA 160)) := by
  taint_decide_ops_check

theorem ifmaUpdate_side : Scrub.scrubSideG (updateCode (Impl.Poly1305.X86_64.Blocks.name .ifma) (Impl.Poly1305.X86_64.Blocks.code .ifma)) 160 0 .avx true []
    (Impl.Scrub.X86_64.chunksA 160) (Impl.Scrub.X86_64.gsAll []) [] = true := by
  lit_decide

/-- The cleanup of `vg_poly1305_update` over `vg_poly1305_blocks_ifma`. -/
def ifmaUpdate : UpdScrub (Impl.Poly1305.X86_64.Blocks.name .ifma) (Impl.Poly1305.X86_64.Blocks.code .ifma) where
  level := .avx
  runs := []
  ok := ⟨[Mcdt.X86_64.enterOpR], ⟨Mcdt.X86_64.enterOpR_sound, trivial⟩,
    let ⟨h, h₁, h₂⟩ := ifmaUpdate_okF; ⟨h, RScrub.any_resOkB h₁, h₂⟩⟩
  side := ifmaUpdate_side

end VG.Proof.Poly1305.X86_64
