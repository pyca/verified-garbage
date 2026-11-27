module

public import VerifiedGarbage.Proof.Aes.AArch64.ExpandKey
public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.ExpandKey
public import VerifiedGarbage.Proof.Aes.AArch64.OneBlock
public import VerifiedGarbage.Impl.Aes.AArch64.Callee
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubSide
public import VerifiedGarbage.Proof.Framework.AArch64.Depth
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Implementations of `vg_aes_ctr32` on AArch64

A `Ctr32Impl` is what a function that calls `vg_aes_ctr32` needs of it, so
that its proof holds for every implementation: each is a variant of the
interface `AesCtr32` on AArch64 (`Variants/AesCtr32/AArch64/`), and each
caller (in `Generic/AesCtr32/AArch64/`) is emitted once for each of them (see
`TCB/Emit.lean`). Every implementation is proven against the same contract,
`Proof.Aes.ctr32AArch64`, and has no frames, as is its out-of-place form
(`to`, against `Proof.Aes.ctr32ToAArch64`). It comes with the
implementation of `vg_aes_expand_key` that goes with it (with the same
suffix and CPU features), for the callers that also expand the key, proven
against `Proof.Aes.expandKeyAArch64`.
-/

@[expose] public section

namespace VG.Proof.Aes.AArch64

open VG.AArch64

/-- An implementation of `vg_aes_ctr32` on AArch64. -/
structure Ctr32Impl where
  /-- Its symbol and code. -/
  callee : Impl.Aes.AArch64.Ctr32
  /-- It has no frames (`WP.call`). -/
  noFrames : callee.code.noFrames = true
  ok : ∀ s, Proof.Aes.ctr32AArch64.pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ Proof.Aes.ctr32AArch64.post s s'
  ct : ConstantTime isa Proof.Aes.ctr32AArch64.pre Proof.Aes.ctr32AArch64.pub callee.code
  /-- The bytes of `scratch` it needs: none, or `ctr32AArch64`'s 2048. A
  caller allocates only these (`ctr32AArch64With`), so that it has less of its
  stack to zero on return. -/
  scratch : Nat
  scratch_ok : scratch = 0 ∨ scratch = 2048
  /-- `scratch` is what `Impl/` states of `callee` (`Impl.Aes.AArch64.Ctr32.scratch`),
  from which the functions that call it size their frames. -/
  scratch_eq : callee.scratch = scratch
  okW : ∀ s, (Proof.Aes.ctr32AArch64With scratch).pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.ctr32AArch64With scratch).post s s'
  ctW : ConstantTime isa (Proof.Aes.ctr32AArch64With scratch).pre (Proof.Aes.ctr32AArch64With scratch).pub
    callee.code
  /-- It never writes v8–v15. -/
  keepsV : callee.code.allInstrs keepsV = true
  /-- Its out-of-place form, an internal function proven against
  `Proof.Aes.ctr32ToAArch64`, with the same CPU features. -/
  to : Impl.Aes.AArch64.Ctr32
  toNoFrames : to.code.noFrames = true
  toOk : ∀ s, Proof.Aes.ctr32ToAArch64.pre s →
    ∃ t s', Exec isa to.code s t s' ∧ abiPreserved s s' ∧ Proof.Aes.ctr32ToAArch64.post s s'
  toCt : ConstantTime isa Proof.Aes.ctr32ToAArch64.pre Proof.Aes.ctr32ToAArch64.pub to.code
  /-- `toOk` and `toCt` with `scratch` bytes of `scratch`, as `okW` and `ctW`. -/
  toOkW : ∀ s, (Proof.Aes.ctr32ToAArch64With scratch).pre s →
    ∃ t s', Exec isa to.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.ctr32ToAArch64With scratch).post s s'
  toCtW : ConstantTime isa (Proof.Aes.ctr32ToAArch64With scratch).pre (Proof.Aes.ctr32ToAArch64With scratch).pub
    to.code
  toKeepsV : to.code.allInstrs AArch64.keepsV = true
  /-- What the names of its callers' instances end with (e.g. `_aes`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String
  /-- `callee.code` writes, of the registers the calling convention does not
  preserve, only those `Impl/` states (`callee.clear`): what the cleanup of a
  function that calls it needs of it (`Scrub.scrubSide_union`). -/
  scrub : AArch64.Scrub.calleeSide callee.code callee.clear = true
  /-- The same of `to`, which needs the same `scratch`. -/
  toScrub : AArch64.Scrub.calleeSide to.code to.clear = true
  toScratch_eq : to.scratch = scratch
  /-- The implementation of `vg_aes_expand_key` that goes with it, which
  needs no more CPU features. -/
  expand : Impl.Aes.AArch64.ExpandKey
  expandNoFrames : expand.code.noFrames = true
  expandOk : ∀ s, Proof.Aes.expandKeyAArch64.pre s →
    ∃ t s', Exec isa expand.code s t s' ∧ abiPreserved s s' ∧ Proof.Aes.expandKeyAArch64.post s s'
  expandCt : ConstantTime isa Proof.Aes.expandKeyAArch64.pre Proof.Aes.expandKeyAArch64.pub expand.code
  expandKeepsV : expand.code.allInstrs AArch64.keepsV = true
  /-- `expand.code` writes only the registers `Impl/` states
  (`expand.clear`), as `scrub` is of `callee.code`. -/
  expandScrub : AArch64.Scrub.calleeSide expand.code expand.clear = true

/-- Code without frames uses no stack. -/
theorem depth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.aarch64Depth]

namespace Ctr32Impl

/-- At most `ctr32AArch64`'s 2048 bytes. -/
theorem scratch_le (c : Ctr32Impl) : c.scratch ≤ 2048 := by
  rcases c.scratch_ok with h | h <;> omega

/-- The implementation in the baseline ISA, `vg_aes_ctr32`: each
block encrypted by vector permutations (`OneBlock.lean`). -/
def scalar : Ctr32Impl where
  callee := .scalar
  noFrames := by lit_decide
  ok := OneBlock.ctr32N_correct
  ct := OneBlock.ctr32N_ct
  scratch := 2048
  scratch_ok := .inr rfl
  scratch_eq := rfl
  okW := by rw [Proof.Aes.ctr32AArch64With_2048]; exact OneBlock.ctr32N_correct
  ctW := by rw [Proof.Aes.ctr32AArch64With_2048]; exact OneBlock.ctr32N_ct
  keepsV := by lit_decide
  to := .scalarTo
  toNoFrames := by lit_decide
  toOk := OneBlock.ctr32ToN_correct
  toCt := OneBlock.ctr32ToN_ct
  toOkW := by rw [Proof.Aes.ctr32ToAArch64With_2048]; exact OneBlock.ctr32ToN_correct
  toCtW := by rw [Proof.Aes.ctr32ToAArch64With_2048]; exact OneBlock.ctr32ToN_ct
  toKeepsV := by lit_decide
  suffix := ""
  features := []
  scrub := by lit_decide
  toScrub := by lit_decide
  toScratch_eq := rfl
  expand := .scalar
  expandNoFrames := by lit_decide
  expandOk := expandKey_correct
  expandCt := expandKey_ct
  expandKeepsV := by lit_decide
  expandScrub := by lit_decide

/-- The implementation with the Cryptographic Extension, `vg_aes_ctr32_aes`. -/
def aese : Ctr32Impl where
  callee := .aese
  noFrames := by lit_decide
  ok := Aese.ctr32_correct
  ct := Aese.ctr32_ct
  scratch := 0
  scratch_ok := .inl rfl
  scratch_eq := rfl
  okW := Aese.ctr32_correctW 0
  ctW := Aese.ctr32_ctW 0
  keepsV := by lit_decide
  to := .aeseTo
  toNoFrames := by lit_decide
  toOk := Aese.ctr32To_correct
  toCt := Aese.ctr32To_ct
  toOkW := Aese.ctr32To_correctW 0
  toCtW := Aese.ctr32To_ctW 0
  toKeepsV := by lit_decide
  suffix := "_aes"
  features := ["aes"]
  scrub := by lit_decide
  toScrub := by lit_decide
  toScratch_eq := rfl
  expand := .aese
  expandNoFrames := by lit_decide
  expandOk := Aese.Key.expandKey_correct
  expandCt := Aese.Key.expandKey_ct
  expandKeepsV := by lit_decide
  expandScrub := by lit_decide

end Ctr32Impl

end VG.Proof.Aes.AArch64
