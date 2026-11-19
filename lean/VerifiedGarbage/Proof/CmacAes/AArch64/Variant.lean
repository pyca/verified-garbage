module

public import VerifiedGarbage.Impl.CmacAes.AArch64.Callee
public import VerifiedGarbage.Impl.Residue.AArch64.Scrub
public import VerifiedGarbage.Proof.CmacAes.AArch64.Aese
public import VerifiedGarbage.Proof.CmacAes.AArch64.UpdateCT
public import VerifiedGarbage.Proof.CmacAes.AArch64.Verified
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract

@[expose] public section

namespace VG.Proof.CmacAes.AArch64
open VG VG.AArch64
/-- The whole-block implementation used by streaming absorb. Every variant
has the existing CMAC update contract, so the buffering proof is shared. -/
structure UpdateImpl where
  callee : Impl.CmacAes.AArch64.Update
  noFrames : callee.code.noFrames = true
  ok : ∀ s, updateAArch64.pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ updateAArch64.post s s'
  ct : ConstantTime isa updateAArch64.pre updateAArch64.pub callee.code
  /-- The bytes of working space it needs: none, or `updateAArch64`'s.
  Streaming absorb allocates only these (`Stream/AArch64`), in a frame whose
  proofs take each size in turn. -/
  scratch : Nat
  scratch_ok : scratch = 0 ∨ scratch = 2176
  okW : ∀ s, (updateAArch64With scratch).pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ (updateAArch64With scratch).post s s'
  ctW : ConstantTime isa (updateAArch64With scratch).pre (updateAArch64With scratch).pub callee.code
  keepsV : callee.code.allInstrs AArch64.keepsV = true
  suffix : String
  features : List String
  /-- The registers `callee.code` writes: a caller's tail clears them with
  its own (`ScrubAll.clearUnion`), and its `ScrubAll.scrubSide` holds this
  to the code. -/
  clear : Impl.Residue.AArch64.Clear
  /-- The implementation of `vg_aes_ctr32` that goes with it, for callers
  that also run counter mode (AES-CCM, AES-SIV): the one it is built on, or
  for the chaining kept in registers, `vg_aes_ctr32_aes`. It needs the same
  CPU features. -/
  ctr : Proof.Aes.AArch64.Ctr32Impl
  ctrFeatures : ctr.features = features
  /-- Its counter-mode implementation needs no more working space than it does. -/
  ctrScratch : ctr.scratch ≤ scratch

/-- The existing generic CMAC chaining loop, for any CTR implementation. -/
def UpdateImpl.ctr32 (v : Proof.Aes.AArch64.Ctr32Impl) (clear : Impl.Residue.AArch64.Clear) : UpdateImpl where
  callee := ⟨"vg_cmac_aes_update" ++ v.suffix, Impl.CmacAes.AArch64.update v.callee⟩
  noFrames := by
    simp [Impl.CmacAes.AArch64.update, Impl.CmacAes.AArch64.body, Code.noFrames, v.noFrames]
  ok := update_correct v
  ct := update_ct v
  scratch := 2176
  scratch_ok := .inr rfl
  okW := by rw [updateAArch64With_2176]; exact update_correct v
  ctW := by rw [updateAArch64With_2176]; exact update_ct v
  keepsV := update_keepsV v
  suffix := v.suffix
  features := v.features
  clear := clear
  ctr := v
  ctrFeatures := rfl
  ctrScratch := by rcases v.scratch_ok with h | h <;> rw [h] <;> decide

/-- Round keys and chaining value stay in registers across all blocks:
`vg_cmac_aes_update_aes`, faster than the chaining by calls of
`vg_aes_ctr32_aes` for any number of blocks. -/
def UpdateImpl.aese : UpdateImpl where
  callee := ⟨"vg_cmac_aes_update_aes", Impl.CmacAes.AArch64.Aese.update⟩
  noFrames := by decide +kernel
  ok := Aese.correct
  ct := Aese.ct
  scratch := 0
  scratch_ok := .inl rfl
  okW := Aese.correctW 0
  ctW := Aese.ctW 0
  keepsV := by decide +kernel
  suffix := "_aes"
  features := ["aes"]
  clear := ⟨[.x3, .x4, .x6, .x7, .x9],
    [.v0, .v1, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30,
     .v31],
    []⟩
  ctr := .aese
  ctrFeatures := rfl
  ctrScratch := Nat.le_refl _
end VG.Proof.CmacAes.AArch64
