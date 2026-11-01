module

public import VerifiedGarbage.Impl.CmacAes.AArch64.Callee
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
  keepsV : callee.code.allInstrs AArch64.keepsV = true
  suffix : String
  features : List String
  /-- The implementation of `vg_aes_ctr32` that goes with it, for callers
  that also run counter mode (AES-CCM, AES-SIV): the one it is built on, or
  for the chaining kept in registers, `vg_aes_ctr32_aes`. It needs the same
  CPU features. -/
  ctr : Proof.Aes.AArch64.Ctr32Impl
  ctrFeatures : ctr.features = features

/-- The existing generic CMAC chaining loop, for any CTR implementation. -/
def UpdateImpl.ctr32 (v : Proof.Aes.AArch64.Ctr32Impl) : UpdateImpl where
  callee := ⟨"vg_cmac_aes_update" ++ v.suffix, Impl.CmacAes.AArch64.update v.callee⟩
  noFrames := by
    simp [Impl.CmacAes.AArch64.update, Impl.CmacAes.AArch64.body, Code.noFrames, v.noFrames]
  ok := update_correct v
  ct := update_ct v
  keepsV := update_keepsV v
  suffix := v.suffix
  features := v.features
  ctr := v
  ctrFeatures := rfl

/-- Round keys and chaining value stay in registers across all blocks. -/
def UpdateImpl.aese : UpdateImpl where
  callee := ⟨"vg_cmac_aes_update_aes_cbc", Impl.CmacAes.AArch64.Aese.update⟩
  noFrames := by decide +kernel
  ok := Aese.correct
  ct := Aese.ct
  keepsV := by decide +kernel
  suffix := "_aes_cbc"
  features := ["aes"]
  ctr := .aese
  ctrFeatures := rfl
end VG.Proof.CmacAes.AArch64
