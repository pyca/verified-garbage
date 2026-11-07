module

public import VerifiedGarbage.Impl.CmacAes.AArch64.Callee
public import VerifiedGarbage.Proof.CmacAes.AArch64.Aese
public import VerifiedGarbage.Proof.CmacAes.AArch64.UpdateCT
public import VerifiedGarbage.Proof.CmacAes.AArch64.Verified
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

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
  that also run counter mode (AES-CCM, AES-SIV): the one it calls. It needs
  the same CPU features. -/
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

theorem aese_noFrames : Impl.CmacAes.AArch64.Aese.update.noFrames = true := by decide +kernel

theorem aese_keepsV : Impl.CmacAes.AArch64.Aese.update.allInstrs AArch64.keepsV = true := by
  decide +kernel

/-! ## The choice by the number of blocks -/

/-- What the comparison leaves: `x9` is `n >> 1`, which is zero exactly when
`n` (`x4`) is less than 2, and nothing else changes. -/
theorem hybrid_run (s : State) :
    ∃ u, execBlock isa [.lsr .x .x9 .x4 1] s = some (u, []) ∧
      (∀ r, r ≠ .x9 → u.gpr r = s.gpr r) ∧ u.sp = s.sp ∧ u.mem = s.mem ∧ u.rd = s.rd ∧
      u.wr = s.wr ∧ u.v = s.v ∧
      eval (.nonzero .x .x9) u = some (decide (2 ≤ (s.gpr .x4).toNat)) := by
  refine ⟨_, by simp only [execBlock, exec_lsr_x (by decide : 1 < 64)]; rfl,
    fun r h => RegUpd.gpr_write_of_ne s .x _ h, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only [eval, State.read, RegUpd.gpr_write_self, Size.bits, BitVec.setWidth_eq,
    Option.some.injEq]
  have h := (s.gpr .x4).isLt
  rw [Bool.eq_iff_iff, bne_iff_ne, ne_eq, decide_eq_true_iff, ← BitVec.toNat_inj,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  show ¬(s.gpr .x4).toNat / 2 ^ 1 = 0 ↔ _
  omega

/-- `hybrid v`, for the proofs of a state satisfying the precondition (which
`Verified` asks of each branch): the chaining with the round keys in
registers for two blocks or more, otherwise by calls of `v`
(`Verified.entryBranch`). The comparison writes only `x9`, which the
contract does not read, and leaks nothing; the branch depends only on `n`
(`x4`), which is public. -/
theorem hybrid_verified (v : Proof.Aes.AArch64.Ctr32Impl) {s₀ : State} (h₀ : updateAArch64.pre s₀) :
    Verified AArch64.target (Impl.CmacAes.AArch64.hybrid v.callee) updateAArch64 := by
  have hp : ∀ r ∈ preserved, r ≠ .x9 := by decide
  refine Verified.entryBranch (p := fun s => decide (2 ≤ (s.gpr .x4).toNat)) (fun _ => [])
    ⟨Aese.correct, Aese.ct, _, h₀⟩ ⟨update_correct v, update_ct v, _, h₀⟩ (fun s hs => ?_) ?_ ⟨_, h₀⟩
  · obtain ⟨u, e, g, sp, m, rd, wr, vv, ev⟩ := hybrid_run s
    have pre : updateAArch64.pre u := by
      simp only [updateAArch64] at hs ⊢
      rw [g .x0 (by decide), g .x1 (by decide), g .x2 (by decide), g .x3 (by decide),
        g .x4 (by decide), g .x5 (by decide), rd, wr]
      exact hs
    have post : ∀ s', AArch64.target.abiPreserved u s' → updateAArch64.post u s' →
        AArch64.target.abiPreserved s s' ∧ updateAArch64.post s s' := fun s' a q =>
      ⟨⟨fun x hx => by rw [a.1 x hx, g x (hp x hx)], by rw [a.2.1, sp], fun x hx => by rw [a.2.2 x hx, vv]⟩,
        by
          simp only [updateAArch64] at q ⊢
          rw [g .x0 (by decide), g .x1 (by decide), g .x2 (by decide), g .x3 (by decide),
            g .x4 (by decide), m] at q
          exact q⟩
    exact ⟨u, e, ev, fun _ => ⟨pre, post⟩, fun _ => ⟨pre, post⟩⟩
  · intro s s' u u' _ _ hq e e'
    obtain ⟨u₀, e₀, g, sp, -⟩ := hybrid_run s
    obtain ⟨u₀', e₀', g', sp', -⟩ := hybrid_run s'
    rw [e₀] at e; rw [e₀'] at e'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
    obtain ⟨q0, q1, q2, q3, q4, q5, q6⟩ := hq
    have pu : updateAArch64.pub u₀ u₀' := by
      simp only [updateAArch64]
      rw [g .x0 (by decide), g' .x0 (by decide), g .x1 (by decide), g' .x1 (by decide),
        g .x2 (by decide), g' .x2 (by decide), g .x3 (by decide), g' .x3 (by decide),
        g .x4 (by decide), g' .x4 (by decide), g .x5 (by decide), g' .x5 (by decide), sp, sp']
      exact ⟨q0, q1, q2, q3, q4, q5, q6⟩
    exact ⟨rfl, by rw [q4], fun _ => pu, fun _ => pu⟩

/-- The chaining with the round keys in registers for two blocks or more,
otherwise by calls of `v` on one block at a time: `vg_cmac_aes_update` with
`v`'s suffix, for an implementation `v` that needs the AES extension. -/
def UpdateImpl.hybrid (v : Proof.Aes.AArch64.Ctr32Impl) : UpdateImpl where
  callee := ⟨"vg_cmac_aes_update" ++ v.suffix, Impl.CmacAes.AArch64.hybrid v.callee⟩
  noFrames := by
    have := aese_noFrames
    simp [Impl.CmacAes.AArch64.hybrid, Code.iteCold, Impl.CmacAes.AArch64.update,
      Impl.CmacAes.AArch64.body, Code.noFrames, v.noFrames, this]
  ok := fun s hs => (hybrid_verified v hs).1 s hs
  ct := fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ => (hybrid_verified v h₁).2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂
  keepsV := by
    have := aese_keepsV; have := update_keepsV v
    simp only [Impl.CmacAes.AArch64.hybrid, Code.iteCold, Code.allInstrs] at *
    simp only [*]
    rfl
  suffix := v.suffix
  features := v.features
  ctr := v
  ctrFeatures := rfl
end VG.Proof.CmacAes.AArch64
