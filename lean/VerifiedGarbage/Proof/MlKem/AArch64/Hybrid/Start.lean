module
public import Mathlib.Tactic.IntervalCases
public import VerifiedGarbage.Impl.MlKem.AArch64.Hybrid
public import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit

import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Matrix
meta import VerifiedGarbage.Proof.MlKem.AArch64.Encaps

/-!
# The hashing encapsulation's first phase

`startH_ok`: the prologue, `m`, the all-zero third state and `ρ`
(`Hybrid.startH`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Encaps
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Spec.MlKem
open VG.Proof.MlKem

variable {P : KemLay}

/-- After the first phase. -/
structure AfterS (P : KemLay) (s₀ s : State) : Prop where
  kb : KB P (enL P) s₀ s
  x24 : s.gpr .x24 = 1
  m : bytesAt s.mem (sA (enL P) s₀ MB) 32 = mE s₀
  rho : bytesAt s.mem (sA (enL P) s₀ SB) 32 = rhoE P s₀
  zero : stateAt s.mem (kA s₀ (enL P).sc) = Spec.Sha3.zero

theorem startH_ok {s₀ : State} (hp : Pre P (enL P) s₀) :
    WP isa (Impl.MlKem.AArch64.Hybrid.startH P) s₀ (AfterS P s₀) := by
  have hw := hp.wf
  unfold Impl.MlKem.AArch64.Hybrid.startH
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  -- the prologue and `m`
  refine WP.mono (prologue_ok hp) fun s₁ h₁ => ?_
  refine WP.mono (KeyGen.copy_ok (S := kA s₀ 1) (D := kA s₀ 4) (so := 0) (dO := MB) (by decide) (by decide)
    (by decide) (by decide) (hp.args.rdisj (by enk) (by enk) (by enk) (hp.fs (by lom)) (by enk)
      (by decide)) (by rw [h₁.keep.get .x1 (by decide)]; rfl) h₁.kb.x28
    (cov_r hp h₁.kb (b := 1) (by enk) (by enk)) (cov_s hp h₁.kb (by lom)))
    fun s₂ ⟨k₂, f₂, b₂⟩ => ?_
  have kb₂ := h₁.kb.frame k₂ f₂ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact safe_scr hp (by enk)
  have m₂ : bytesAt s₂.mem (sA (enL P) s₀ MB) 32 = mE s₀ := by
    rw [show sA (enL P) s₀ MB = kA s₀ 4 + BitVec.ofNat 64 MB from rfl, b₂,
      h₁.kb.ro_bytes (b := 1) (by enk) (by enk), ptr_zero]
  have x24₂ : s₂.gpr .x24 = 1 := by rw [k₂.get .x24, h₁.x24]
  -- the third state
  have hS := hsetup hp kb₂ (by decide : 136 ∈ Spec.Sha3.rates)
  refine WP.mono (zeroState_ok hS (s := s₂) ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩) fun s₃ ⟨k₃, z₃⟩ => ?_
  have e28' : ∀ o l, (⟨s₂.gpr .x28 + BitVec.ofNat 64 o, l⟩ : Region) = R (kA s₀) (enL P).sc o l :=
    fun o l => by rw [kb₂.x28]
  have kb₃ := kb₂.call k₃ fun r hr => by
    rw [List.mem_singleton.mp hr, VG.Proof.MlKem.AArch64.STr, e28']; exact safe_scr hp (by lom)
  have m₃ : bytesAt s₃.mem (sA (enL P) s₀ MB) 32 = mE s₀ := by
    rw [bytesAt_frame k₃.frame (fun r hr => by
      rw [List.mem_singleton.mp hr, VG.Proof.MlKem.AArch64.STr, e28']
      exact sdisj hp (by lom) (by lom) (by lom)) (by decide)]
    exact m₂
  have z₃' : stateAt s₃.mem (kA s₀ (enL P).sc) = Spec.Sha3.zero := by
    rw [kb₂.x28, show KEM.ST = 0 from rfl, ptr_zero] at z₃; exact z₃
  have x24₃ : s₃.gpr .x24 = 1 := by rw [k₃.cs _ (by decide) (by decide), x24₂]
  -- `ρ`
  refine WP.mono (KeyGen.copy_ok (S := kA s₀ 0) (D := kA s₀ 4) (so := 384 * P.k) (dO := SB) (by decide)
    (by decide) (by lom) (by decide) (hp.args.rdisj (by enk) (by enk) (by enk)
      (hp.fs (by lom)) (by enk) (by enk)) kb₃.x25 kb₃.x28 (cov_r hp kb₃ (b := 0) (by enk)
      (by enk)) (cov_s hp kb₃ (by lom)))
    fun s₄ ⟨k₄, f₄, b₄⟩ => ?_
  have kb₄ := kb₃.frame k₄ f₄ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact safe_scr hp (by enk)
  have far₄ : ∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ SB ∨ SB + 32 ≤ o) →
      bytesAt s₄.mem (sA (enL P) s₀ o) l = bytesAt s₃.mem (sA (enL P) s₀ o) l := fun f h => by
    refine bytesAt_frame f₄ (fun r hr => ?_) (by lom)
    rw [List.mem_singleton.mp hr]
    exact sdisj hp f (by lom) h
  refine ⟨kb₄, by rw [k₄.get .x24, x24₃], by rw [far₄ (o := MB) (l := 32) (by lom) (by decide)]; exact m₃,
    ?_, ?_⟩
  · rw [show sA (enL P) s₀ SB = kA s₀ 4 + BitVec.ofNat 64 SB from rfl, b₄,
      kb₃.ro_bytes (b := 0) (by enk) (by enk),
      ← bytesAt_slice _ _ (show 384 * P.k + 32 ≤ P.ekLen from Nat.le_refl _)]
    rfl
  · rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame f₄ (fun r hr => by
      rw [List.mem_singleton.mp hr, stR_sc]; exact sdisj hp (by lom) (by lom) (by lom))]
    exact z₃'

end VG.Proof.MlKem.AArch64.Hybrid
