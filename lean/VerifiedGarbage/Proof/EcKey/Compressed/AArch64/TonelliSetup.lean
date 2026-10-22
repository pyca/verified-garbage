module

import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Frame
public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Decompress
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop

/-! # Initialize P-224's descent from its two computed powers -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Impl.EcKey.Compressed.AArch64 (rootQ)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

theorem tonelliSetup_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hr : sv c base s T5 < c.C.p) (ht : sv c base s ACC < c.C.p) :
    WP isa (.block (Impl.EcKey.Compressed.AArch64.tonelliSetup c)) s fun t =>
      KeepRegs [.x1, .x19] s t ∧ Unch base (slW c [T0, ACC, T1]) s.mem t.mem ∧
      (∀ i ∈ [ACC, T0, T1], sv c base t i < c.C.p) ∧
      t.gpr .x19 = BitVec.ofNat 64 95 ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s T5) ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t T0) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t T1) =
        Spec.Weierstrass.pow (Fin.ofNat c.C.p 11) (rootQ c) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := hs.nowrap
  have hT0 := sl_le c h7 (i := T0) (by decide)
  have hACC := sl_le c h7 (i := ACC) (by decide)
  have hT5 := sl_le c h7 (i := T5) (by decide)
  have hT1 := sl_le c h7 (i := T1) (by decide)
  rw [Impl.EcKey.Compressed.AArch64.tonelliSetup, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copy_ok c.n hs hT0 hACC (sl_mod8 c T0) (sl_mod8 c ACC)
    (by have := sl_apart c (i := T0) (j := ACC) (by decide); omega)) fun s₁ ⟨v₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok c.n hs₁ hACC hT5 (sl_mod8 c ACC) (sl_mod8 c T5)
    (by have := sl_apart c (i := ACC) (j := T5) (by decide); omega)) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have r₂ : sv c base s₂ ACC = sv c base s T5 := by
    rw [sv, v₂, O₁.wordsVal (sl_apart c (i := T5) (j := T0) (by decide)) (by omega)]
  have t₂ : sv c base s₂ T0 = sv c base s ACC := by
    rw [sv, O₂.wordsVal (sl_apart c (i := T0) (j := ACC) (by decide)) (by omega), v₁]
  let z := Spec.Weierstrass.pow (Fin.ofNat c.C.p 11) (rootQ c)
  have zR : c.mont z.val < 2 ^ (64 * c.n) := Nat.lt_trans
    (Nat.mod_lt _ (by have := hc.p_ge; omega)) hc.p_lt
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok hs₂ hT1 (sl_mod8 c T1) zR) fun s₃ ⟨v₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  refine WP.mono (setCounter_ok s₃ (j := 95) (by decide)) fun t ⟨v₄, k₄⟩ => ?_
  have e₃ {i : Nat} (hi : i < 45) (hw : i ≠ T1) : sv c base s₃ i = sv c base s₂ i :=
    O₃.wordsVal (sl_apart c hw) (by have := sl_le c h7 hi; omega)
  have e₄ (i : Nat) : sv c base t i = sv c base s₃ i := by rw [sv, k₄.mem]
  have r₄ : sv c base t ACC = sv c base s T5 := by
    rw [e₄, e₃ (by decide) (by decide), r₂]
  have t₄ : sv c base t T0 = sv c base s ACC := by
    rw [e₄, e₃ (by decide) (by decide), t₂]
  have c₄ : sv c base t T1 = c.mont z.val := by
    rw [e₄]; exact v₃
  refine ⟨(((k₁.trans k₂).trans k₃).mono (by sub_regs)).trans
      ((Keeps.regs k₄).mono (by sub_regs)), ?_, ?_, ?_, by rw [r₄], by rw [t₄], ?_⟩
  · rw [k₄.mem]
    exact unch_same (unch_same (slot_frame (by simp) (Nat.le_refl _) O₁)
      (slot_frame (by simp) (Nat.le_refl _) O₂)) (slot_frame (by simp) (Nat.le_refl _) O₃)
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · rw [r₄]; exact hr
    · rw [t₄]; exact ht
    · rw [c₄]; exact Nat.mod_lt _ (by have := hc.p_ge; omega)
  · exact v₄
  · rw [c₄, toM_cmont hc]
    exact Fin.ext (Nat.mod_eq_of_lt z.isLt)

end VG.Proof.EcKey.Compressed.AArch64
