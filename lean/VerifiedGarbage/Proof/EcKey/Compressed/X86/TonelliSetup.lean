module

import VerifiedGarbage.Proof.EcKey.Compressed.X86.Frame
public import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
import VerifiedGarbage.Proof.Ecdsa.X86.Stages
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Ecdsa.X86.Fixed

/-! # Initialize P-224's descent from its two computed powers -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86

open VG.X86.Wp
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Ecdsa.X86 VG.Impl.Weierstrass.X86
open VG.Impl.EcKey.Compressed.X86 (rootQ)
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86

theorem tonelliSetup_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hr : sv c base s T5 < c.C.p) (ht : sv c base s ACC < c.C.p) :
    WP isa (.block (Impl.EcKey.Compressed.X86.tonelliSetup c)) s fun t =>
      Keeps [.eax] s t ∧ Unch base (slW c [T0, ACC, T1, T2]) s.mem t.mem ∧
      (∀ i ∈ [ACC, T0, T1], sv c base t i < c.C.p) ∧
      t.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 95 ∧
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
  have hT2 := sl_le c h7 (i := T2) (by decide)
  rw [Impl.EcKey.Compressed.X86.tonelliSetup, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copy_ok (2 * c.n) hs (by omega) (by omega)
    (by have := sl_apart c (i := T0) (j := ACC) (by decide); omega)) fun s₁ ⟨v₁, k₁, O₁⟩ => ?_
  simp only [← wordsVal_eq_val32] at v₁
  rw [show 4 * (2 * c.n) = 8 * c.n by omega] at O₁
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (2 * c.n) hs₁ (by omega) (by omega)
    (by have := sl_apart c (i := ACC) (j := T5) (by decide); omega)) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_
  simp only [← wordsVal_eq_val32] at v₂
  rw [show 4 * (2 * c.n) = 8 * c.n by omega] at O₂
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have r₂ : sv c base s₂ ACC = sv c base s T5 := by
    rw [sv, v₂, O₁.wordsVal (sl_apart c (i := T5) (j := T0) (by decide)) (by omega)]
  have t₂ : sv c base s₂ T0 = sv c base s ACC := by
    rw [sv, O₂.wordsVal (sl_apart c (i := T0) (j := ACC) (by decide)) (by omega), v₁]
  let z := Spec.Weierstrass.pow (Fin.ofNat c.C.p 11) (rootQ c)
  have zR : c.mont z.val < 2 ^ (64 * c.n) := Nat.lt_trans
    (Nat.mod_lt _ (by have := hc.p_ge; omega)) hc.p_lt
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok hs₂ hT1 zR) fun s₃ ⟨v₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine wp_movi fun s₄ u₄ => ?_
  have hs₄ := hs₃.of_keeps u₄.keeps (by decide)
  refine wp_storeS (hs₄.ea (by omega)) (hs₄.write (by omega : c.sl T2 + 4 ≤ size))
    fun t m₄ => WP.block_nil ?_
  have O₄ : Outside base (c.sl T2) 4 s₃.mem t.mem := by
    rw [m₄.mem, u₄.mem]
    exact writeW32_outside _ _ _ (by omega)
  have v₄ : t.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 95 := by
    rw [m₄.mem, Mem.readW_writeW_self32, u₄.gpr]; rfl
  have k₄ : Keeps [.eax] s₃ t := u₄.keeps.trans (m₄.keeps _)
  have e₃ {i : Nat} (hi : i < 45) (hw : i ≠ T1) : sv c base s₃ i = sv c base s₂ i :=
    O₃.wordsVal (sl_apart c hw) (by have := sl_le c h7 hi; omega)
  have e₄ {i : Nat} (hi : i < 45) (hw : i ≠ T2) : sv c base t i = sv c base s₃ i :=
    O₄.wordsVal (by have := sl_apart c hw; omega) (by have := sl_le c h7 hi; omega)
  have r₄ : sv c base t ACC = sv c base s T5 := by
    rw [e₄ (by decide) (by decide), e₃ (by decide) (by decide), r₂]
  have t₄ : sv c base t T0 = sv c base s ACC := by
    rw [e₄ (by decide) (by decide), e₃ (by decide) (by decide), t₂]
  have c₄ : sv c base t T1 = c.mont z.val := by
    rw [e₄ (by decide) (by decide)]; exact v₃
  refine ⟨((k₁.trans k₂).trans k₃).trans k₄, ?_, ?_, ?_, by rw [r₄], by rw [t₄], ?_⟩
  · exact unch_same (unch_same (unch_same (slot_frame (by simp) (Nat.le_refl _) O₁)
      (slot_frame (by simp) (Nat.le_refl _) O₂)) (slot_frame (by simp) (Nat.le_refl _) O₃))
      (slot_frame (by simp) (by omega) O₄)
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · rw [r₄]; exact hr
    · rw [t₄]; exact ht
    · rw [c₄]; exact Nat.mod_lt _ (by have := hc.p_ge; omega)
  · exact v₄
  · rw [c₄, toM_cmont hc]
    exact Fin.ext (Nat.mod_eq_of_lt z.isLt)

end VG.Proof.EcKey.Compressed.X86
