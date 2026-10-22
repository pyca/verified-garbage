module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.RootPow
import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Weierstrass.X86_64.Pow

/-! # The two initial powers in P-224's root recovery -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Impl.Ecdh.X86_64 (W2)
open VG.Impl.EcKey.Compressed.X86_64 (rootQ)
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

abbrev tonelliPowerWrites (c : Cfg) :=
  rootPowerWrites c 1 ++ slW c [T5] ++ rootPowerWrites c 2

theorem tonelliPowers_ok {c : Cfg} (hc : BaseCfgOk c) (hn9 : c.n ≠ 9)
    {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkW c.MP' size c.C.p s.mem base) (hB : sv c base s W2 < c.C.p)
    (hO : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (Impl.EcKey.Compressed.X86_64.tonelliPowers c).inline s fun t =>
      KeepRegs (powClob c.n) s t ∧ Unch base (tonelliPowerWrites c) s.mem t.mem ∧
      sv c base t ACC < c.C.p ∧ sv c base t T5 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ rootQ c ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t T5) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ ((rootQ c + 1) / 2) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hq : rootQ c ≤ c.C.p - 1 := Nat.div_le_self _ _
  have hp := hc.p_ge
  have he : (rootQ c + 1) / 2 < 2 ^ (64 * c.n) := by have := hc.p_lt; omega
  have hqR : rootQ c < 2 ^ (64 * c.n) := by have := hc.p_lt; omega
  change WP isa (.seq (Impl.EcKey.Compressed.X86_64.rootPower c ((rootQ c + 1) / 2) 1).inline
    (.seq (.block (copy c.n (c.sl T5) (c.sl ACC)))
      (Impl.EcKey.Compressed.X86_64.rootPower c (rootQ c) 2).inline)) s _
  refine WP.seq (WP.mono (rootPower_ok hc (by decide) (.inr hn9) he hs hM hB hO)
    fun s₁ ⟨k₁, U₁, lt₁, v₁⟩ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (rdi_not_powClob _)
  have e₁ {i : Nat} (hi : i < 45) (hw : i ∉ [EXPP, ACC, PT, TMP]) :
      sv c base s₁ i = sv c base s i := sv_unch U₁ h7 hn hi (rootPower_apart hi hw)
  refine WP.seq (WP.mono (copy_ok c.n hs₁ (sl_le c h7 (by decide)) (sl_le c h7 (by decide))
    (by have := sl_apart c (i := T5) (j := ACC) (by decide); omega)) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_)
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have e₂ {i : Nat} (hi : i < 45) (hw : i ≠ T5) : sv c base s₂ i = sv c base s₁ i :=
    O₂.wordsVal (sl_apart c hw) (by have := sl_le c h7 hi; omega)
  have M₂ : ModOkW c.MP' size c.C.p s₂.mem base := modP_of hc (by
    change sv c base s₂ MP = _
    rw [e₂ (by decide) (by decide), e₁ (by decide) (by decide)]; exact hM.val)
  refine WP.mono (rootPower_ok hc (by decide) (.inl (by decide)) hqR hs₂ M₂
    (by rw [e₂ (by decide) (by decide), e₁ (by decide) (by decide)]; exact hB)
    (by rw [e₂ (by decide) (by decide), e₁ (by decide) (by decide)]; exact hO))
    fun t ⟨kt, Ut, ltt, vt⟩ => ?_
  have et : sv c base t T5 = sv c base s₂ T5 :=
    sv_unch Ut h7 hn (by decide) (rootPower_apart (by decide) (by decide))
  refine ⟨(k₁.trans (k₂.mono (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr; simp [powClob, clob]))).trans kt,
    (U₁.trans O₂.unch).trans Ut, ltt, ?_, ?_, ?_⟩
  · rw [et]
    change wordsVal s₂.mem base (c.sl T5) c.n < _
    rw [v₂]; exact lt₁
  · rw [vt, e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
  · rw [et]
    change toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₂.mem base (c.sl T5) c.n) = _
    rw [v₂]; exact v₁

end VG.Proof.EcKey.Compressed.X86_64
