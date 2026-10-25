module

public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.RootPow
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Frame
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy

/-! # The two fixed powers that initialize P-224's descent -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdh.AArch64 (W2)
open VG.Impl.EcKey.Compressed.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

 abbrev tonelliPowerWrites (c : Cfg) := rootWrites c ++ slW c [T5] ++ rootWrites c

 theorem tonelliPowers_ok {c : Cfg} (hc : BaseCfgOk c)
    (hR : ChainOk (rootChain c ((rootQ c + 1) / 2)) ((rootQ c + 1) / 2))
    (hQ : ChainOk (rootChain c (rootQ c)) (rootQ c))
    {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkA c.MP' size c.C.p s.mem base) (hB : sv c base s W2 < c.C.p) :
    WP isa (tonelliPowers c) s fun t =>
      KeepRegs (powClob c.n) s t ∧ Unch base (tonelliPowerWrites c) s.mem t.mem ∧
      sv c base t ACC < c.C.p ∧ sv c base t T5 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ rootQ c ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t T5) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ ((rootQ c + 1) / 2) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  change WP isa (.seq (rootPower c ((rootQ c + 1) / 2))
    (.seq (.block (copy c.n (c.sl T5) (c.sl ACC))) (rootPower c (rootQ c)))) s _
  refine WP.seq (WP.mono (rootPower_ok hc hR hs hM hB)
    fun s₁ ⟨k₁, U₁, lt₁, v₁⟩ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (x0_not_powClob _)
  have e₁ {i : Nat} (hi : i < 45) (hw : i ∉ rootSlots) :
      sv c base s₁ i = sv c base s i := sv_unch U₁ h7 hn hi (apart_rootWrites hc hi hw)
  refine WP.seq (WP.mono (copy_ok c.n hs₁ (sl_le c h7 (by decide)) (sl_le c h7 (by decide))
    (sl_mod8 c T5) (sl_mod8 c ACC)
    (by have := sl_apart c (i := T5) (j := ACC) (by decide); omega)) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_)
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have e₂ {i : Nat} (hi : i < 45) (hw : i ≠ T5) : sv c base s₂ i = sv c base s₁ i :=
    O₂.wordsVal (sl_apart c hw) (by have := sl_le c h7 hi; omega)
  have M₂ : ModOkA c.MP' size c.C.p s₂.mem base := modP_of hc (by
    change sv c base s₂ MP = _
    rw [e₂ (by decide) (by decide), e₁ (by decide) (by decide)]; exact hM.val)
  refine WP.mono (rootPower_ok hc hQ hs₂ M₂
    (by rw [e₂ (by decide) (by decide), e₁ (by decide) (by decide)]; exact hB))
    fun t ⟨kt, Ut, ltt, vt⟩ => ?_
  have et : sv c base t T5 = sv c base s₂ T5 :=
    sv_unch Ut h7 hn (by decide) (apart_rootWrites hc (by decide) (by decide))
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

end VG.Proof.EcKey.Compressed.AArch64
