import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.GMul
import VerifiedGarbage.Proof.Ecdsa.AArch64.Main

/-! # p192 signing with the general ladder -/

namespace VG.Proof.Ecdsa.AArch64.P192

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64.P192
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

theorem stage₂ (hc : BaseCfgOk p192) (hC : Law p192.C)
    {s₀ : State} {base : Addr} {hs : Option Nat} {s : State} (hS : St₁ p192 hs s₀ base s)
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', St₂ p192 hs s₀ base s' → WP isa rest s' Q) :
    WP isa (.seq gMul (.seq p192.pPow rest)) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hS.scr.nowrap
  have F := hS.fixed
  have W := gMul_ok hc hC hS.scr F (hS.k ▸ wordsVal_lt _ _ _ _)
    hS.rx hS.ry hS.rz hS.t₀
  refine WP.seq (WP.mono W fun s₅ h₅ => ?_)
  obtain ⟨K₅, U₅, M₅, L₅, R₅⟩ := h₅
  have hs₅ := hS.scr.of_keepRegs K₅ (x0_not_powClob h7)
  have F₅ := F.unch h7 hn (fixedOk_slW (l := gSlots) (by decide)) U₅
  refine WP.seq (WP.mono (pPow_ok hc hs₅ M₅
    (L₅ (p192.sl RZ) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))))
    fun s₆ ⟨K₆, U₆, lt₆, v₆⟩ => h s₆ ?_)
  have e₆ : ∀ {i}, i < 45 → i ∉ [ACC, TMP] →
      i ∉ gSlots →
      sv p192 base s₆ i = sv p192 base s i := fun hi h₁ h₂ =>
    (sv_unch U₆ h7 hn hi (apart_chainWc hi h₁)).trans (sv_unch U₅ h7 hn hi (apart_slW h₂))
  have r₆ : ∀ {i}, i < 45 → i ∉ [ACC, TMP] → sv p192 base s₆ i = sv p192 base s₅ i := fun hi h₁ =>
    sv_unch U₆ h7 hn hi (apart_chainWc hi h₁)
  refine ⟨⟨hs₅.of_keepRegs K₆ (x0_not_powClob h7), ?_, by rw [K₆.wr, K₅.wr, hS.wr],
    F₅.unch h7 hn fixedOk_chainWc U₆⟩,
    by rw [e₆ (by decide) (by decide) (by decide), hS.k],
    by rw [e₆ (by decide) (by decide) (by decide), hS.d],
    by rw [e₆ (by decide) (by decide) (by decide), hS.e],
    by rw [flag_unch_chain U₆ h7 h0 hn, flag_unch U₅ h7 h0 hn (by decide), hS.flag], ?_, lt₆, ?_,
    ?_⟩
  · rw [K₆.gpr _ (x20_not_powClob h7), K₅.gpr _ (x20_not_powClob h7), hS.x20]
  · show Rep p192.C (toM _ _ (sv p192 base s₆ RX)) (toM _ _ (sv p192 base s₆ RY)) (toM _ _ (sv p192 base s₆ RZ)) _
    rw [r₆ (i := RX) (by decide) (by decide), r₆ (i := RY) (by decide) (by decide),
      r₆ (i := RZ) (by decide) (by decide)]
    exact R₅
  · show _ = toM _ _ (sv p192 base s₆ RZ) ^ _
    rw [r₆ (i := RZ) (by decide) (by decide)]
    exact v₆
  · rw [r₆ (i := RZ) (by decide) (by decide)]
    exact L₅ (p192.sl RZ) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

theorem sign_ok (hc : BaseCfgOk p192) (hC : Law p192.C)
    {s₀ : State} (hp : SetupPre p192 s₀) (ho : SignOutput p192 s₀) :
    WP isa signP192 s₀ fun s' =>
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) ∧ SignPost p192 s₀ s' := by
  exact stage₁ hc (.inr (.inr rfl)) hp fun _ S₁ =>
    stage₂ hc hC S₁ fun _ S₂ => stage₃ hc S₂ fun _ S₃ => stage₄ hc hC ho rfl S₃

end VG.Proof.Ecdsa.AArch64.P192
