import VerifiedGarbage.Proof.Ecdsa.X86.Inv
import VerifiedGarbage.Proof.Weierstrass.X86.P256Power
import VerifiedGarbage.Proof.Ecdsa.X86.Main
import VerifiedGarbage.Proof.Ecdsa.X86.GMul

/-! # Fixed-base comb in the ECDSA stages -/
namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
variable {c : Cfg} {A : Args}

/-- Fixed-base multiplication preserves the state shared by later stages. -/
theorem Keep.gMul {s₀ s t : State} {base : Addr} (hc : CfgOk c)
    (hs : Keep c s₀ base s) (K : Keeps powClob s t) (U : Unch base (gW c) s.mem t.mem) :
    Keep c s₀ base t :=
  ⟨hs.scr.of_keeps K (by decide), (K.gpr _ (by decide)).trans hs.esp,
    K.rd.trans hs.rd, K.wr.trans hs.wr,
    hs.fixed.unch hc.n10 hs.scr.nowrap fixedOk_gW U,
    whole_of hs.whole U (gW_le hc.n10)⟩

/-- `[k]G`, then `Z^(p-2)`. -/
theorem stage₂Comb (hc : CfgOk c) (hC : Law c.C) (hT : CombTbls c)
    (hCo : ∀ d, c.comb = some d → CombOk c d) (ham3 : AM3 c.C) {s₀ : State} {base : Addr} {s : State} (hS : St₁ c A s₀ base s)
    (hTb : ∀ d, c.comb = some d → TblMem s₀ ((s₀.gpr .eax).setWidth 64) (c.combWords d) ∧
      ∀ i < (c.combWords d).length, ∀ b < 8,
        size ≤ ofs base ((s₀.gpr .eax).setWidth 64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b))
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', St₂ c A s₀ base s' → WP isa rest s' Q) :
    WP isa (.seq c.gMul (.seq c.pPow rest)) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hS.scr.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have F := hS.fixed
  refine WP.seq (WP.mono (gMul_ok' hc hC hT hCo ham3 hS.scr F
    (hS.k ▸ wordsVal_lt _ _ _ _) hS.rx hS.ry hS.rz hS.t₀ (fun d hd => by
      obtain ⟨ht, ho⟩ := hTb d hd
      exact ⟨ht.of_unch (by rw [hS.rd, hS.wr]) hS.whole
        (fun w hw => by rw [List.mem_singleton.mp hw]; exact Nat.le_refl _) ho, ho⟩))
    fun s₅ ⟨K₅, U₅, M₅, L₅, R₅⟩ => ?_)
  have hs₅ := hS.scr.of_keeps K₅ (by decide)
  have F₅ := F.unch h7 hn (fixedOk_gW) U₅
  refine WP.seq (WP.mono (pPow_ok hc hs₅ M₅
    (L₅ (c.sl RZ) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))) F₅.onep
    (fun t ht => by
      show s₅.mem (off base (bitsAt c.n 1 + t)) = _
      rw [tbl_unch U₅ h7 (j := 1) (by decide) ht (tbl_apart_gW (Or.inl rfl) ht)]
      exact hS.t₁ t ht)
    (show c.C.p - 2 < 2 ^ (64 * c.n) by have := hc.p_lt; omega)) fun s₆ ⟨K₆, U₆, lt₆, v₆⟩ => h s₆ ?_)
  have e₆ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] →
      i ∉ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM] →
      sv c base s₆ i = sv c base s i := fun hi h₁ h₂ =>
    (sv_unch U₆ h7 hn hi (apart_pwW hi h₁)).trans (sv_unch U₅ h7 hn hi (apart_gW hi h₂))
  have r₆ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₆ i = sv c base s₅ i := fun hi h₁ =>
    sv_unch U₆ h7 hn hi (apart_pwW hi h₁)
  refine ⟨⟨hs₅.of_keeps K₆ (by decide), by rw [K₆.1 _ (by decide), K₅.1 _ (by decide), hS.esp],
    by rw [K₆.2.1, K₅.2.1, hS.rd], by rw [K₆.2.2, K₅.2.2, hS.wr],
    F₅.unch h7 hn fixedOk_pwW U₆,
    whole_of (whole_of hS.whole U₅ (gW_le h7)) U₆ (pwW_le h7)⟩,
    by rw [e₆ (by decide) (by decide) (by decide), hS.k],
    by rw [e₆ (by decide) (by decide) (by decide), hS.d],
    by rw [e₆ (by decide) (by decide) (by decide), hS.e],
    by rw [flagW, flag_unch_pwW U₆ h7 h0 hn, flag_unch_gW U₅ h7 h0 hn, ← flagW, hS.flag],
    ?_, ?_, lt₆, ?_, ?_⟩
  · intro t ht
    rw [tbl_unch U₆ h7 (j := 2) (by decide) ht (tbl_apart_pwW (by decide) ht),
      tbl_unch U₅ h7 (j := 2) (by decide) ht (tbl_apart_gW (Or.inr rfl) ht)]
    exact hS.t₂ t ht
  · show Rep c.C (toM _ _ (sv c base s₆ RX)) (toM _ _ (sv c base s₆ RY)) (toM _ _ (sv c base s₆ RZ)) _
    rw [r₆ (i := RX) (by decide) (by decide), r₆ (i := RY) (by decide) (by decide),
      r₆ (i := RZ) (by decide) (by decide)]
    exact R₅
  · show _ = toM _ _ (sv c base s₆ RZ) ^ _
    rw [r₆ (i := RZ) (by decide) (by decide)]
    exact v₆
  · rw [r₆ (i := RZ) (by decide) (by decide)]
    exact L₅ (c.sl RZ) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))


/-- The signing body using the fixed-base comb, after the address prefix. -/
theorem signCombBody_ok (hc : CfgOk c) (hC : Law c.C) (hT : CombTbls c)
    (hCo : ∀ d, c.comb = some d → CombOk c d) (ham3 : AM3 c.C)
    {s₀ : State} {extra : List Region} (hp : Pre c s₀ extra)
    (hTb : ∀ d, c.comb = some d → TblMem s₀ ((s₀.gpr .eax).setWidth 64) (c.combWords d) ∧
      ∀ i < (c.combWords d).length, ∀ b < 8,
        size ≤ ofs (ptr s₀ 4) ((s₀.gpr .eax).setWidth 64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) :
    WP isa (c.signWithMul c.gMul) s₀ fun s' => SignKeep c s₀ s' ∧ SignPost c s₀ s' :=
  WP.seq (WP.mono (stage₁ hc hp.setup (rest := .block [])
    (Q := St₁ c .sign s₀ (ptr s₀ 4)) (fun _ h => WP.block_nil h))
    fun _ S₁ => stage₂Comb hc hC hT hCo ham3 S₁ hTb fun _ S₂ =>
      stage₃ hc S₂ fun _ S₃ => stage₄ hc hC hp rfl S₃)


end VG.Proof.Ecdsa.X86
