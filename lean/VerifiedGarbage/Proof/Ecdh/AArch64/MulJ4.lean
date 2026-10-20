module

public import VerifiedGarbage.Proof.Ecdh.AArch64.MulOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJLoop
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
public import VerifiedGarbage.Impl.Ecdh.AArch64.WindowJ
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Ecdh.AArch64.Window
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJNorm
import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
import VerifiedGarbage.Proof.Weierstrass.WindowJ

/-!
# ECDH on AArch64: `[d]P` by 4-bit windows with a Jacobian accumulator

`Cfg.mulJ4`, for a curve of prime order whose order `n` is above the
multiples of every iteration but the last (`winE_two_bound`), as on x86-64
(`Proof/Ecdh/X86_64/MulJ4.lean`): `winPrep` recodes `d` as for `window`, and
`WinCfg.windowJ` (`windowJ_ok`) computes `[d]P`, its table brought into
affine coordinates by the signature's power (`invJ`: `ACC = R.z^(p-2)`,
copied into `E.x`, `invJSpec`). The power after it is `MulOk`'s.
-/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)

variable {c : Cfg}

/-- What the table's inversion writes: the power's areas and `E.x`. -/
def invJW (c : Cfg) : List (Nat × Nat) := chainWc c ++ [(c.sl TX, 8 * c.n)]

/-- The registers the window method and its inversion may change. -/
def invJClob (n : Nat) : List Reg := combClob n ++ powClob n

/-- The table's inversion: the power, then `E.x = ACC`; given that the
power's areas are apart from the window's slots and the modulus
(`hw`), and from its table of bits (`hb`). -/
theorem invJSpec (hc : CfgOk c) {base : Addr}
    (hw : ∀ w ∈ chainWc c, w = ((winQ c).M.tmp, 8 * c.n) ∨
      ((winQ c).M.mo + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ (winQ c).M.mo) ∧
      ∀ x ∈ winSlots (winQ c), x + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ x)
    (hb : ∀ w ∈ invJW c, c.winBits + 4 * (16 * c.n + 1) ≤ w.1 ∨ w.1 + w.2 ≤ c.winBits) :
    InvSpecW (winQ c) c.C base size (Impl.Ecdh.AArch64.Cfg.invJ c) (invJClob c.n) (invJW c) := by
  have h7 := hc.n10
  refine ⟨fun t ht hM hz => ?_, fun w hw' => ?_, hb⟩
  · rw [Impl.Ecdh.AArch64.Cfg.invJ]
    refine WP.seq (WP.mono (pPow_ok hc.toBaseCfgOk ht hM hz) fun t₁ ⟨K₁, U₁, lt₁, v₁⟩ => ?_)
    have ht₁ := ht.of_keepRegs K₁ (x0_not_powClob h7)
    refine WP.mono (copy_ok (size := size) c.n ht₁ (o := c.sl TX) (a := c.sl ACC)
      (sl_le c h7 (by decide)) (sl_le c h7 (by decide)) (sl_mod8 c _) (sl_mod8 c _)
      ((sl_apart c (i := TX) (j := ACC) (by decide)).elim
        (fun h => Or.inl (Nat.le_trans (Nat.le_add_right _ _) h)) Or.inr))
      fun t₂ ⟨v₂, K₂, O₂⟩ => ?_
    refine ⟨(K₁.mono fun r hr => List.mem_append_right _ hr).trans
        (K₂.mono fun r hr => by
          rw [List.mem_singleton.mp hr]; exact List.mem_append_left _ (combClob_mem (by simp))),
      (U₁.trans O₂.unch).mono fun w hw => by simpa [invJW] using hw, ?_, ?_⟩
    · show wordsVal t₂.mem base (c.sl TX) c.n < c.C.p
      rw [v₂]; exact lt₁
    · show toM _ _ (wordsVal t₂.mem base (c.sl TX) c.n) = toM _ _ (wordsVal t.mem base (c.sl RZ) c.n) ^ _
      rw [v₂]; exact v₁
  · simp only [invJW, List.mem_append, List.mem_singleton] at hw'
    rcases hw' with hw' | rfl
    · rcases hw w hw' with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inl rfl

/-- What `mulJ4` writes: the recoded scalar's areas, the window's slots and
the inversion's. -/
abbrev mulJ4W (c : Cfg) : List (Nat × Nat) := winX c ++ (slW c (otherI ++ tblI ++ [TMP]) ++ chainWc c)

/-- `[d]P` by `windowJ`, then the power: `MulOk`, for `c.padd = none`. -/
theorem mulJ4_ok (hc : CfgOk c) (hC : Law c.C) (hO : PrimeOrder c.C) (hpadd : c.padd = none)
    (hbd : 16 * ((2 ^ (64 * c.n) + 135) / 256) + 8 < c.C.n)
    (hw : ∀ w ∈ chainWc c, w = ((winQ c).M.tmp, 8 * c.n) ∨
      ((winQ c).M.mo + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ (winQ c).M.mo) ∧
      ∀ x ∈ winSlots (winQ c), x + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ x)
    (hb : ∀ w ∈ invJW c, c.winBits + 4 * (16 * c.n + 1) ≤ w.1 ∨ w.1 + w.2 ≤ c.winBits)
    (hx : ∀ r ∈ [Reg.x20, .x26, .x27, .x28], r ∉ invJClob c.n ∧ r ∉ clob c.n)
    {dd : Option (Prog isa × Prog isa)} (hD : ∀ base, DblsOk (winQ c) c.C base size dd)
    {ma : Option (Prog isa)} (hMa : ∀ base, MaddOk (winQ c) c.C base size ma)
    {sl : Option (List Instr)} (hS : SelOk (winQ c) size (WinCfg.selOf (winQ c) sl)) :
    MulOk c (Impl.Ecdh.AArch64.Cfg.mulJ4 c dd ma sl) := by
  intro base s hs g F P hP hpx hpy hrep rest R h
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  have hk : wordsVal s.mem base (c.sl K) c.n < 2 ^ (64 * c.n) := wordsVal_lt _ _ _ _
  have hrec := recode_lt hk
  have hWK : c.sl WK + 16 * c.n ≤ size := by
    have := sl_le' c h7 (i := WK + 1) (by decide)
    simp (disch := decide) only [sl_eq] at this ⊢; rw [Nat.mul_add] at this; omega_arith
  have hKW := sl_lt c (show K < WK by decide) (by decide)
  have h16 : (16 : Nat) ^ (16 * c.n + 1) ≤ 2 ^ (64 * (c.n + 1)) := by
    rw [show (16 : Nat) = 2 ^ 4 by rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega_arith)
  have hJ : (winQ c).J = 16 * c.n + 1 := rfl
  have hK : c.winK = c.sl WK := rfl
  have hB : c.winBits = c.sl WB := rfl
  have e69 : c.sl WK + 16 * c.n = c.sl WB := by simp (disch := decide) only [sl_eq]; unfold WK WB; omega_arith
  have hB4 : c.sl WB + 8 ≤ 4096 := by
    simp (disch := decide) only [sl_eq]; unfold WB
    have : 8 * c.n * 55 ≤ 8 * 9 * 55 := Nat.mul_le_mul_right _ (by omega_arith)
    omega_arith
  have hBs : c.sl WB + 64 * (c.n + 1) ≤ c.sl WT := by
    simp (disch := decide) only [sl_eq]; unfold WB WT
    have : 8 * c.n * 87 = 8 * c.n * 55 + 256 * c.n := by omega_arith
    omega_arith
  have hTs := sl_le' c h7 (i := WT) (by decide)
  rw [Impl.Ecdh.AArch64.Cfg.mulJ4]
  apply WP.assoc'
  rw [Cfg.winPrep]
  refine WP.seq (WP.seq ?_)
  rw [hK, offset_eq]
  refine WP.mono (addConst_ok hs (n := c.n) (src := c.sl K) (dst := c.sl WK)
    (c := 8 * geom (16 * c.n + 1)) h0 h7 (sl_le c h7 (by decide)) (by omega_arith) (sl_mod8 c _) (sl_mod8 c _)
    (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (x0_not_clob _)
  rw [hB]
  refine WP.mono (bits_ok hs₁ (n := c.n + 1) (src := c.sl WK) (dst := c.sl WB) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) hB4 (Or.inl (by omega_arith))) fun s₂ ⟨b₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [e₁] at b₂
  have U₂ : Unch base (winX c) s.mem s₂.mem :=
    ((O₁.mono (o' := c.sl WK) (n' := 16 * c.n) (Nat.le_refl _) (by omega_arith)).unch.trans
      ((O₂.mono (o' := c.sl WB) (n' := 64 * (c.n + 1)) (Nat.le_refl _) (by omega_arith)).unch)).mono
      (by intro w hw; simpa [winX, hK, hB] using hw)
  have F₂ := F.unch h7 hn fixedOk_winX U₂
  have e₂ : ∀ {i}, i < 45 → i ≠ TMP → sv c base s₂ i = sv c base s i := fun hi hT =>
    sv_unch U₂ h7 hn hi (apart_winX hi hT)
  have hM₂ := modP_of hc F₂.mp
  have tv : ∀ {i}, i < 45 → i ≠ TMP → tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun hi hT => by
      show toM _ _ (sv c base s₂ _) = toM _ _ (sv c base s _); rw [e₂ hi hT]
  have hF : WinFixed (winQ c) c.C base s₂ P (wordsVal s.mem base (c.sl K) c.n + 8 * geom (16 * c.n + 1)) := by
    refine ⟨?_, ?_, fun x hx => ?_, F₂.zero, ?_, fun t ht => ?_⟩
    · show toM _ _ (wordsVal s₂.mem _ (c.sl AP) c.n) = _; rw [F₂.ap]; exact toM_cmont hc _
    · show toM _ _ (wordsVal s₂.mem _ (c.sl BM) c.n) = _; rw [F₂.bm]; exact toM_cmont hc _
    · simp only [winRo, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact lt_of_eq_of_lt F₂.ap (hmont _)
      · exact lt_of_eq_of_lt F₂.bm (hmont _)
      · exact lt_of_eq_of_lt F₂.zero (by omega_arith)
      · exact lt_of_eq_of_lt (e₂ (i := PX) (by decide) (by decide)) hpx
      · exact lt_of_eq_of_lt (e₂ (i := PY) (by decide) (by decide)) hpy
      · exact lt_of_eq_of_lt F₂.onep (Nat.mod_lt _ (by omega_arith))
    · show Rep _ (tmv c.C c.n base s₂ (c.sl PX)) (tmv c.C c.n base s₂ (c.sl PY))
        (tmv c.C c.n base s₂ (c.sl ONEP)) P
      rw [tv (by decide) (by decide), tv (by decide) (by decide), tv (by decide) (by decide)]; exact hrep
    · rw [hJ] at ht
      exact b₂ t (by omega_arith)
  have hP0 : P ≠ .infinity := by
    intro e
    have hz := (hrep.z_eq_zero_iff).mpr e
    have h1 : tmv c.C c.n base s (c.sl ONEP) = 1 := by
      show toM _ _ (wordsVal s.mem base (c.sl ONEP) c.n) = 1
      rw [F.onep]; exact toM_one hpR
    exact hC.one_ne_zero (h1 ▸ hz)
  have hJ2 : 2 ≤ (winQ c).J := by rw [hJ]; omega_arith
  have hRC : ∀ r ∈ combClob c.n, r ∈ invJClob c.n := fun r hr => List.mem_append_left _ hr
  have hx0 : Reg.x0 ∉ invJClob c.n := fun h' =>
    (List.mem_append.mp h').elim (x0_not_combClob h7) (x0_not_powClob h7)
  refine WP.seq (WP.mono (windowJ_ok (winLayQ hc) (winAQ hc) hpR hC hc.am3 hO hP hP0 hc.p_lt (hmont 1)
    (show toM c.C.p (2 ^ (64 * c.n)) (c.mont 1) = 1 by rw [toM_cmont hc]; rfl) (invJSpec hc hw hb) hRC hx0
    hs₂ hM₂ hF (by rw [hJ]; exact hrec) (Nat.le_add_left _ _) hJ2
    (by rw [hJ]; exact winE_two_bound (by omega_arith) hk hbd) (winAddOk hc)
    (by rw [hpadd]; trivial) (by rw [hpadd]; trivial) (by rw [hpadd]; trivial) (hD base) (hMa base) hS)
    fun s₃ ⟨K₃, U₃, M₃, L₃, R₃⟩ => ?_)
  rw [winW_eq] at U₃
  rw [hJ, Nat.add_sub_cancel] at R₃
  have hs₃ := hs₂.of_keepRegs K₃ hx0
  have rz₃ : wordsVal s₃.mem base (c.sl RZ) c.n < c.C.p := L₃ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  refine WP.seq (WP.mono (pPow_ok hc.toBaseCfgOk hs₃ M₃ rz₃) fun s₄ ⟨K₄, U₄, lt₄, v₄⟩ => h s₄ ?_)
  have r₄ : ∀ {i}, i < 45 → i ∉ [ACC, TMP] → sv c base s₄ i = sv c base s₃ i := fun hi h₁ =>
    sv_unch U₄ h7 hn hi (apart_chainWc hc.toBaseCfgOk hi h₁)
  have U : Unch base (mulJ4W c) s.mem s₄.mem := ((U₂.trans U₃).trans U₄).mono fun w hw => by
    simp only [invJW, List.mem_append, List.mem_singleton] at hw
    simp only [mulJ4W, List.mem_append]
    rcases hw with ((hw | hw | hw | rfl) | hw)
    · exact Or.inl hw
    · exact Or.inr (Or.inl hw)
    · exact Or.inr (Or.inr hw)
    · exact Or.inr (Or.inl (List.mem_map.mpr ⟨TX, by decide, rfl⟩))
    · exact Or.inr (Or.inr hw)
  have hFix : FixedOk c (mulJ4W c) :=
    fixedOk_winX.append ((fixedOk_slW (by decide)).append (fixedOk_chainWc hc.toBaseCfgOk))
  have gr : ∀ r ∈ [Reg.x20, .x26, .x27, .x28], s₄.gpr r = s.gpr r := fun r hr => by
    obtain ⟨h₁, h₂⟩ := hx r hr
    have hpc : r ∉ powClob c.n := fun h' => h₁ (List.mem_append_right _ h')
    have h12 : r ∉ [Reg.x1, .x2, .x5, .x16, .x17, .x19] := fun h' =>
      h₁ (List.mem_append_left _ (combClob_sub r h'))
    rw [K₄.gpr r hpc, K₃.gpr r h₁, k₂.gpr r h12, k₁.gpr r h₂]
  refine ⟨hs₃.of_keepRegs K₄ (x0_not_powClob h7), F.unch h7 hn hFix U,
    fun r hr => gr r (List.mem_cons_of_mem _ hr), gr _ (List.mem_cons_self ..),
    by rw [K₄.rd, K₃.rd, k₂.rd, k₁.rd], by rw [K₄.wr, K₃.wr, k₂.wr, k₁.wr],
    flag_unch_win hc.toBaseCfgOk U h7 h0 hn (by decide),
    sv_unch U h7 hn (i := D) (by decide) (apart_append (apart_winX (by decide))
      (apart_append (apart_slW (by decide)) (apart_chainWc hc.toBaseCfgOk (by decide) (by decide)))),
    fun _ _ => ?_, lt₄, ?_, ?_⟩
  · show Rep _ (toM _ _ (sv c base s₄ RX)) (toM _ _ (sv c base s₄ RY)) (toM _ _ (sv c base s₄ RZ)) _
    rw [r₄ (i := RX) (by decide) (by decide), r₄ (i := RY) (by decide) (by decide),
      r₄ (i := RZ) (by decide) (by decide)]
    exact R₃
  · show _ = toM _ _ (sv c base s₄ RZ) ^ _
    rw [r₄ (i := RZ) (by decide) (by decide)]
    exact v₄
  · rw [r₄ (i := RZ) (by decide) (by decide)]; exact rz₃

end VG.Proof.Ecdh.AArch64
