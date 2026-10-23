module

public import VerifiedGarbage.Proof.Ecdh.AArch64.MulOk
public import VerifiedGarbage.Proof.Ecdh.AArch64.MulJ4
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
import VerifiedGarbage.Proof.Ecdh.AArch64.P521.Window.Double
public import VerifiedGarbage.Impl.Ecdh.P521.AArch64.Window
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase

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

namespace VG.Proof.Ecdh.AArch64.P521.Window

attribute [local instance high] instPowNat

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)

open VG.Impl.Ecdh.AArch64.P521Window

def prepW (c : Cfg) : List (Nat × Nat) := [(3944,16*c.n),(3304,64*(c.n+1))]

def coreW (c : Cfg) : List (Nat × Nat) :=
  prepW c ++ (slW c (otherI ++ tblI ++ [TMP]) ++ chainWc c)

theorem prep_apart {c : Cfg} (h9 : c.n=9)
    {i : Nat} (hi : i<45) (hT : i ≠ TMP) :
    ∀ w ∈ prepW c, c.sl i+8*c.n ≤ w.1 ∨ w.1+w.2 ≤ c.sl i := by
  intro w hw
  rw [sl_eq c i hT]
  simp only [prepW,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl <;> left <;> dsimp only <;> rw [h9] <;> omega

theorem prep_fixed {c : Cfg} (h9 : c.n=9) : FixedOk c (prepW c) := by
  intro w hw
  simp only [prepW,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl <;> right <;> rw [sl_eq c 12 (by decide),h9] <;> decide

/-- `[d]P` by `windowJ`, then the power: `MulOk`, for `c.padd = none`. -/
theorem recode_small {k : Nat} (hk : k < 2^521) : k+8*geom 131 < 16^131 := by
  have hg := geom_mul 131
  have h4 : (2:Nat)^521*4 ≤ 16^131 := by decide +kernel
  omega

theorem core_ok (c : Cfg) (hc : CfgOk c) (h9 : c.n=9)
    (hbd : 16*((2^521+135)/256)+8 < c.C.n) (hpadd : c.padd=none)
    (hL : WinLay (config c) size) (hA : WinA (config c))
    (hInv : ∀ base, InvSpecW (config c) c.C base size (Impl.Ecdh.AArch64.Cfg.invJ c)
      (invJClob c.n) (invJW c)) (hC : Law c.C) (hO : PrimeOrder c.C)
    {base : Addr} {s : State} (hs : Scr s base size) {g : Reg → BitVec 64}
    (F : Fixed c base g s.mem) {P : Point c.C} (hP : onCurve c.C P = true)
    (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P)
    (hkbound : sv c base s K < 2^521) {rest : Prog isa} {R : State → Prop}
    (h : ∀ s', MulPost c base g P (sv c base s K) s s' → WP isa rest s' R) :
    WP isa (.seq (coreFor c) (.seq c.pPow rest)) s R := by
  have hx : ∀ r ∈ [Reg.x20,.x26,.x27,.x28], r ∉ invJClob c.n ∧ r ∉ clob c.n := by rw [h9] <;> decide +kernel
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  have hk : wordsVal s.mem base (c.sl K) c.n < 2^521 := hkbound
  have hrec := recode_small hk
  have hWK : 3944+16*c.n ≤ size := by rw [h9] <;> decide
  have hKW : c.sl K+8*c.n ≤ 3944 := by rw [sl_eq c K (by decide),h9]; decide
  have h16 : (16 : Nat)^131 ≤ 2^(64*(c.n+1)) := by
    rw [h9]
    decide +kernel
  have hJ : (config c).J = 131 := rfl
  have hB4 : 3304+8 ≤ 4096 := by decide
  have hBs : 3304+64*(c.n+1) ≤ 3944 := by rw [h9] <;> decide
  have hTs := sl_le' c h7 (i := WT) (by decide)
  rw [coreFor]
  apply WP.assoc'
  rw [prepFor]
  refine WP.seq (WP.seq ?_)
  rw [offset_eq]
  refine WP.mono (addConst_ok hs (n := c.n) (src := c.sl K) (dst := 3944)
    (c := 8 * geom (131)) h0 h7 (sl_le c h7 (by decide)) (by omega_arith) (sl_mod8 c _) (by decide)
    (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (x0_not_clob _)
  refine WP.mono (bits_ok hs₁ (n := c.n + 1) (src := 3944) (dst := 3304) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) hB4 (Or.inr (by omega_arith))) fun s₂ ⟨b₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [e₁] at b₂
  have U₂ : Unch base (prepW c) s.mem s₂.mem :=
    ((O₁.mono (o' := 3944) (n' := 16 * c.n) (Nat.le_refl _) (by omega_arith)).unch.trans
      ((O₂.mono (o' := 3304) (n' := 64 * (c.n + 1)) (Nat.le_refl _) (by omega_arith)).unch)).mono
      (by intro w hw; simpa [prepW] using hw)
  have F₂ := F.unch h7 hn (prep_fixed h9) U₂
  have e₂ : ∀ {i}, i < 45 → i ≠ TMP → sv c base s₂ i = sv c base s i := fun hi hT =>
    sv_unch U₂ h7 hn hi (prep_apart h9 hi hT)
  have hM₂ := modP_of hc F₂.mp
  have tv : ∀ {i}, i < 45 → i ≠ TMP → tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun hi hT => by
      show toM _ _ (sv c base s₂ _) = toM _ _ (sv c base s _); rw [e₂ hi hT]
  have hF : WinFixed (config c) c.C base s₂ P (wordsVal s.mem base (c.sl K) c.n + 8 * geom (131)) := by
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
  have hJ2 : 2 ≤ (config c).J := by rw [hJ]; omega_arith
  have hRC : ∀ r ∈ combClob c.n, r ∈ invJClob c.n := fun r hr => List.mem_append_left _ hr
  have hx0 : Reg.x0 ∉ invJClob c.n := fun h' =>
    (List.mem_append.mp h').elim (x0_not_combClob h7) (x0_not_powClob h7)
  refine WP.seq (WP.mono (windowJ_ok hL hA hpR hC hc.am3 hO hP hP0 hc.p_lt (hmont 1)
    (show toM c.C.p (2 ^ (64 * c.n)) (c.mont 1) = 1 by rw [toM_cmont hc]; rfl) (hInv base) hRC hx0
    hs₂ hM₂ hF (by rw [hJ]; exact hrec) (Nat.le_add_left _ _) hJ2
    (by rw [hJ]; exact winE_two_bound (d := wordsVal s.mem base (c.sl K) c.n) (J := 131) (b := 521) (n := c.C.n) (by decide) hk hbd) (winAddOk hc)
    (by rw [hpadd]; trivial) (by rw [hpadd]; trivial) (by rw [hpadd]; trivial) (scheduled_doubles hL hA hpR) MaddOk.none (selOk_default (Nat.lt_trans (hmont 1) hc.p_lt)))
    fun s₃ ⟨K₃, U₃, M₃, L₃, R₃⟩ => ?_)
  change Unch base (winW (winQ c) ++ invJW c) s₂.mem s₃.mem at U₃
  rw [winW_eq] at U₃
  rw [hJ, Nat.add_sub_cancel] at R₃
  have hs₃ := hs₂.of_keepRegs K₃ hx0
  have rz₃ : wordsVal s₃.mem base (c.sl RZ) c.n < c.C.p := L₃ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  refine WP.seq (WP.mono (pPow_ok hc.toBaseCfgOk hs₃ M₃ rz₃) fun s₄ ⟨K₄, U₄, lt₄, v₄⟩ => h s₄ ?_)
  have r₄ : ∀ {i}, i < 45 → i ∉ [ACC, TMP] → sv c base s₄ i = sv c base s₃ i := fun hi h₁ =>
    sv_unch U₄ h7 hn hi (apart_chainWc hc.toBaseCfgOk hi h₁)
  have U : Unch base (coreW c) s.mem s₄.mem := ((U₂.trans U₃).trans U₄).mono fun w hw => by
    simp only [invJW, List.mem_append, List.mem_singleton] at hw
    simp only [coreW, List.mem_append]
    rcases hw with ((hw | hw | hw | rfl) | hw)
    · exact Or.inl hw
    · exact Or.inr (Or.inl hw)
    · exact Or.inr (Or.inr hw)
    · exact Or.inr (Or.inl (List.mem_map.mpr ⟨TX, by decide, rfl⟩))
    · exact Or.inr (Or.inr hw)
  have hFix : FixedOk c (coreW c) :=
    (prep_fixed h9).append ((fixedOk_slW (by decide)).append (fixedOk_chainWc hc.toBaseCfgOk))
  have gr : ∀ r ∈ [Reg.x20, .x26, .x27, .x28], s₄.gpr r = s.gpr r := fun r hr => by
    obtain ⟨h₁, h₂⟩ := hx r hr
    have hpc : r ∉ powClob c.n := fun h' => h₁ (List.mem_append_right _ h')
    have h12 : r ∉ [Reg.x1, .x2, .x5, .x16, .x17, .x19] := fun h' =>
      h₁ (List.mem_append_left _ (combClob_sub r h'))
    rw [K₄.gpr r hpc, K₃.gpr r h₁, k₂.gpr r h12, k₁.gpr r h₂]
  refine ⟨hs₃.of_keepRegs K₄ (x0_not_powClob h7), F.unch h7 hn hFix U,
    fun r hr => gr r (List.mem_cons_of_mem _ hr), gr _ (List.mem_cons_self ..),
    by rw [K₄.rd, K₃.rd, k₂.rd, k₁.rd], by rw [K₄.wr, K₃.wr, k₂.wr, k₁.wr],
    (by
      apply U.word (d := c.sl FLAG)
      · intro w hw
        have ha := apart_append (prep_apart h9 (i := FLAG) (by decide) (by decide))
          (apart_append (apart_slW (c := c) (i := FLAG) (l := otherI++tblI++[TMP]) (by decide))
            (apart_chainWc hc.toBaseCfgOk (i := FLAG) (by decide) (by decide))) w hw
        rcases ha with ha | ha
        · left; have := hc.n0; omega
        · exact .inr ha
      · have := sl_le c h7 (i := FLAG) (by decide); omega),
    sv_unch U h7 hn (i := D) (by decide) (apart_append (prep_apart h9 (by decide) (by decide))
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

end VG.Proof.Ecdh.AArch64.P521.Window
