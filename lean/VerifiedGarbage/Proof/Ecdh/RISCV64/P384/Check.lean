module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.Masks
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.MulFn
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Impl.Ecdh.P384.RISCV64
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_p384_check_point` on RISC-V: correctness

The check (`Impl/Ecdh/RISCV64.lean`) on P-384's slots: the masks of
`x < p` and `y < p` anded into the flag (`ltMask_ok`, `andFlag_ok`), `x` and
`y` in Montgomery's form by multiplications by `R² mod p` (`mulCall_ok`),
`y² - (x³ + a x + b)` by field operations (`fprog_ok`), whose mask of being
zero goes into the flag too, and the point the scalar multiplication takes,
selected by the flag (`sel_ok`).
-/

@[expose] public section

-- `p`, below `2^384`, is evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.Ecdh.RISCV64.P384

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.P384
open VG.Proof.X25519.RISCV64 (Rest wp_and)
open VG.Spec.Weierstrass (Curve Fe Point)

/-- The flag's offset. -/
abbrev FL : Nat := 2176

theorem sl_FLAG : p384.sl FLAG = FL := rfl

theorem sl_eq (i : Nat) : p384.sl i = 64 + 48 * i := by simp only [Cfg.sl, slot, p384]

/-- The flag `&=` the mask `a7`. -/
theorem andFlag_ok {s : State} {base : Addr} (hw : WsReg s base) :
    WP isa (.block (Cfg.andFlag p384)) s fun s' =>
      word s'.mem base FL = word s.mem base FL &&& s.gpr .a7 ∧ Rest [.t0] s s' ∧ Outside base FL 8 s.mem s'.mem := by
  rw [Cfg.andFlag, sl_FLAG]
  refine ldAt_ws hw (d := FL) (by decide) (by decide) fun s₁ u₁ => wp_and fun s₂ u₂ => ?_
  have r₂ : Rest [.t0] s s₂ := (u₁.rest (by decide)).trans (u₂.rest (by decide))
  refine sdAt_ws (hw.of_rest r₂) (by decide) (d := FL) (by decide) (by decide) fun s₃ u₃ => WP.block_nil ⟨?_, r₂.trans (u₃.rest _), ?_⟩
  · rw [u₃.mem, word_writeW_self, u₂.gpr, u₁.gpr, u₁.other .a7 (by decide)]
  · rw [u₃.mem, u₂.mem, u₁.mem]; exact writeW_outside _ _ _ (by decide)

/-- The masks of `x < p` and `y < p` into the flag. -/
theorem masks_ok {s : State} {base : Addr} (hw : WsReg s base) :
    WP isa (.block (ltMask 6 (p384.sl CX) (p384.sl MP) ++ Cfg.andFlag p384 ++ ltMask 6 (p384.sl CY) (p384.sl MP) ++
      Cfg.andFlag p384)) s fun s' =>
      Kp s s' ∧ Outside base FL 8 s.mem s'.mem ∧
      word s'.mem base FL = word s.mem base FL &&& maskOf (decide (sv base s CX < sv base s MP)) &&&
        maskOf (decide (sv base s CY < sv base s MP)) := by
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (ltMask_ok hw (n := 6) (a := p384.sl CX) (m := p384.sl MP) (by decide)
    (by decide) (by decide) (by decide)) fun s₁ ⟨r₁, m₁, g₁⟩ => ?_)
  have hw₁ := hw.of_rest r₁
  refine WP.block_append (WP.mono (andFlag_ok hw₁) fun s₂ ⟨f₂, r₂, O₂⟩ => ?_)
  have hw₂ := hw₁.of_rest r₂
  refine WP.block_append (WP.mono (ltMask_ok hw₂ (n := 6) (a := p384.sl CY) (m := p384.sl MP) (by decide)
    (by decide) (by decide) (by decide)) fun s₃ ⟨r₃, m₃, g₃⟩ => ?_)
  have hw₃ := hw₂.of_rest r₃
  refine WP.mono (andFlag_ok hw₃) fun s₄ ⟨f₄, r₄, O₄⟩ => ⟨?_, ?_, ?_⟩
  · exact (Kp.of_rest r₁).trans ((Kp.of_rest r₂).trans ((Kp.of_rest r₃).trans (Kp.of_rest r₄)))
  · rw [← m₁]; exact O₂.trans (by rw [← m₃]; exact O₄)
  · have e : ∀ i, i < 44 → sv base s₂ i = sv base s i := fun i hi => by
      show wordsVal s₂.mem _ _ _ = _
      rw [O₂.wordsVal (by rw [sl_eq, FL]; omega) (by rw [sl_eq]; omega), m₁]
    rw [f₄, m₃, g₃, f₂, m₁, g₁]
    simp only [sv] at e ⊢
    rw [show wordsVal s₂.mem base (p384.sl CY) 6 = _ from e CY (by decide),
      show wordsVal s₂.mem base (p384.sl MP) 6 = _ from e MP (by decide)]

/-- The slots of the curve's equation. -/
abbrev curveSlots : List Nat :=
  [p384.sl AP, p384.sl BP, p384.sl CXM, p384.sl CYM, p384.sl W0, p384.sl W1, p384.sl W2, p384.sl CPX]

theorem curveLay : Lay p384.MP' (own 6) (· ∈ curveSlots) :=
  ⟨by decide, fun x y hx hy => (by decide : ∀ x ∈ curveSlots, ∀ y ∈ curveSlots,
      x ≠ y → x + 8 * p384.MP'.n ≤ y ∨ y + 8 * p384.MP'.n ≤ x) x hx y hy, by decide, by decide⟩

theorem curveShort : Short (· ∈ curveSlots) := by decide

theorem curve_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps (Cfg.curveOps p384) e (p384.sl W1) =
      e (p384.sl CYM) * e (p384.sl CYM) - ((e (p384.sl CXM) * e (p384.sl CXM) * e (p384.sl CXM) +
        e (p384.sl AP) * e (p384.sl CXM)) + e (p384.sl BP)) := by
  simp only [Cfg.curveOps, runOps_cons, runOps_nil, FOp.run, Function.update_apply, sl_eq]
  simp only [W0, W1, W2, CYM, CXM, AP, BP, CPX, Nat.reduceMul, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]

/-- `y² - (x³ + a x + b)` to `W1`. -/
theorem curve_ok {s : State} {base : Addr} (hw : WsReg s base)
    (hlt : ∀ x ∈ [CXM, CYM, AP, BP], sv base s x < W.p) :
    WP isa (fprog p384Field (Cfg.curveOps p384)) s fun s' =>
      KeepR 6 base ((Cfg.curveOps p384).map FOp.out) s s' ∧
      sv base s' W1 < W.p ∧
      toM W.p (2 ^ 384) (sv base s' W1) =
        toM W.p (2 ^ 384) (sv base s CYM) * toM W.p (2 ^ 384) (sv base s CYM) -
          ((toM W.p (2 ^ 384) (sv base s CXM) * toM W.p (2 ^ 384) (sv base s CXM) *
            toM W.p (2 ^ 384) (sv base s CXM) + toM W.p (2 ^ 384) (sv base s AP) *
            toM W.p (2 ^ 384) (sv base s CXM)) + toM W.p (2 ^ 384) (sv base s BP)) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt
  refine WP.mono (fprog_ok (M := p384.MP') (F := p384Field) field_ok rfl curveLay curveShort unit
    (Cfg.curveOps p384) (V := [p384.sl CXM, p384.sl CYM, p384.sl AP, p384.sl BP])
    (E := fun x => toM W.p (2 ^ 384) (wordsVal s.mem base x 6)) ⟨hw, by decide, fun x hx => ?_, fun _ _ => rfl⟩
    (by decide) (by decide)) fun s' ⟨K, I⟩ => ⟨K, I.lt _ (by decide), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hlt.1
    · exact hlt.2.1
    · exact hlt.2.2.1
    · exact hlt.2.2.2
  · have v := I.val (p384.sl W1) (by decide)
    exact v.trans (curve_run (F := Fe W) _)

/-! ## The whole check -/

/-- A slot apart from what changed. -/
theorem sv_unch {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (U : Unch base W m m') (i : Nat)
    (h : ∀ w ∈ W, p384.sl i + 48 ≤ w.1 ∨ w.1 + w.2 ≤ p384.sl i) (hi : i < 100 := by decide) :
    wordsVal m' base (p384.sl i) 6 = wordsVal m base (p384.sl i) 6 :=
  U.wordsVal h (by rw [sl_eq]; omega)

/-- The flag, apart from what changed. -/
theorem fl_unch {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (U : Unch base W m m')
    (h : ∀ w ∈ W, FL + 8 ≤ w.1 ∨ w.1 + w.2 ≤ FL) : word m' base FL = word m base FL :=
  U.word h (by decide)

theorem maskOf_and (a b : Bool) : maskOf a &&& maskOf b = maskOf (a && b) := by
  cases a <;> cases b <;> decide

/-- `toM` is injective on numbers below `m`. -/
theorem toM_inj {m R : Nat} [NeZero m] (hR : UnitMod m R) {x y : Nat} (hx : x < m) (hy : y < m)
    (h : toM m R x = toM m R y) : x = y := by
  have e := congrArg (· * Fin.ofNat m R) h
  simp only [toM] at e
  rw [Lean.Grind.Semiring.mul_assoc, Lean.Grind.Semiring.mul_assoc, Lean.Grind.CommSemiring.mul_comm (rinv m R),
    mul_rinv hR, Lean.Grind.Semiring.mul_one, Lean.Grind.Semiring.mul_one] at e
  have := (ofNat_eq_ofNat (m := m)).mp e
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

/-- A Montgomery multiplication by `R² mod p` gives `x R mod p`. -/
theorem mont_eq {r x : Nat} (hr : r < W.p) (h : r * 2 ^ 384 % W.p = x * (2 ^ 384 * 2 ^ 384 % W.p) % W.p) :
    r = x * 2 ^ 384 % W.p :=
  toM_inj unit hr (Nat.mod_lt _ (by decide)) ((toM_r2 unit h).trans (toM_mont unit).symm)

/-- P-384's check of `Proof/Weierstrass/CheckPointContract.lean`. -/
abbrev CC : Impl.Weierstrass.CheckPoint.Curve := Impl.Weierstrass.CheckPoint.p384

/-- `vg_p384_check_point(ws = a0)`. -/
def checkRVc : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .a0, 8192⟩] ∧ (s.gpr .a0).toNat + 8192 ≤ 2 ^ 64 ∧
    (s.gpr .a0).toNat % 8 = 0 ∧ CC.pre (s.gpr .a0) s.mem
  post s s' := CC.post (s.gpr .a0) s.mem s'.mem
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0

theorem num_eq (m : Mem) (ws : Addr) (i : Nat) (hi : i < 100 := by decide) :
    CC.num ws m (CC.slot i) = wordsVal m ws (p384.sl i) 6 := by
  unfold Impl.Weierstrass.CheckPoint.Curve.num
  rw [Impl.Weierstrass.Mont.numAt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
    simp only [Impl.Weierstrass.CheckPoint.Curve.slot, CC, Impl.Weierstrass.CheckPoint.p384]; omega)]
  exact read_eq_wordsVal m ws 6 _

theorem flag_eq (m : Mem) (ws : Addr) : CC.flag ws m = word m ws FL := by
  unfold Impl.Weierstrass.CheckPoint.Curve.flag
  simp only [word, off, Mem.readW]
  rfl

/-- The writes of the check: its own working space or its results. -/
abbrev chkW : List (Nat × Nat) :=
  ((([(160, 8), (168, 8)] ++ [(FL, 8)]) ++ [(p384.sl CXM, 48), (own 6, 384)]) ++ [(p384.sl CYM, 48), (own 6, 384)]) ++
    (((Cfg.curveOps p384).map FOp.out).map (fun w => (w, 8 * 6)) ++ [(own 6, 64 * 6)]) ++
    [(FL, 8), (p384.sl CPX, 48), (p384.sl CPY, 48)]

theorem keeps_of_unch {ws : Addr} {m m' : Mem} (hu : Unch ws chkW m m') : CC.Keeps ws m m' := by
  intro i hi hown hout
  have h8 : Impl.Weierstrass.Mont.wsBytes = 8192 := rfl
  refine hu _ fun w hw => ?_
  rw [show ws + BitVec.ofNat 64 i = off ws i from rfl, ofs_off0 ws (by omega)]
  have hw' := (by decide : ∀ w ∈ chkW, (160 ≤ w.1 ∧ w.1 + w.2 ≤ 208) ∨ (w.1 = FL ∧ w.2 = 8) ∨
    (∃ j ∈ [34, 35, 37, 38, 41, 42, 43], w.1 = 64 + 48 * j ∧ w.2 = 48) ∨ (3712 ≤ w.1 ∧ w.1 + w.2 ≤ 4096)) w hw
  simp only [FL, Impl.Weierstrass.CheckPoint.Curve.Own, Impl.Weierstrass.CheckPoint.Curve.Out,
    Impl.Weierstrass.CheckPoint.Curve.slot, Impl.Weierstrass.CheckPoint.Curve.flagAt, CC,
    Impl.Weierstrass.CheckPoint.p384, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes,
    List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, not_or] at hown hout hw'
  omega

/-- The validity the masks compute. -/
theorem masks_valid {x y w1 xm ym : Nat} (hw1 : w1 < W.p)
    (hxm : xm = x * 2 ^ 384 % W.p) (hym : ym = y * 2 ^ 384 % W.p)
    (hv : toM W.p (2 ^ 384) w1 = toM W.p (2 ^ 384) ym * toM W.p (2 ^ 384) ym -
      ((toM W.p (2 ^ 384) xm * toM W.p (2 ^ 384) xm * toM W.p (2 ^ 384) xm +
        Fin.ofNat W.p W.a * toM W.p (2 ^ 384) xm) + Fin.ofNat W.p W.b)) :
    maskOf (decide (x < W.p)) &&& maskOf (decide (y < W.p)) &&& maskOf (decide (w1 = 0)) =
      Impl.Weierstrass.CheckPoint.Curve.mask (CC.Valid x y) := by
  rw [hxm, hym, toM_mont unit, toM_mont unit] at hv
  unfold Impl.Weierstrass.CheckPoint.Curve.mask Impl.Weierstrass.CheckPoint.Curve.Valid
  show _ = if x < W.p ∧ y < W.p ∧ Spec.Weierstrass.onCurve W (.affine (Fin.ofNat W.p x) (Fin.ofNat W.p y)) = true
    then BitVec.allOnes 64 else 0
  by_cases hx : x < W.p
  · by_cases hy : y < W.p
    · have e : w1 = 0 ↔ VG.Proof.Ecdh.OnCurveF W x y := by
        rw [← toM_eq_zero_iff unit hw1, hv]
      have ex : (Fin.ofNat W.p x : Fe W) = ⟨x, hx⟩ := VG.Proof.EcKey.fe_eq hx rfl
      have ey : (Fin.ofNat W.p y : Fe W) = ⟨y, hy⟩ := VG.Proof.EcKey.fe_eq hy rfl
      have hc : Spec.Weierstrass.onCurve W (.affine (Fin.ofNat W.p x) (Fin.ofNat W.p y)) = true ↔ w1 = 0 := by
        rw [ex, ey, VG.Proof.Ecdh.onCurve_iff hx hy, ← e]
      by_cases h0 : w1 = 0 <;> simp [hx, hy, h0, hc, maskOf]
    · simp [hy, maskOf]
  · simp [hx, maskOf]

/-- `vg_p384_check_point` meets `checkRVc`. -/
theorem check_rv (s : State) (hs : checkRVc.pre s) :
    ∃ t s', Exec isa checkP384 s t s' ∧ abiPreserved s s' ∧ checkRVc.post s s' := by
  obtain ⟨-, hwr, hfit, hal, ⟨hp, hr2, ha, hb, hf⟩⟩ := hs
  generalize hb0 : s.gpr .a0 = base at hwr hfit hal hp hr2 ha hb hf
  have hwr' : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_singleton_self _
  suffices h : WP isa checkP384 s fun s' => abiPreserved s s' ∧ checkRVc.post s s' by
    obtain ⟨t, s', he, h⟩ := h; exact ⟨t, s', he, h⟩
  rw [checkP384, Cfg.checkFn, show Cfg.checkSave p384 = 160 from rfl]
  refine WP.seq (sd_a0 hb0 hwr' hal (d := 160) (by decide) (by decide) fun s₁ u₁ => ?_)
  refine sd_a0 (by rw [u₁.gpr]; exact hb0) (by rw [u₁.wr]; exact hwr') hal (d := 168) (by decide) (by decide)
    fun s₂ u₂ => wp_mv fun s₃ u₃ => WP.block_nil ?_
  have g₃ : ∀ r, r ≠ .s0 → s₃.gpr r = s.gpr r := fun r hr => by rw [u₃.other r hr, u₂.gpr, u₁.gpr]
  have hw₃ : WsReg s₃ base := ⟨by rw [u₃.gpr, u₂.gpr, u₁.gpr, hb0], by rw [u₃.wr, u₂.wr, u₁.wr]; exact hwr',
    hfit, hal⟩
  have m₃ : s₃.mem = (s.mem.writeW (off base 160) (s.gpr .s0)).writeW (off base 168) (s.gpr .ra) := by
    simp only [u₃.mem, u₂.mem, u₁.mem, u₁.gpr]
  have U₃ : Unch base [(160, 8), (168, 8)] s.mem s₃.mem := by
    rw [m₃]; exact (writeW_outside _ _ _ (by decide)).unch.trans (writeW_outside _ _ _ (by decide)).unch
  -- The masks.
  refine WP.seq (WP.mono (masks_ok hw₃) fun s₄ ⟨K₄, O₄, f₄⟩ => ?_)
  have hw₄ := hw₃.of_kp K₄
  have U₄ := U₃.trans O₄.unch
  -- `x R` and `y R`.
  have hr2' : sv base s₄ R2P = 2 ^ 384 * 2 ^ 384 % W.p := by
    rw [show sv base s₄ R2P = sv base s R2P from sv_unch U₄ R2P (by decide)]
    exact (num_eq s.mem base R2P).symm.trans hr2
  refine WP.seq (WP.mono (mulCall_ok field_ok hw₄ (o := p384.sl CXM) (a := p384.sl CX) (b := p384.sl R2P)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by show sv base s₄ R2P < W.p; rw [hr2']; exact Nat.mod_lt _ (by decide)))
    fun s₅ ⟨C₅, lt₅, e₅⟩ => ?_)
  have hw₅ := hw₄.of_kp C₅.kp
  have U₅ : Unch base [(p384.sl CXM, 48), (own 6, 384)] s₄.mem s₅.mem := C₅.mem
  refine WP.seq (WP.mono (mulCall_ok field_ok hw₅ (o := p384.sl CYM) (a := p384.sl CY) (b := p384.sl R2P)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by show sv base s₅ R2P < W.p; rw [show sv base s₅ R2P = sv base s₄ R2P from sv_unch U₅ R2P (by decide), hr2']; exact Nat.mod_lt _ (by decide)))
    fun s₆ ⟨C₆, lt₆, e₆⟩ => ?_)
  have hw₆ := hw₅.of_kp C₆.kp
  have U₆ : Unch base [(p384.sl CYM, 48), (own 6, 384)] s₅.mem s₆.mem := C₆.mem
  -- The values so far, from the contract's.
  have x₄ : sv base s₄ CX = CC.num base s.mem CC.xAt := by
    rw [show sv base s₄ CX = sv base s CX from sv_unch U₄ CX (by decide)]; exact (num_eq s.mem base CX).symm
  have y₅ : sv base s₅ CY = CC.num base s.mem CC.yAt := by
    rw [show sv base s₅ CY = sv base s CY from sv_unch (U₄.trans U₅) CY (by decide)]; exact (num_eq s.mem base CY).symm
  have xm₆ : sv base s₆ CXM = CC.num base s.mem CC.xAt * 2 ^ 384 % W.p := by
    rw [show sv base s₆ CXM = sv base s₅ CXM from sv_unch U₆ CXM (by decide), ← x₄]
    refine mont_eq lt₅ (e₅.trans ?_)
    show sv base s₄ CX * sv base s₄ R2P % W.p = _
    rw [hr2']
  have ym₆ : sv base s₆ CYM = CC.num base s.mem CC.yAt * 2 ^ 384 % W.p := by
    rw [← y₅]
    refine mont_eq lt₆ (e₆.trans ?_)
    show sv base s₅ CY * sv base s₅ R2P % W.p = _
    rw [show sv base s₅ R2P = sv base s₄ R2P from sv_unch U₅ R2P (by decide), hr2']
  have ap₆ : sv base s₆ AP = W.a * 2 ^ 384 % W.p := by
    rw [show sv base s₆ AP = sv base s AP from sv_unch ((U₄.trans U₅).trans U₆) AP (by decide)]
    exact (num_eq s.mem base AP).symm.trans ha
  have bp₆ : sv base s₆ BP = W.b * 2 ^ 384 % W.p := by
    rw [show sv base s₆ BP = sv base s BP from sv_unch ((U₄.trans U₅).trans U₆) BP (by decide)]
    exact (num_eq s.mem base BP).symm.trans hb
  have hp0 : 0 < W.p := by decide
  -- The curve's equation.
  refine WP.seq (WP.mono (curve_ok hw₆ (fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rw [xm₆]; exact Nat.mod_lt _ hp0
    · rw [ym₆]; exact Nat.mod_lt _ hp0
    · rw [ap₆]; exact Nat.mod_lt _ hp0
    · rw [bp₆]; exact Nat.mod_lt _ hp0)) fun s₇ ⟨K₇, lt₇, v₇⟩ => ?_)
  have hw₇ := hw₆.of_kp K₇.kp
  have U₇ : Unch base (((Cfg.curveOps p384).map FOp.out).map (fun w => (w, 8 * 6)) ++ [(own 6, 64 * 6)])
      s₆.mem s₇.mem := K₇.mem
  -- The mask of the equation, and the flag.
  rw [show p384.n = 6 from rfl]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (zeroMask_ok hw₇ (n := 6) (a := p384.sl W1) (by decide) (by decide))
    fun s₈ ⟨r₈, m₈, g₈⟩ => ?_)
  have hw₈ := hw₇.of_rest r₈
  refine WP.block_append (WP.mono (andFlag_ok hw₈) fun s₉ ⟨f₉, r₉, O₉⟩ => ?_)
  have hw₉ := hw₈.of_rest r₉
  refine ldAt_ws hw₉ (d := p384.sl FLAG) (by decide) (by decide) fun s₁₀ u₁₀ => ?_
  have hw₁₀ := hw₉.of_kp (Kp.of_upd u₁₀)
  -- The flag's value.
  have U₃₇ := ((U₄.trans U₅).trans U₆).trans U₇
  have fl₇ : word s₇.mem base FL = word s₄.mem base FL :=
    fl_unch ((U₅.trans U₆).trans U₇) (by decide)
  have fl₃ : word s₃.mem base FL = word s.mem base FL := fl_unch U₃ (by decide)
  have e₃ : ∀ i, i < 44 → i ≠ 2 → sv base s₃ i = sv base s i := fun i hi h2 => by
    show wordsVal _ _ _ _ = _
    rw [U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> (simp only; rw [sl_eq]; omega)) (by rw [sl_eq]; omega)]
  have hpw : sv base s MP = W.p := (num_eq s.mem base MP).symm.trans hp
  rw [e₃ CX (by decide) (by decide), e₃ CY (by decide) (by decide), e₃ MP (by decide) (by decide), hpw,
    fl₃] at f₄
  have hxv : sv base s CX = CC.num base s.mem CC.xAt := (num_eq s.mem base CX).symm
  have hyv : sv base s CY = CC.num base s.mem CC.yAt := (num_eq s.mem base CY).symm
  rw [hxv, hyv] at f₄
  have hv := masks_valid lt₇ xm₆ ym₆ (by rw [v₇, ap₆, bp₆, toM_mont unit, toM_mont unit])
  generalize hx : CC.num base s.mem CC.xAt = x at *
  generalize hy : CC.num base s.mem CC.yAt = y at *
  have hF : word s₉.mem base FL = CC.flag base s.mem &&& Impl.Weierstrass.CheckPoint.Curve.mask (CC.Valid x y) := by
    rw [f₉, m₈, g₈, fl₇, f₄, flag_eq, ← hv]; simp only [BitVec.and_assoc]
  generalize hFv : CC.flag base s.mem &&& Impl.Weierstrass.CheckPoint.Curve.mask (CC.Valid x y) = F at hF
  have hFm : F = if decide (F ≠ 0) then BitVec.allOnes 64 else 0 := by
    rw [← hFv]
    unfold Impl.Weierstrass.CheckPoint.Curve.mask
    rcases hf with h | h <;> rw [h] <;> split <;> decide
  have a₁₀ : s₁₀.gpr .a7 = if decide (F ≠ 0) then BitVec.allOnes 64 else 0 := by
    rw [u₁₀.gpr]; exact hF.trans hFm
  -- The point.
  refine WP.block_append (WP.mono (sel_ok (decide (F ≠ 0)) 6 hw₁₀ a₁₀ (o := p384.sl CPX) (a := p384.sl GX)
    (b := p384.sl CXM) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun s₁₁ ⟨e₁₁, r₁₁, O₁₁⟩ => ?_)
  have hw₁₁ := hw₁₀.of_rest r₁₁
  have a₁₁ : s₁₁.gpr .a7 = if decide (F ≠ 0) then BitVec.allOnes 64 else 0 := by
    rw [r₁₁.gpr _ (by decide), a₁₀]
  refine WP.block_append (WP.mono (sel_ok (decide (F ≠ 0)) 6 hw₁₁ a₁₁ (o := p384.sl CPY) (a := p384.sl GY)
    (b := p384.sl CYM) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun s₁₂ ⟨e₁₂, r₁₂, O₁₂⟩ => ?_)
  have hw₁₂ := hw₁₁.of_rest r₁₂
  -- What changed.
  have U₉ : Unch base [(FL, 8)] s₇.mem s₉.mem := by rw [← m₈]; exact O₉.unch
  have m₁₀ : s₁₀.mem = s₉.mem := u₁₀.mem
  have Uend : Unch base [(FL, 8), (p384.sl CPX, 48), (p384.sl CPY, 48)] s₇.mem s₁₂.mem := by
    have := (U₉.trans (by rw [← m₁₀]; exact O₁₁.unch)).trans O₁₂.unch
    exact this
  have U₆₁₂ := U₇.trans Uend
  have Uall : Unch base chkW s.mem s₁₂.mem := U₃₇.trans Uend
  -- The loads.
  have far : ∀ d ∈ [160, 168], word s₁₂.mem base d = word s₃.mem base d := fun d hd => by
    have U := ((((O₄.unch.trans U₅).trans U₆).trans U₇).trans Uend)
    refine U.word (fun w hw => ?_) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; omega)
    have := (by decide : ∀ w ∈ (((([(FL, 8)] ++ [(p384.sl CXM, 48), (own 6, 384)]) ++
        [(p384.sl CYM, 48), (own 6, 384)]) ++
        (((Cfg.curveOps p384).map FOp.out).map (fun w => (w, 8 * 6)) ++ [(own 6, 64 * 6)])) ++
        [(FL, 8), (p384.sl CPX, 48), (p384.sl CPY, 48)]), 176 ≤ w.1) w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    omega
  have w36 : word s₁₂.mem base 168 = s.gpr .ra := by rw [far 168 (by simp), m₃, word_writeW_self]
  have w28 : word s₁₂.mem base 160 = s.gpr .s0 := by
    rw [far 160 (by simp), m₃, (writeW_outside (d := 168) _ base _ (by omega)).word (by omega) (by omega),
      word_writeW_self]
  have Kp₁₂ : Kp s₃ s₁₂ := K₄.trans (C₅.kp.trans (C₆.kp.trans (K₇.kp.trans ((Kp.of_rest r₈).trans
    ((Kp.of_rest r₉).trans ((Kp.of_upd u₁₀).trans ((Kp.of_rest r₁₁).trans (Kp.of_rest r₁₂))))))))
  refine ldAt_ws hw₁₂ (d := 168) (by decide) (by decide) fun s₁₃ u₁₃ => ?_
  have hw₁₃ := hw₁₂.of_kp (Kp.of_upd u₁₃)
  refine ldAt_ws hw₁₃ (d := 160) (by decide) (by decide) fun s₁₄ u₁₄ => WP.block_nil ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · by_cases h0 : r = .s0
    · subst h0; rw [u₁₄.gpr, u₁₃.mem, w28]
    rw [u₁₄.other _ h0, u₁₃.other _ (fun e => by subst e; revert hr; decide), Kp₁₂.gpr r hr, g₃ r h0]
  · rw [u₁₄.sp, u₁₃.sp, Kp₁₂.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₁₄.other _ (by decide), u₁₃.gpr, w36]
  · have m₁₄ : s₁₄.mem = s₁₂.mem := by rw [u₁₄.mem, u₁₃.mem]
    show CC.post (s.gpr .a0) s.mem s₁₄.mem
    rw [hb0, m₁₄]
    have xm : sv base s₁₂ CXM = x * 2 ^ 384 % W.p := by
      rw [show sv base s₁₂ CXM = sv base s₆ CXM from sv_unch U₆₁₂ CXM (by decide), xm₆]
    have ym : sv base s₁₂ CYM = y * 2 ^ 384 % W.p := by
      rw [show sv base s₁₂ CYM = sv base s₆ CYM from sv_unch U₆₁₂ CYM (by decide), ym₆]
    refine ⟨?_, ?_, ?_, ?_, ?_, keeps_of_unch Uall⟩
    · have U' : Unch base ([(p384.sl CPX, 8 * 6)] ++ [(p384.sl CPY, 8 * 6)]) s₉.mem s₁₂.mem := by
        rw [← m₁₀]; exact O₁₁.unch.trans O₁₂.unch
      rw [flag_eq, fl_unch U' (by decide), hF, hx, hy, hFv]
    · rw [hx]
      refine (num_eq _ _ CXM).trans (xm.trans ?_)
      rfl
    · rw [hy]
      refine (num_eq _ _ CYM).trans (ym.trans ?_)
      rfl
    · have U' : Unch base ([(p384.sl CPX, 8 * 6)] ++ [(p384.sl CPY, 8 * 6)]) s₁₀.mem s₁₂.mem :=
        O₁₁.unch.trans O₁₂.unch
      have U'' := U₃₇.trans U₉
      rw [← m₁₀] at U''
      have h1 : sv base s₁₂ CPX = sv base s₁₁ CPX := sv_unch O₁₂.unch CPX (by decide)
      have h2 : sv base s₁₀ CXM = sv base s₁₂ CXM := (sv_unch U' CXM (by decide)).symm
      have h3 : sv base s₁₀ GX = sv base s GX := sv_unch U'' GX (by decide)
      rw [hx, hy, hFv, show CC.pxAt = CC.slot CPX from rfl, show CC.gxAt = CC.slot GX from rfl, num_eq _ _ CPX,
        num_eq _ _ GX]
      show sv base s₁₂ CPX = if F = 0 then sv base s GX else _
      rw [h1]; show wordsVal s₁₁.mem _ _ _ = _; rw [e₁₁]
      show (if decide (F ≠ 0) = true then sv base s₁₀ CXM else sv base s₁₀ GX) = _
      rw [h2, h3, xm]
      by_cases h : F = 0 <;> simp [h] <;> rfl
    · have O' := O₁₁
      rw [m₁₀] at O'
      have U'' := (U₃₇.trans U₉).trans O'.unch
      have h2 : sv base s₁₁ CYM = sv base s₁₂ CYM := (sv_unch O₁₂.unch CYM (by decide)).symm
      have h3 : sv base s₁₁ GY = sv base s GY := sv_unch U'' GY (by decide)
      rw [hx, hy, hFv, show CC.pyAt = CC.slot CPY from rfl, show CC.gyAt = CC.slot GY from rfl, num_eq _ _ CPY,
        num_eq _ _ GY]
      show wordsVal s₁₂.mem _ _ _ = if F = 0 then sv base s GY else _
      rw [e₁₂]
      show (if decide (F ≠ 0) = true then sv base s₁₁ CYM else sv base s₁₁ GY) = _
      rw [h2, h3, ym]
      by_cases h : F = 0 <;> simp [h] <;> rfl

end VG.Proof.Ecdh.RISCV64.P384
