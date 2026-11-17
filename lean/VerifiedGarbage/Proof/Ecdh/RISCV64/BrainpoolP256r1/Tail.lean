module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP256r1.MulVerified
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP256r1.MulLit
import VerifiedGarbage.Proof.Weierstrass.PointFacts
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ecdh.RISCV64.Masks
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP256r1.MulFn
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP256r1.RISCV64
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Mont.Read

/-! ### `Ecdh.RISCV64.BrainpoolP256r1.Check`, which this module and modules that import it used -/

section

/-!
# `vg_brainpoolp256r1_check_point` on RISC-V: correctness

The check (`Impl/Ecdh/RISCV64.lean`) on brainpoolP256r1's slots: the masks of
`x < p` and `y < p` anded into the flag (`ltMask_ok`, `andFlag_ok`), `x` and
`y` in Montgomery's form by multiplications by `R² mod p` (`mulCall_ok`),
`y² - (x³ + a x + b)` by field operations (`fprog_ok`), whose mask of being
zero goes into the flag too, and the point the scalar multiplication takes,
selected by the flag (`sel_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdh.RISCV64.BrainpoolP256r1

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.BrainpoolP256r1
open VG.Proof.X25519.RISCV64 (Rest wp_and)
open VG.Spec.Weierstrass (Curve Fe Point)

/-- The flag's offset. -/
abbrev FL : Nat := 1472

theorem sl_FLAG : brainpoolp256r1.sl FLAG = FL := rfl

theorem sl_eq (i : Nat) : brainpoolp256r1.sl i = 64 + 32 * i := by simp only [Cfg.sl, slot, brainpoolp256r1]

/-- The flag `&=` the mask `a7`. -/
theorem andFlag_ok {s : State} {base : Addr} (hw : WsReg s base) :
    WP isa (.block (Cfg.andFlag brainpoolp256r1)) s fun s' =>
      word s'.mem base FL = word s.mem base FL &&& s.gpr .a7 ∧ Rest [.t0] s s' ∧ Outside base FL 8 s.mem s'.mem := by
  rw [Cfg.andFlag, sl_FLAG]
  refine ld_ws hw (by decide) (by decide) fun s₁ u₁ => wp_and fun s₂ u₂ => ?_
  obtain r₂ : Rest [.t0] s s₂ := (u₁.rest (by decide)).trans (u₂.rest (by decide))
  refine sd_ws (hw.of_rest r₂) (by decide) (by decide) fun s₃ u₃ => WP.block_nil ⟨?_, r₂.trans (u₃.rest _), ?_⟩
  · rw [u₃.mem, word_writeW_self, u₂.gpr, u₁.gpr, u₁.other .a7 (by decide)]
  · rw [u₃.mem, u₂.mem, u₁.mem]; exact writeW_outside _ _ _ (by decide)

/-- The masks of `x < p` and `y < p` into the flag. -/
theorem masks_ok {s : State} {base : Addr} (hw : WsReg s base) :
    WP isa (.block (ltMask 4 (brainpoolp256r1.sl CX) (brainpoolp256r1.sl MP) ++ Cfg.andFlag brainpoolp256r1 ++ ltMask 4 (brainpoolp256r1.sl CY) (brainpoolp256r1.sl MP) ++
      Cfg.andFlag brainpoolp256r1)) s fun s' =>
      Kp s s' ∧ Outside base FL 8 s.mem s'.mem ∧
      word s'.mem base FL = word s.mem base FL &&& maskOf (decide (sv base s CX < sv base s MP)) &&&
        maskOf (decide (sv base s CY < sv base s MP)) := by
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (ltMask_ok hw (n := 4) (a := brainpoolp256r1.sl CX) (m := brainpoolp256r1.sl MP) (by decide)
    (by decide) (by decide) (by decide)) fun s₁ ⟨r₁, m₁, g₁⟩ => ?_)
  obtain hw₁ := hw.of_rest r₁
  refine WP.block_append (WP.mono (andFlag_ok hw₁) fun s₂ ⟨f₂, r₂, O₂⟩ => ?_)
  obtain hw₂ := hw₁.of_rest r₂
  refine WP.block_append (WP.mono (ltMask_ok hw₂ (n := 4) (a := brainpoolp256r1.sl CY) (m := brainpoolp256r1.sl MP) (by decide)
    (by decide) (by decide) (by decide)) fun s₃ ⟨r₃, m₃, g₃⟩ => ?_)
  obtain hw₃ := hw₂.of_rest r₃
  refine WP.mono (andFlag_ok hw₃) fun s₄ ⟨f₄, r₄, O₄⟩ => ⟨?_, ?_, ?_⟩
  · exact (Kp.of_rest r₁).trans ((Kp.of_rest r₂).trans ((Kp.of_rest r₃).trans (Kp.of_rest r₄)))
  · rw [← m₁]; exact O₂.trans (by rw [← m₃]; exact O₄)
  · have e : ∀ i, i < 44 → sv base s₂ i = sv base s i := fun i hi => by
      show wordsVal s₂.mem _ _ _ = _
      rw [O₂.wordsVal (by rw [sl_eq, FL]; omega_using [hi]) (by rw [sl_eq]; omega_using [hi]), m₁]
    rw [f₄, m₃, g₃, f₂, m₁, g₁]
    simp only [sv] at e ⊢
    rw [show wordsVal s₂.mem base (brainpoolp256r1.sl CY) 4 = _ from e CY (by decide),
      show wordsVal s₂.mem base (brainpoolp256r1.sl MP) 4 = _ from e MP (by decide)]

/-- The slots of the curve's equation. -/
abbrev curveSlots : List Nat :=
  [brainpoolp256r1.sl AP, brainpoolp256r1.sl BP, brainpoolp256r1.sl CXM, brainpoolp256r1.sl CYM, brainpoolp256r1.sl W0, brainpoolp256r1.sl W1, brainpoolp256r1.sl W2, brainpoolp256r1.sl CPX]

theorem curveLay : Lay brainpoolp256r1.MP' (own 4) (· ∈ curveSlots) :=
  ⟨by decide, fun x y hx hy => (by decide : ∀ x ∈ curveSlots, ∀ y ∈ curveSlots,
      x ≠ y → x + 8 * brainpoolp256r1.MP'.n ≤ y ∨ y + 8 * brainpoolp256r1.MP'.n ≤ x) x hx y hy, by decide, by decide⟩

theorem curveShort : Short (· ∈ curveSlots) := by decide

theorem curve_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps (Cfg.curveOps brainpoolp256r1) e (brainpoolp256r1.sl W1) =
      e (brainpoolp256r1.sl CYM) * e (brainpoolp256r1.sl CYM) - ((e (brainpoolp256r1.sl CXM) * e (brainpoolp256r1.sl CXM) * e (brainpoolp256r1.sl CXM) +
        e (brainpoolp256r1.sl AP) * e (brainpoolp256r1.sl CXM)) + e (brainpoolp256r1.sl BP)) := by
  simp only [Cfg.curveOps, runOps_cons, runOps_nil, FOp.run, Function.update_apply, sl_eq]
  simp only [W0, W1, W2, CYM, CXM, AP, BP, CPX, Nat.reduceMul, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]

/-- `y² - (x³ + a x + b)` to `W1`. -/
theorem curve_ok {s : State} {base : Addr} (hw : WsReg s base)
    (hlt : ∀ x ∈ [CXM, CYM, AP, BP], sv base s x < W.p) :
    WP isa (fprog brainpoolp256r1Field (Cfg.curveOps brainpoolp256r1)) s fun s' =>
      KeepR 4 base ((Cfg.curveOps brainpoolp256r1).map FOp.out) s s' ∧
      sv base s' W1 < W.p ∧
      toM W.p (2 ^ 256) (sv base s' W1) =
        toM W.p (2 ^ 256) (sv base s CYM) * toM W.p (2 ^ 256) (sv base s CYM) -
          ((toM W.p (2 ^ 256) (sv base s CXM) * toM W.p (2 ^ 256) (sv base s CXM) *
            toM W.p (2 ^ 256) (sv base s CXM) + toM W.p (2 ^ 256) (sv base s AP) *
            toM W.p (2 ^ 256) (sv base s CXM)) + toM W.p (2 ^ 256) (sv base s BP)) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt
  refine WP.mono (fprog_ok (M := brainpoolp256r1.MP') (F := brainpoolp256r1Field) field_ok rfl curveLay curveShort unit
    (Cfg.curveOps brainpoolp256r1) (V := [brainpoolp256r1.sl CXM, brainpoolp256r1.sl CYM, brainpoolp256r1.sl AP, brainpoolp256r1.sl BP])
    (E := fun x => toM W.p (2 ^ 256) (wordsVal s.mem base x 4)) ⟨hw, by decide, fun x hx => ?_, fun _ _ => rfl⟩
    (by decide) (by decide)) fun s' ⟨K, I⟩ => ⟨K, I.lt _ (by decide), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hlt.1
    · exact hlt.2.1
    · exact hlt.2.2.1
    · exact hlt.2.2.2
  · have v := I.val (brainpoolp256r1.sl W1) (by decide)
    exact v.trans (curve_run (F := Fe W) _)

/-! ## The whole check -/

/-- A slot apart from what changed. -/
theorem sv_unch {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (U : Unch base W m m') (i : Nat)
    (h : ∀ w ∈ W, brainpoolp256r1.sl i + 32 ≤ w.1 ∨ w.1 + w.2 ≤ brainpoolp256r1.sl i) (hi : i < 100 := by decide) :
    wordsVal m' base (brainpoolp256r1.sl i) 4 = wordsVal m base (brainpoolp256r1.sl i) 4 :=
  U.wordsVal h (by rw [sl_eq]; omega_using [hi])

/-- The flag, apart from what changed. -/
theorem fl_unch {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (U : Unch base W m m')
    (h : ∀ w ∈ W, FL + 8 ≤ w.1 ∨ w.1 + w.2 ≤ FL) : word m' base FL = word m base FL :=
  U.word h (by decide)

theorem maskOf_and (a b : Bool) : maskOf a &&& maskOf b = maskOf (a && b) := by
  cases a <;> cases b <;> decide

/-- `toM` is injective on numbers below `m`. -/
theorem toM_inj {m R : Nat} [NeZero m] (hR : UnitMod m R) {x y : Nat} (hx : x < m) (hy : y < m)
    (h : toM m R x = toM m R y) : x = y := by
  obtain e := congrArg (· * Fin.ofNat m R) h
  simp only [toM] at e
  rw [Lean.Grind.Semiring.mul_assoc, Lean.Grind.Semiring.mul_assoc, Lean.Grind.CommSemiring.mul_comm (rinv m R),
    mul_rinv hR, Lean.Grind.Semiring.mul_one, Lean.Grind.Semiring.mul_one] at e
  have := (ofNat_eq_ofNat (m := m)).mp e
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

/-- A Montgomery multiplication by `R² mod p` gives `x R mod p`. -/
theorem mont_eq {r x : Nat} (hr : r < W.p) (h : r * 2 ^ 256 % W.p = x * (2 ^ 256 * 2 ^ 256 % W.p) % W.p) :
    r = x * 2 ^ 256 % W.p :=
  toM_inj unit hr (Nat.mod_lt _ (by decide)) ((toM_r2 unit h).trans (toM_mont unit).symm)

/-- brainpoolP256r1's check of `Proof/Weierstrass/CheckPointContract.lean`. -/
abbrev CC : Impl.Weierstrass.CheckPoint.Curve := Impl.Weierstrass.CheckPoint.brainpoolp256r1

/-- `vg_brainpoolp256r1_check_point(ws = a0)`. -/
def checkRVc : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .a0, 8192⟩] ∧ (s.gpr .a0).toNat + 8192 ≤ 2 ^ 64 ∧
    (s.gpr .a0).toNat % 8 = 0 ∧ CC.pre (s.gpr .a0) s.mem
  post s s' := CC.post (s.gpr .a0) s.mem s'.mem
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0

theorem num_eq (m : Mem) (ws : Addr) (i : Nat) (hi : i < 100 := by decide) :
    CC.num ws m (CC.slot i) = wordsVal m ws (brainpoolp256r1.sl i) 4 := by
  unfold Impl.Weierstrass.CheckPoint.Curve.num
  rw [Impl.Weierstrass.Mont.numAt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
    simp only [Impl.Weierstrass.CheckPoint.Curve.slot, CC, Impl.Weierstrass.CheckPoint.brainpoolp256r1]; omega_using [hi])]
  exact read_eq_wordsVal m ws 4 _

theorem flag_eq (m : Mem) (ws : Addr) : CC.flag ws m = word m ws FL := by
  unfold Impl.Weierstrass.CheckPoint.Curve.flag
  simp only [word, off, Mem.readW]
  rfl

/-- The writes of the check: its own working space or its results. -/
abbrev chkW : List (Nat × Nat) :=
  ((([(128, 8), (136, 8)] ++ [(FL, 8)]) ++ [(brainpoolp256r1.sl CXM, 32), (own 4, 256)]) ++ [(brainpoolp256r1.sl CYM, 32), (own 4, 256)]) ++
    (((Cfg.curveOps brainpoolp256r1).map FOp.out).map (fun w => (w, 8 * 4)) ++ [(own 4, 64 * 4)]) ++
    [(FL, 8), (brainpoolp256r1.sl CPX, 32), (brainpoolp256r1.sl CPY, 32)]

theorem keeps_of_unch {ws : Addr} {m m' : Mem} (hu : Unch ws chkW m m') : CC.Keeps ws m m' := by
  intro i hi hown hout
  have h8 : Impl.Weierstrass.Mont.wsBytes = 8192 := rfl
  refine hu _ fun w hw => ?_
  rw [show ws + BitVec.ofNat 64 i = off ws i from rfl, ofs_off0 ws (by omega_using [hi, h8])]
  obtain hw' := (by decide : ∀ w ∈ chkW, (128 ≤ w.1 ∧ w.1 + w.2 ≤ 160) ∨ (w.1 = FL ∧ w.2 = 8) ∨
    (∃ j ∈ [34, 35, 37, 38, 41, 42, 43], w.1 = 64 + 32 * j ∧ w.2 = 32) ∨ (3840 ≤ w.1 ∧ w.1 + w.2 ≤ 4096)) w hw
  simp only [FL, Impl.Weierstrass.CheckPoint.Curve.Own, Impl.Weierstrass.CheckPoint.Curve.Out,
    Impl.Weierstrass.CheckPoint.Curve.slot, Impl.Weierstrass.CheckPoint.Curve.flagAt, CC,
    Impl.Weierstrass.CheckPoint.brainpoolp256r1, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes,
    List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, not_or] at hown hout hw'
  omega_using [hown, hout, hw']

/-- The validity the masks compute. -/
theorem masks_valid {x y w1 xm ym : Nat} (hw1 : w1 < W.p)
    (hxm : xm = x * 2 ^ 256 % W.p) (hym : ym = y * 2 ^ 256 % W.p)
    (hv : toM W.p (2 ^ 256) w1 = toM W.p (2 ^ 256) ym * toM W.p (2 ^ 256) ym -
      ((toM W.p (2 ^ 256) xm * toM W.p (2 ^ 256) xm * toM W.p (2 ^ 256) xm +
        Fin.ofNat W.p W.a * toM W.p (2 ^ 256) xm) + Fin.ofNat W.p W.b)) :
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
      obtain ex : (Fin.ofNat W.p x : Fe W) = ⟨x, hx⟩ := VG.Proof.EcKey.fe_eq hx rfl
      obtain ey : (Fin.ofNat W.p y : Fe W) = ⟨y, hy⟩ := VG.Proof.EcKey.fe_eq hy rfl
      obtain hc : Spec.Weierstrass.onCurve W (.affine (Fin.ofNat W.p x) (Fin.ofNat W.p y)) = true ↔ w1 = 0 := by
        rw [ex, ey, VG.Proof.Ecdh.onCurve_iff hx hy, ← e]
      by_cases h0 : w1 = 0 <;> simp [hx, hy, h0, hc, maskOf]
    · simp [hy, maskOf]
  · simp [hx, maskOf]

/-- `vg_brainpoolp256r1_check_point` meets `checkRVc`. -/
theorem check_rv (s : State) (hs : checkRVc.pre s) :
    ∃ t s', Exec isa checkBrainpoolP256r1 s t s' ∧ abiPreserved s s' ∧ checkRVc.post s s' := by
  obtain ⟨-, hwr, hfit, hal, ⟨hp, hr2, ha, hb, hf⟩⟩ := hs
  generalize hb0 : s.gpr .a0 = base at hwr hfit hal hp hr2 ha hb hf
  obtain hwr' : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_singleton_self _
  suffices h : WP isa checkBrainpoolP256r1 s fun s' => abiPreserved s s' ∧ checkRVc.post s s' by
    obtain ⟨t, s', he, h⟩ := h; exact ⟨t, s', he, h⟩
  rw [checkBrainpoolP256r1, Cfg.checkFn, show Cfg.checkSave brainpoolp256r1 = 128 from rfl]
  refine WP.seq (sd_a0 hb0 hwr' hal (d := 128) (by decide) (by decide) fun s₁ u₁ => ?_)
  refine sd_a0 (by rw [u₁.gpr]; exact hb0) (by rw [u₁.wr]; exact hwr') hal (d := 136) (by decide) (by decide)
    fun s₂ u₂ => wp_mv fun s₃ u₃ => WP.block_nil ?_
  obtain g₃ : ∀ r, r ≠ .s0 → s₃.gpr r = s.gpr r := fun r hr => by rw [u₃.other r hr, u₂.gpr, u₁.gpr]
  obtain hw₃ : WsReg s₃ base := ⟨by rw [u₃.gpr, u₂.gpr, u₁.gpr, hb0], by rw [u₃.wr, u₂.wr, u₁.wr]; exact hwr',
    hfit, hal⟩
  obtain m₃ : s₃.mem = (s.mem.writeW (off base 128) (s.gpr .s0)).writeW (off base 136) (s.gpr .ra) := by
    simp only [u₃.mem, u₂.mem, u₁.mem, u₁.gpr]
  obtain U₃ : Unch base [(128, 8), (136, 8)] s.mem s₃.mem := by
    rw [m₃]; exact (writeW_outside _ _ _ (by decide)).unch.trans (writeW_outside _ _ _ (by decide)).unch
  -- The masks.
  refine WP.seq (WP.mono (masks_ok hw₃) fun s₄ ⟨K₄, O₄, f₄⟩ => ?_)
  obtain hw₄ := hw₃.of_kp K₄
  obtain U₄ := U₃.trans O₄.unch
  -- `x R` and `y R`.
  obtain hr2' : sv base s₄ R2P = 2 ^ 256 * 2 ^ 256 % W.p := by
    rw [show sv base s₄ R2P = sv base s R2P from sv_unch U₄ R2P (by decide)]
    exact (num_eq s.mem base R2P).symm.trans hr2
  refine WP.seq (WP.mono (mulCall_ok field_ok hw₄ (o := brainpoolp256r1.sl CXM) (a := brainpoolp256r1.sl CX) (b := brainpoolp256r1.sl R2P)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by show sv base s₄ R2P < W.p; rw [hr2']; exact Nat.mod_lt _ (by decide)))
    fun s₅ ⟨C₅, lt₅, e₅⟩ => ?_)
  obtain hw₅ := hw₄.of_kp C₅.kp
  have U₅ : Unch base [(brainpoolp256r1.sl CXM, 32), (own 4, 256)] s₄.mem s₅.mem := C₅.mem
  refine WP.seq (WP.mono (mulCall_ok field_ok hw₅ (o := brainpoolp256r1.sl CYM) (a := brainpoolp256r1.sl CY) (b := brainpoolp256r1.sl R2P)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by show sv base s₅ R2P < W.p; rw [show sv base s₅ R2P = sv base s₄ R2P from sv_unch U₅ R2P (by decide), hr2']; exact Nat.mod_lt _ (by decide)))
    fun s₆ ⟨C₆, lt₆, e₆⟩ => ?_)
  obtain hw₆ := hw₅.of_kp C₆.kp
  have U₆ : Unch base [(brainpoolp256r1.sl CYM, 32), (own 4, 256)] s₅.mem s₆.mem := C₆.mem
  -- The values so far, from the contract's.
  obtain x₄ : sv base s₄ CX = CC.num base s.mem CC.xAt := by
    rw [show sv base s₄ CX = sv base s CX from sv_unch U₄ CX (by decide)]; exact (num_eq s.mem base CX).symm
  obtain y₅ : sv base s₅ CY = CC.num base s.mem CC.yAt := by
    rw [show sv base s₅ CY = sv base s CY from sv_unch (U₄.trans U₅) CY (by decide)]; exact (num_eq s.mem base CY).symm
  obtain xm₆ : sv base s₆ CXM = CC.num base s.mem CC.xAt * 2 ^ 256 % W.p := by
    rw [show sv base s₆ CXM = sv base s₅ CXM from sv_unch U₆ CXM (by decide), ← x₄]
    refine mont_eq lt₅ (e₅.trans ?_)
    show sv base s₄ CX * sv base s₄ R2P % W.p = _
    rw [hr2']
  obtain ym₆ : sv base s₆ CYM = CC.num base s.mem CC.yAt * 2 ^ 256 % W.p := by
    rw [← y₅]
    refine mont_eq lt₆ (e₆.trans ?_)
    show sv base s₅ CY * sv base s₅ R2P % W.p = _
    rw [show sv base s₅ R2P = sv base s₄ R2P from sv_unch U₅ R2P (by decide), hr2']
  obtain ap₆ : sv base s₆ AP = W.a * 2 ^ 256 % W.p := by
    rw [show sv base s₆ AP = sv base s AP from sv_unch ((U₄.trans U₅).trans U₆) AP (by decide)]
    exact (num_eq s.mem base AP).symm.trans ha
  obtain bp₆ : sv base s₆ BP = W.b * 2 ^ 256 % W.p := by
    rw [show sv base s₆ BP = sv base s BP from sv_unch ((U₄.trans U₅).trans U₆) BP (by decide)]
    exact (num_eq s.mem base BP).symm.trans hb
  obtain hp0 : 0 < W.p := by decide
  -- The curve's equation.
  refine WP.seq (WP.mono (curve_ok hw₆ (fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rw [xm₆]; exact Nat.mod_lt _ hp0
    · rw [ym₆]; exact Nat.mod_lt _ hp0
    · rw [ap₆]; exact Nat.mod_lt _ hp0
    · rw [bp₆]; exact Nat.mod_lt _ hp0)) fun s₇ ⟨K₇, lt₇, v₇⟩ => ?_)
  obtain hw₇ := hw₆.of_kp K₇.kp
  have U₇ : Unch base (((Cfg.curveOps brainpoolp256r1).map FOp.out).map (fun w => (w, 8 * 4)) ++ [(own 4, 64 * 4)])
      s₆.mem s₇.mem := K₇.mem
  -- The mask of the equation, and the flag.
  rw [show brainpoolp256r1.n = 4 from rfl]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (zeroMask_ok hw₇ (n := 4) (a := brainpoolp256r1.sl W1) (by decide) (by decide))
    fun s₈ ⟨r₈, m₈, g₈⟩ => ?_)
  obtain hw₈ := hw₇.of_rest r₈
  refine WP.block_append (WP.mono (andFlag_ok hw₈) fun s₉ ⟨f₉, r₉, O₉⟩ => ?_)
  obtain hw₉ := hw₈.of_rest r₉
  refine ldAt_ws hw₉ (d := brainpoolp256r1.sl FLAG) (by decide) (by decide) fun s₁₀ u₁₀ => ?_
  obtain hw₁₀ := hw₉.of_kp (Kp.of_upd u₁₀)
  -- The flag's value.
  obtain U₃₇ := ((U₄.trans U₅).trans U₆).trans U₇
  obtain fl₇ : word s₇.mem base FL = word s₄.mem base FL :=
    fl_unch ((U₅.trans U₆).trans U₇) (by decide)
  obtain fl₃ : word s₃.mem base FL = word s.mem base FL := fl_unch U₃ (by decide)
  obtain e₃ : ∀ i, i < 44 → i ≠ 2 → sv base s₃ i = sv base s i := fun i hi h2 => by
    show wordsVal _ _ _ _ = _
    rw [U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> (simp only; rw [sl_eq]; omega_using [h2])) (by rw [sl_eq]; omega_using [hi])]
  obtain hpw : sv base s MP = W.p := (num_eq s.mem base MP).symm.trans hp
  rw [e₃ CX (by decide) (by decide), e₃ CY (by decide) (by decide), e₃ MP (by decide) (by decide), hpw,
    fl₃] at f₄
  obtain hxv : sv base s CX = CC.num base s.mem CC.xAt := (num_eq s.mem base CX).symm
  obtain hyv : sv base s CY = CC.num base s.mem CC.yAt := (num_eq s.mem base CY).symm
  rw [hxv, hyv] at f₄
  obtain hv := masks_valid lt₇ xm₆ ym₆ (by rw [v₇, ap₆, bp₆, toM_mont unit, toM_mont unit])
  generalize hx : CC.num base s.mem CC.xAt = x at *
  generalize hy : CC.num base s.mem CC.yAt = y at *
  obtain hF : word s₉.mem base FL = CC.flag base s.mem &&& Impl.Weierstrass.CheckPoint.Curve.mask (CC.Valid x y) := by
    rw [f₉, m₈, g₈, fl₇, f₄, flag_eq, ← hv]; simp only [BitVec.and_assoc]
  generalize hFv : CC.flag base s.mem &&& Impl.Weierstrass.CheckPoint.Curve.mask (CC.Valid x y) = F at hF
  obtain hFm : F = if decide (F ≠ 0) then BitVec.allOnes 64 else 0 := by
    rw [← hFv]
    unfold Impl.Weierstrass.CheckPoint.Curve.mask
    rcases hf with h | h <;> rw [h] <;> split <;> decide
  obtain a₁₀ : s₁₀.gpr .a7 = if decide (F ≠ 0) then BitVec.allOnes 64 else 0 := by
    rw [u₁₀.gpr]; exact hF.trans hFm
  -- The point.
  refine WP.block_append (WP.mono (sel_ok (decide (F ≠ 0)) 4 hw₁₀ a₁₀ (o := brainpoolp256r1.sl CPX) (a := brainpoolp256r1.sl GX)
    (b := brainpoolp256r1.sl CXM) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun s₁₁ ⟨e₁₁, r₁₁, O₁₁⟩ => ?_)
  obtain hw₁₁ := hw₁₀.of_rest r₁₁
  obtain a₁₁ : s₁₁.gpr .a7 = if decide (F ≠ 0) then BitVec.allOnes 64 else 0 := by
    rw [r₁₁.gpr _ (by decide), a₁₀]
  refine WP.block_append (WP.mono (sel_ok (decide (F ≠ 0)) 4 hw₁₁ a₁₁ (o := brainpoolp256r1.sl CPY) (a := brainpoolp256r1.sl GY)
    (b := brainpoolp256r1.sl CYM) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun s₁₂ ⟨e₁₂, r₁₂, O₁₂⟩ => ?_)
  obtain hw₁₂ := hw₁₁.of_rest r₁₂
  -- What changed.
  obtain U₉ : Unch base [(FL, 8)] s₇.mem s₉.mem := by rw [← m₈]; exact O₉.unch
  have m₁₀ : s₁₀.mem = s₉.mem := u₁₀.mem
  obtain Uend : Unch base [(FL, 8), (brainpoolp256r1.sl CPX, 32), (brainpoolp256r1.sl CPY, 32)] s₇.mem s₁₂.mem := by
    have := (U₉.trans (by rw [← m₁₀]; exact O₁₁.unch)).trans O₁₂.unch
    exact this
  obtain U₆₁₂ := U₇.trans Uend
  obtain Uall : Unch base chkW s.mem s₁₂.mem := U₃₇.trans Uend
  -- The loads.
  obtain far : ∀ d ∈ [128, 136], word s₁₂.mem base d = word s₃.mem base d := fun d hd => by
    obtain U := ((((O₄.unch.trans U₅).trans U₆).trans U₇).trans Uend)
    refine U.word (fun w hw => ?_) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; omega_using [hd])
    have := (by decide : ∀ w ∈ (((([(FL, 8)] ++ [(brainpoolp256r1.sl CXM, 32), (own 4, 256)]) ++
        [(brainpoolp256r1.sl CYM, 32), (own 4, 256)]) ++
        (((Cfg.curveOps brainpoolp256r1).map FOp.out).map (fun w => (w, 8 * 4)) ++ [(own 4, 64 * 4)])) ++
        [(FL, 8), (brainpoolp256r1.sl CPX, 32), (brainpoolp256r1.sl CPY, 32)]), 144 ≤ w.1) w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    omega_using [this, hd]
  obtain w36 : word s₁₂.mem base 136 = s.gpr .ra := by rw [far 136 (by simp), m₃, word_writeW_self]
  obtain w28 : word s₁₂.mem base 128 = s.gpr .s0 := by
    rw [far 128 (by simp), m₃, (writeW_outside (d := 136) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []),
      word_writeW_self]
  obtain Kp₁₂ : Kp s₃ s₁₂ := K₄.trans (C₅.kp.trans (C₆.kp.trans (K₇.kp.trans ((Kp.of_rest r₈).trans
    ((Kp.of_rest r₉).trans ((Kp.of_upd u₁₀).trans ((Kp.of_rest r₁₁).trans (Kp.of_rest r₁₂))))))))
  refine ld_ws hw₁₂ (d := 136) (by decide) (by decide) fun s₁₃ u₁₃ => ?_
  obtain hw₁₃ := hw₁₂.of_kp (Kp.of_upd u₁₃)
  refine ld_ws hw₁₃ (d := 128) (by decide) (by decide) fun s₁₄ u₁₄ => WP.block_nil ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · by_cases h0 : r = .s0
    · subst h0; rw [u₁₄.gpr, u₁₃.mem, w28]
    rw [u₁₄.other _ h0, u₁₃.other _ (fun e => by subst e; revert hr; decide), Kp₁₂.gpr r hr, g₃ r h0]
  · rw [u₁₄.sp, u₁₃.sp, Kp₁₂.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₁₄.other _ (by decide), u₁₃.gpr, w36]
  · have m₁₄ : s₁₄.mem = s₁₂.mem := by rw [u₁₄.mem, u₁₃.mem]
    show CC.post (s.gpr .a0) s.mem s₁₄.mem
    rw [hb0, m₁₄]
    obtain xm : sv base s₁₂ CXM = x * 2 ^ 256 % W.p := by
      rw [show sv base s₁₂ CXM = sv base s₆ CXM from sv_unch U₆₁₂ CXM (by decide), xm₆]
    obtain ym : sv base s₁₂ CYM = y * 2 ^ 256 % W.p := by
      rw [show sv base s₁₂ CYM = sv base s₆ CYM from sv_unch U₆₁₂ CYM (by decide), ym₆]
    refine ⟨?_, ?_, ?_, ?_, ?_, keeps_of_unch Uall⟩
    · have U' : Unch base ([(brainpoolp256r1.sl CPX, 8 * 4)] ++ [(brainpoolp256r1.sl CPY, 8 * 4)]) s₉.mem s₁₂.mem := by
        rw [← m₁₀]; exact O₁₁.unch.trans O₁₂.unch
      rw [flag_eq, fl_unch U' (by decide), hF, hx, hy, hFv]
    · rw [hx]
      refine (num_eq _ _ CXM).trans (xm.trans ?_)
      rfl
    · rw [hy]
      refine (num_eq _ _ CYM).trans (ym.trans ?_)
      rfl
    · have U' : Unch base ([(brainpoolp256r1.sl CPX, 8 * 4)] ++ [(brainpoolp256r1.sl CPY, 8 * 4)]) s₁₀.mem s₁₂.mem :=
        O₁₁.unch.trans O₁₂.unch
      obtain U'' := U₃₇.trans U₉
      rw [← m₁₀] at U''
      obtain h1 : sv base s₁₂ CPX = sv base s₁₁ CPX := sv_unch O₁₂.unch CPX (by decide)
      obtain h2 : sv base s₁₀ CXM = sv base s₁₂ CXM := (sv_unch U' CXM (by decide)).symm
      obtain h3 : sv base s₁₀ GX = sv base s GX := sv_unch U'' GX (by decide)
      rw [hx, hy, hFv, show CC.pxAt = CC.slot CPX from rfl, show CC.gxAt = CC.slot GX from rfl, num_eq _ _ CPX,
        num_eq _ _ GX]
      show sv base s₁₂ CPX = if F = 0 then sv base s GX else _
      rw [h1]; show wordsVal s₁₁.mem _ _ _ = _; rw [e₁₁]
      show (if decide (F ≠ 0) = true then sv base s₁₀ CXM else sv base s₁₀ GX) = _
      rw [h2, h3, xm]
      by_cases h : F = 0 <;> simp [h] <;> rfl
    · have O' := O₁₁
      rw [m₁₀] at O'
      obtain U'' := (U₃₇.trans U₉).trans O'.unch
      obtain h2 : sv base s₁₁ CYM = sv base s₁₂ CYM := (sv_unch O₁₂.unch CYM (by decide)).symm
      obtain h3 : sv base s₁₁ GY = sv base s GY := sv_unch U'' GY (by decide)
      rw [hx, hy, hFv, show CC.pyAt = CC.slot CPY from rfl, show CC.gyAt = CC.slot GY from rfl, num_eq _ _ CPY,
        num_eq _ _ GY]
      show wordsVal s₁₂.mem _ _ _ = if F = 0 then sv base s GY else _
      rw [e₁₂]
      show (if decide (F ≠ 0) = true then sv base s₁₁ CYM else sv base s₁₁ GY) = _
      rw [h2, h3, ym]
      by_cases h : F = 0 <;> simp [h] <;> rfl

end VG.Proof.Ecdh.RISCV64.BrainpoolP256r1

end

end

/-!
# ECDH and public keys over brainpoolp256r1 on RISC-V: the multiplication and after

What follows the point's setup in both functions (`tail`): the masks of `d`
in `[1, n-1]` into the flag (`range_ok`), `R = [d]P` by a call of
`vg_brainpoolp256r1_mul` (`mul_rv`), `Z^(p-2)` by its chain (`chainPow_ok`), and `x = X Z^(p-2)`
out of Montgomery's form (`affine_ok`). The callees' `Keeps` are frames
(`unch_of_mulKeeps`).
-/

@[expose] public section

/-!
## ECDH and public keys over brainpoolp256r1 on RISC-V: the setup

The constants (`consts_ok`: `setConst` for each, apart), and what both
functions' setups share.
-/

namespace VG.Proof.Ecdh.RISCV64.BrainpoolP256r1

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.BrainpoolP256r1
open VG.Proof.X25519.RISCV64 (Rest)

/-- Constants to slots below 44, each its own. -/
theorem consts_ok : ∀ (L : List (Nat × Nat)) {s : State} {base : Addr}, WsReg s base → (∀ e ∈ L, e.1 < 44) →
    (L.map Prod.fst).Nodup →
    WP isa (.block (L.flatMap fun e => setConst 4 (brainpoolp256r1.sl e.1) e.2)) s fun s' =>
      Rest [.t0, .t1] s s' ∧ Unch base (L.map fun e => (brainpoolp256r1.sl e.1, 32)) s.mem s'.mem ∧
      ∀ e ∈ L, sv base s' e.1 = e.2 % 2 ^ 256
  | [], s, _, _, _, _ => WP.block_nil ⟨Rest.refl _ _, Unch.refl _ _ _, by simp⟩
  | (i, x) :: L, s, base, hw, hlt, hnd => by
    simp only [List.mem_cons, forall_eq_or_imp] at hlt
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rw [List.flatMap_cons]
    refine WP.block_append (WP.mono (setConst_ok 4 hw (o := brainpoolp256r1.sl i) (x := x) (by rw [sl_eq]; omega_using [])
      (by rw [sl_eq]; omega)) fun s₁ ⟨r₁, O₁, e₁⟩ => ?_)
    refine WP.mono (consts_ok L (hw.of_rest r₁) hlt.2 hnd.2) fun s₂ ⟨r₂, U₂, e₂⟩ => ⟨r₁.trans r₂, ?_, ?_⟩
    · exact O₁.unch.trans U₂
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · show wordsVal _ _ _ _ = _
        rw [U₂.wordsVal (fun w hw => by
          simp only [List.mem_map] at hw
          obtain ⟨e', he', rfl⟩ := hw
          obtain hne : e'.1 ≠ i := fun h => hnd.1 ⟨e', he', h⟩
          have := hlt.2 e' he'
          simp only [sl_eq]; omega_using [hne]) (by rw [sl_eq]; omega)]
        exact e₁
      · exact e₂ e he

/-- The constants, as `consts_ok` takes them. -/
theorem constCode_eq : constCode brainpoolp256r1 = (consts brainpoolp256r1).flatMap fun e => setConst 4 (brainpoolp256r1.sl e.1) e.2 := rfl

/-- The constants' slots. -/
theorem consts_slots : ∀ e ∈ consts brainpoolp256r1, e.1 < 44 := by decide

theorem consts_nodup : ((consts brainpoolp256r1).map Prod.fst).Nodup := by decide

/-- The constants are below `2²⁵⁶`. -/
theorem consts_lt : ∀ e ∈ consts brainpoolp256r1, e.2 < 2 ^ 256 := by decide

/-- `sd t, d(r)` at the working space's base, in `r`. -/
theorem sd_reg {s : State} {base : Addr} {is : List Instr} {Q : State → Prop} {r : Reg} (h0 : s.gpr r = base)
    (hwr : (⟨base, 8192⟩ : Region) ∈ s.wr) (hal : base.toNat % 8 = 0)
    {t : Reg} {d : Nat} (hd : d + 8 ≤ 2048) (hd8 : d % 8 = 0)
    (k : ∀ s', Mupd s s' (s.mem.writeW (off base d) (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t r d :: is)) s Q :=
  wp_sd (by omega_using [hd]) (by rw [h0]) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hal, hd8])
    ⟨_, hwr, Offset.contains_base base (by omega_using [hd]) (by omega_using [hd])⟩ k

/-- The saves, `s0 = s3 = r` and `s2 = a0`. -/
theorem save_ok {s : State} {r : Reg} {base : Addr} (h0 : s.gpr r = base)
    (hwr : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64) (hal : base.toNat % 8 = 0) :
    WP isa (.block (saveCode r)) s fun s' => WsReg s' base ∧ s'.gpr .s3 = base ∧ s'.gpr .s2 = s.gpr .a0 ∧
      (∀ x, x ≠ .s0 → x ≠ .s2 → x ≠ .s3 → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ Unch base [(0, 40)] s.mem s'.mem ∧
      word s'.mem base 0 = s.gpr .s0 ∧ word s'.mem base 8 = s.gpr .s1 ∧ word s'.mem base 16 = s.gpr .s2 ∧
      word s'.mem base 24 = s.gpr .ra ∧ word s'.mem base 32 = s.gpr .s3 := by
  rw [saveCode]
  refine sd_reg h0 hwr hal (d := 0) (by decide) (by decide) fun s₁ u₁ => ?_
  refine sd_reg (by rw [u₁.gpr]; exact h0) (by rw [u₁.wr]; exact hwr) hal (d := 8) (by decide) (by decide)
    fun s₂ u₂ => ?_
  refine sd_reg (by rw [u₂.gpr, u₁.gpr]; exact h0) (by rw [u₂.wr, u₁.wr]; exact hwr) hal (d := 16) (by decide)
    (by decide) fun s₃ u₃ => ?_
  refine sd_reg (by rw [u₃.gpr, u₂.gpr, u₁.gpr]; exact h0) (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hwr) hal (d := 24)
    (by decide) (by decide) fun s₄ u₄ => ?_
  refine sd_reg (by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]; exact h0) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hwr)
    hal (d := 32) (by decide) (by decide) fun s₅ u₅ =>
    wp_mv fun s₆ u₆ => wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ => WP.block_nil ?_
  obtain g₅ : ∀ x, s₅.gpr x = s.gpr x := fun x => by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  obtain m₅ : s₅.mem = ((((s.mem.writeW (off base 0) (s.gpr .s0)).writeW (off base 8) (s.gpr .s1)).writeW
      (off base 16) (s.gpr .s2)).writeW (off base 24) (s.gpr .ra)).writeW (off base 32) (s.gpr .s3) := by
    simp only [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  obtain m₈ : s₈.mem = s₅.mem := by rw [u₈.mem, u₇.mem, u₆.mem]
  obtain O : ∀ {d} {m : Mem} {v : BitVec 64}, d ≤ 32 → Outside base d 8 m (m.writeW (off base d) v) :=
    fun h => writeW_outside _ _ _ (by omega_using [h])
  obtain hw₈ : WsReg s₈ base := by
    refine ⟨by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅, h0], ?_, hn, hal⟩
    rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hwr
  obtain w0 : ∀ {d e} {m : Mem} {v : BitVec 64}, d ≤ 32 → e ≤ 32 → d + 8 ≤ e ∨ e + 8 ≤ d →
      word (m.writeW (off base e) v) base d = word m base d :=
    fun hd he h => (O he).word h (by omega_using [hd])
  obtain e₆ : s₆.gpr r = s₅.gpr r := by
    by_cases h : r = .s0
    · subst h; exact u₆.gpr
    · exact u₆.other _ h
  refine ⟨hw₈, by rw [u₈.other _ (by decide), u₇.gpr, e₆, g₅, h0],
    by rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g₅], fun x h1 h2 h3 => by
      rw [u₈.other _ h2, u₇.other _ h3, u₆.other _ h1, g₅],
    by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd],
    by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr],
    by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m₈, m₅]
    exact (((((O (by decide)).unch.trans (O (by decide)).unch).trans (O (by decide)).unch).trans
      (O (by decide)).unch).trans (O (by decide)).unch).cover (by decide)
  · rw [m₈, m₅, w0 (by decide) (by decide) (by decide), w0 (by decide) (by decide) (by decide),
      w0 (by decide) (by decide) (by decide), w0 (by decide) (by decide) (by decide), word_writeW_self]
  · rw [m₈, m₅, w0 (by decide) (by decide) (by decide), w0 (by decide) (by decide) (by decide),
      w0 (by decide) (by decide) (by decide), word_writeW_self]
  · rw [m₈, m₅, w0 (by decide) (by decide) (by decide), w0 (by decide) (by decide) (by decide), word_writeW_self]
  · rw [m₈, m₅, w0 (by decide) (by decide) (by decide), word_writeW_self]
  · rw [m₈, m₅, word_writeW_self]


end VG.Proof.Ecdh.RISCV64.BrainpoolP256r1

namespace VG.Proof.Ecdh.RISCV64.BrainpoolP256r1

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.BrainpoolP256r1
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point)
open VG.Spec.Ecdsa (bytesAt)
open VG.WriteBytes (writeBytes)

/-- What `vg_brainpoolp256r1_mul` may write, as ranges of offsets. -/
abbrev mulKW : List (Nat × Nat) := [(512, 96), (608, 448), (128, 32), (1344, 32), (1504, 2 ^ 64)]

theorem unch_of_mulKeeps {base : Addr} {m m' : Mem} (h : MC.Keeps base m m') : Unch base mulKW m m' := by
  intro x hx
  obtain e := fun w hw => hx w hw
  simp only [mulKW, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e
  obtain hb : ofs base x < 2 ^ 64 := (x - base).isLt
  obtain hlt : ofs base x < 1504 := by omega_using [e, hb]
  obtain ex : x = base + BitVec.ofNat 64 (ofs base x) := by
    simp only [ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rw [BitVec.add_comm, BitVec.sub_add_cancel]
  rw [ex]
  refine h _ (by show _ < 8192; omega_using [e, hb]) ?_ ?_
  · simp only [Impl.Weierstrass.Mul.Curve.Own, Impl.Weierstrass.Mul.Curve.slot, Impl.Weierstrass.Mul.Curve.tmpAt,
      Impl.Weierstrass.Mul.Curve.bitsAt, true_and]
    omega_using [e, hb]
  · simp only [Impl.Weierstrass.Mul.Curve.pAt, Impl.Weierstrass.Mul.Curve.ptBytes, Impl.Weierstrass.Mul.Curve.slot]
    omega_using [e]

/-- What `vg_brainpoolp256r1_check_point` may write, as ranges of offsets. -/
abbrev checkKW : List (Nat × Nat) :=
  [(128, 32), (1248, 32), (1376, 32), (1408, 32), (3840, 256), (1152, 32), (1184, 32), (1280, 32), (1440, 32),
    (FL, 8), (8192, 2 ^ 64)]

theorem unch_of_checkKeeps {base : Addr} {m m' : Mem} (h : CC.Keeps base m m') : Unch base checkKW m m' := by
  intro x hx
  obtain e := fun w hw => hx w hw
  simp only [checkKW, FL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e
  obtain hb : ofs base x < 2 ^ 64 := (x - base).isLt
  obtain hlt : ofs base x < 8192 := by omega_using [e, hb]
  obtain ex : x = base + BitVec.ofNat 64 (ofs base x) := by
    simp only [ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rw [BitVec.add_comm, BitVec.sub_add_cancel]
  rw [ex]
  refine h _ hlt ?_ ?_
  · simp only [Impl.Weierstrass.CheckPoint.Curve.Own, Impl.Weierstrass.CheckPoint.Curve.slot, CC,
      Impl.Weierstrass.CheckPoint.brainpoolp256r1, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes,
      List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, not_or]
    omega_using [e]
  · simp only [Impl.Weierstrass.CheckPoint.Curve.Out, Impl.Weierstrass.CheckPoint.Curve.slot,
      Impl.Weierstrass.CheckPoint.Curve.flagAt, CC, Impl.Weierstrass.CheckPoint.brainpoolp256r1,
      List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, not_or]
    omega_using [e]

theorem not_mask (b : Bool) : maskOf b ^^^ BitVec.ofInt 64 (-1) = maskOf (!b) := by cases b <;> decide

/-- A call on the working space, then `s0` from `s3`. -/
theorem wsCallR_ok {f : String} {body : Prog isa} (hn : body.noFrames = true) {K : Contract isa}
    (hK : Meets body K) {s : State} {base : Addr} (hw : WsReg s base) (h3 : s.gpr .s3 = base)
    (hpre : ∀ t : State, t.rd = [] → t.wr = [⟨base, 8192⟩] → t.gpr .a0 = base → t.mem = s.mem → K.pre t)
    {Q : State → Prop}
    (hQ : ∀ s' s'' : State, Kp s s'' → s''.mem = s'.mem → ∀ t : State, t.gpr .a0 = base → t.mem = s.mem →
      K.post t (s'.withRegions [] [⟨base, 8192⟩]) → Q s'') :
    WP isa (Cfg.wsCall f body) s Q := by
  rw [Cfg.wsCall]
  refine WP.seq (wsCall_ok hn hK hw hpre fun s' K' t a m hp => wp_mv fun s'' u => WP.block_nil ?_)
  refine hQ s' s'' ⟨fun r hr => ?_, by rw [u.rd, K'.rd], by rw [u.wr, K'.wr], by rw [u.sp, K'.sp]⟩ u.mem t a m hp
  by_cases h : r = .s0
  · subst h; rw [u.gpr, K'.gpr _ (by decide), h3, hw.s0]
  · rw [u.other _ h, K'.gpr _ hr]

/-- A slot below the flag's. -/
theorem sl_lt {i : Nat} (hi : i < 44) : brainpoolp256r1.sl i % 8 = 0 ∧ brainpoolp256r1.sl i + 8 * 4 ≤ 2048 ∧ brainpoolp256r1.sl i + 8 * 4 ≤ FL := by
  simp only [Cfg.sl, slot, show brainpoolp256r1.n = 4 from rfl, FL]; omega_using [hi]

/-- The masks of `x < n` and `x ≠ 0` into the flag, for `x` at slot `i`. -/
theorem rangeOf_ok {i : Nat} (hi : i < 44) {s : State} {base : Addr} (hw : WsReg s base) :
    WP isa (.block (rangeOf brainpoolp256r1 i)) s fun s' =>
      Kp s s' ∧ Outside base FL 8 s.mem s'.mem ∧
      word s'.mem base FL = word s.mem base FL &&& maskOf (decide (sv base s i < sv base s MN)) &&&
        maskOf (!decide (sv base s i = 0)) := by
  obtain ⟨a8, a2, aF⟩ := sl_lt hi
  rw [rangeOf, show brainpoolp256r1.n = 4 from rfl]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (ltMask_ok hw (n := 4) (a := brainpoolp256r1.sl i) (m := brainpoolp256r1.sl MN) a8
    (by decide) (by omega_using [a2]) (by decide)) fun s₁ ⟨r₁, m₁, g₁⟩ => ?_)
  obtain hw₁ := hw.of_rest r₁
  refine WP.block_append (WP.mono (andFlag_ok hw₁) fun s₂ ⟨f₂, r₂, O₂⟩ => ?_)
  obtain hw₂ := hw₁.of_rest r₂
  refine WP.block_append (WP.mono (zeroMask_ok hw₂ (n := 4) (a := brainpoolp256r1.sl i) a8 (by omega_using [a2]))
    fun s₃ ⟨r₃, m₃, g₃⟩ => ?_)
  refine WP.cons (exec_logicImm (by decide)) ?_
  obtain hw₃' := (hw₂.of_rest r₃).of_kp (Kp.of_upd (Upd.write s₃ .a7 (s₃.gpr .a7 ^^^ BitVec.ofInt 64 (-1))))
  refine WP.mono (andFlag_ok hw₃') fun s₄ ⟨f₄, r₄, O₄⟩ => ⟨?_, ?_, ?_⟩
  · exact (Kp.of_rest r₁).trans ((Kp.of_rest r₂).trans ((Kp.of_rest r₃).trans
      ((Kp.of_upd (Upd.write s₃ .a7 _)).trans (Kp.of_rest r₄))))
  · rw [← m₁]; exact O₂.trans (by rw [← m₃]; exact O₄)
  · have k₂ : sv base s₂ i = sv base s i := by
      show wordsVal _ _ _ _ = _
      rw [O₂.wordsVal (.inl aF) (by omega_using [a2]), m₁]
    rw [f₄]
    simp only [State.write, ↓reduceIte]
    rw [m₃, f₂, m₁, g₁, g₃, not_mask]
    simp only [sv] at k₂
    rw [k₂]

/-- The masks of `d < n` and `d ≠ 0` into the flag. -/
theorem range_ok {s : State} {base : Addr} (hw : WsReg s base) :
    WP isa (.block (rangeCode brainpoolp256r1)) s fun s' =>
      Kp s s' ∧ Outside base FL 8 s.mem s'.mem ∧
      word s'.mem base FL = word s.mem base FL &&& maskOf (decide (sv base s K < sv base s MN)) &&&
        maskOf (!decide (sv base s K = 0)) :=
  rangeOf_ok (by decide) hw

/-- The constants `tail` reads. -/
structure TailConsts (base : Addr) (s : State) : Prop where
  mp : sv base s MP = W.p
  mn : sv base s MN = W.n
  zero : sv base s ZERO = 0
  one : sv base s ONE = 1
  onep : sv base s ONEP = 1 * 2 ^ 256 % W.p
  ap : sv base s AP = W.a * 2 ^ 256 % W.p
  b3p : sv base s B3P = 3 * W.b * 2 ^ 256 % W.p
  expp : sv base s EXPP = W.p - 2

theorem mn_eq {base : Addr} {s : State} (h : TailConsts base s) : sv base s MN = W.n := h.mn

theorem TailConsts.of_unch {base : Addr} {s s' : State} {W' : List (Nat × Nat)} (h : TailConsts base s)
    (U : Unch base W' s.mem s'.mem)
    (hW : ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP], ∀ w ∈ W', brainpoolp256r1.sl i + 32 ≤ w.1 ∨ w.1 + w.2 ≤ brainpoolp256r1.sl i) :
    TailConsts base s' := by
  obtain e : ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP], sv base s' i = sv base s i := fun i hi =>
    sv_unch U i (hW i hi) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                              rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  exact ⟨(e MP (by simp)).trans h.mp, (e MN (by simp)).trans h.mn, (e ZERO (by simp)).trans h.zero,
    (e ONE (by simp)).trans h.one, (e ONEP (by simp)).trans h.onep, (e AP (by simp)).trans h.ap,
    (e B3P (by simp)).trans h.b3p, (e EXPP (by simp)).trans h.expp⟩

theorem chainLay : ChainLayR (chainP brainpoolp256r1) 4 where
  n := rfl
  k1 := by decide
  acc := by decide
  base := by decide
  tbl := by decide
  short := by decide
  acc8 := by decide
  base8 := by decide
  tbl8 := by decide
  acc_base := by decide
  acc_tbl := by decide
  base_tbl := by decide

/-- The chain is `p - 2`'s. -/
theorem chainP_ok : ChainOkR (chainP brainpoolp256r1) (W.p - 2) := ChainOkR.of_check (by lit_decide)

/-- The coordinate `[o] = [a] Z^(p-2)` out of Montgomery's form, `Z^(p-2) R` in `ACC`. -/
theorem affine_ok {s : State} {base : Addr} (hw : WsReg s base) {t o a : Nat} (ht : t < 44) (ho : o < 44)
    (ha : a < 44) (htm : t ≠ ONE ∧ t ≠ ACC) (hacc : sv base s ACC < W.p) (hone : sv base s ONE = 1) :
    WP isa (affineCoord brainpoolp256r1 t o a) s fun s' =>
      Kp s s' ∧ Unch base [(brainpoolp256r1.sl t, 32), (own 4, 256), (brainpoolp256r1.sl o, 32), (own 4, 256)] s.mem s'.mem ∧
      sv base s' o < W.p ∧
      Fin.ofNat W.p (sv base s' o) = toM W.p (2 ^ 256) (sv base s a) * toM W.p (2 ^ 256) (sv base s ACC) := by
  obtain hl : ∀ i, i < 44 → brainpoolp256r1.sl i + 8 * brainpoolp256r1Field.S.k ≤ own brainpoolp256r1Field.S.k := fun i hi => by
    show 64 + 32 * i + 32 ≤ 3840 + 0 - 0 + 0; omega_using [hi]
  obtain hs : ∀ i, i < 44 → brainpoolp256r1.sl i < 4095 := fun i hi => by rw [sl_eq]; omega_using [hi]
  have hk4 : brainpoolp256r1Field.S.k = 4 := rfl
  rw [affineCoord]
  refine WP.seq (WP.mono (mulCall_ok field_ok hw (o := brainpoolp256r1.sl t) (a := brainpoolp256r1.sl a) (b := brainpoolp256r1.sl ACC) (hl t ht)
    (hl a ha) (hl ACC (by decide)) (hs t ht) (hs a ha) (hs ACC (by decide)) hacc) fun s₁ ⟨C₁, lt₁, e₁⟩ => ?_)
  obtain one₁ : sv base s₁ ONE = 1 := by
    rw [← hone]
    exact sv_unch (C₁.mem : Unch _ _ _ _) ONE (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · simp only [sl_eq, ONE]; simp only [ONE, ACC] at htm; omega_using [htm, hk4]
      · decide)
  refine WP.mono (mulCall_ok field_ok (hw.of_kp C₁.kp) (o := brainpoolp256r1.sl o) (a := brainpoolp256r1.sl t) (b := brainpoolp256r1.sl ONE)
    (hl o ho) (hl t ht) (hl ONE (by decide)) (hs o ho) (hs t ht) (hs ONE (by decide))
    (by show sv base s₁ ONE < W.p; rw [one₁]; decide)) fun s₂ ⟨C₂, lt₂, e₂⟩ => ⟨C₁.kp.trans C₂.kp,
      Unch.trans (C₁.mem : Unch _ _ _ _) (C₂.mem : Unch _ _ _ _), lt₂, ?_⟩
  obtain e₂' : sv base s₂ o * 2 ^ 256 % W.p = sv base s₁ t * 1 % W.p := by
    rw [← one₁]; exact e₂
  rw [toM_one_mul unit e₂']
  exact toM_mul unit e₁

/-- The coordinates the multiplication's contract decodes. -/
theorem dq (hL : VG.Proof.Weierstrass.Law W) (x : Nat) : MC.toPoint.dec x = toM W.p (2 ^ 256) x :=
  VG.Proof.Weierstrass.Point.dec_eq MC.toPoint hL.one_ne_zero (VG.Proof.Weierstrass.Point.fermat_of_law hL) unit x

theorem coord_sv (m : Mem) (base : Addr) (i : Nat) (hi : i < 100 := by decide) :
    MC.toPoint.coordAt m base (brainpoolp256r1.sl i) = wordsVal m base (brainpoolp256r1.sl i) 4 :=
  coordAt_eq m base (by rw [sl_eq]; omega_using [hi])

/-- The point the multiplication's contract reads. -/
theorem point_eq (hL : VG.Proof.Weierstrass.Law W) (m : Mem) (base : Addr) :
    MC.point base m = .affine (toM W.p (2 ^ 256) (wordsVal m base (brainpoolp256r1.sl RX) 4))
      (toM W.p (2 ^ 256) (wordsVal m base (brainpoolp256r1.sl RY) 4)) := by
  unfold Impl.Weierstrass.Mul.Curve.point
  rw [dq hL, dq hL]
  show Point.affine (toM W.p (2 ^ 256) (MC.toPoint.coordAt m base (brainpoolp256r1.sl RX)))
    (toM W.p (2 ^ 256) (MC.toPoint.coordAt m base (brainpoolp256r1.sl RY))) = _
  rw [coord_sv _ _ RX, coord_sv _ _ RY]

theorem rep_of_represents {X Y Z : Fe W} {P : Point W} (h : Impl.Weierstrass.MulBase.Represents X Y Z P) :
    Rep W X Y Z P := by
  cases P <;> exact h

/-- What `tail` writes. -/
abbrev tailW : List (Nat × Nat) :=
  [(FL, 8)] ++ mulKW ++ chainWx (chainP brainpoolp256r1) 4 ++
    [(brainpoolp256r1.sl XM, 32), (own 4, 256), (brainpoolp256r1.sl XO, 32), (own 4, 256)]

/-- `tail` with a call of `mulName`, whose code is `mulCode`, that computes
`R = [d]P` as `vg_brainpoolp256r1_mul`'s contract says (`hcall`, from the state after
the range's masks, which changes only the flag): the range of `d` into the
flag, `R = [d]P`, `Z^(p-2)`, and `x`. -/
theorem tailWith_ok (hL : VG.Proof.Weierstrass.Law W) {mulName : String} {mulCode : Prog isa} {s : State}
    {base : Addr} (hw : WsReg s base)
    (h3 : s.gpr .s3 = base) (hc : TailConsts base s)
    (hcall : ∀ s₁ : State, WsReg s₁ base → s₁.gpr .s3 = base → Kp s s₁ → Unch base [(FL, 8)] s.mem s₁.mem →
      s₁.syms = s.syms →
      WP isa (Cfg.wsCall mulName mulCode) s₁ fun s₂ => Kp s₁ s₂ ∧
        MC.ResultInRange (MC.scalar base s₁.mem) (MC.point base s₁.mem) base s₁.mem s₂.mem) :
    WP isa (tail brainpoolp256r1 mulName mulCode) s fun s' =>
      Kc s s' ∧ Unch base tailW s.mem s'.mem ∧
      word s'.mem base FL = word s.mem base FL &&& maskOf (decide (sv base s K < W.n)) &&&
        maskOf (!decide (sv base s K = 0)) ∧
      (1 ≤ sv base s K → sv base s K < W.n →
        Rep W (toM W.p (2 ^ 256) (sv base s' RX)) (toM W.p (2 ^ 256) (sv base s' RY))
          (toM W.p (2 ^ 256) (sv base s' RZ))
          (Spec.Weierstrass.mul (sv base s K) (.affine (toM W.p (2 ^ 256) (sv base s RX))
            (toM W.p (2 ^ 256) (sv base s RY)))) ∧
        sv base s' RX < W.p ∧ sv base s' RY < W.p ∧ sv base s' RZ < W.p) ∧
      sv base s' XO < W.p ∧
      Fin.ofNat W.p (sv base s' XO) =
        toM W.p (2 ^ 256) (sv base s' RX) * toM W.p (2 ^ 256) (sv base s' RZ) ^ (W.p - 2) ∧
      sv base s' ACC < W.p ∧
      toM W.p (2 ^ 256) (sv base s' ACC) = toM W.p (2 ^ 256) (sv base s' RZ) ^ (W.p - 2) := by
  obtain hp0 : 0 < W.p := by decide
  rw [tail]
  -- The range.
  refine WP.seq (WP.mono (show WP isa _ s fun s' => _ ∧ s'.syms = s.syms from
    let ⟨t, s', he, hq⟩ := range_ok hw; ⟨t, s', he, hq, Exec.syms he⟩) fun s₁ ⟨⟨K₁, O₁, f₁⟩, sy₁⟩ => ?_)
  obtain hw₁ := hw.of_kp K₁
  have U₁ := O₁.unch
  obtain e₁ : ∀ i, i < 44 → sv base s₁ i = sv base s i := fun i hi =>
    sv_unch U₁ i (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; rw [sl_eq, FL]; omega_using [hi])
      (by omega_using [hi])
  obtain hc₁ := hc.of_unch U₁ (by decide)
  rw [mn_eq hc] at f₁
  -- The multiplication.
  refine WP.seq (WP.mono (hcall s₁ hw₁ (by rw [K₁.gpr _ (by decide)]; exact h3) K₁ U₁ sy₁) fun s₂ ⟨K₂, hp₂'⟩ => ?_)
  obtain ⟨hR, hK⟩ := hp₂'
  obtain U₂ : Unch base mulKW s₁.mem s₂.mem := unch_of_mulKeeps hK
  obtain hw₂ := hw₁.of_kp K₂
  obtain hc₂ := hc₁.of_unch U₂ (by decide)
  -- `Z^(p-2)`.
  refine WP.seq (WP.mono (chainPow_ok (P := chainP brainpoolp256r1) (F := brainpoolp256r1Field) field_ok chainLay unit hw₂
    (one := brainpoolp256r1.sl ONEP) (by decide) (by decide)
    (by show sv base s₂ ONEP = _; rw [hc₂.onep]; rfl) chainP_ok) fun s₃ ⟨K₃, U₃, lt₃, v₃⟩ => ?_)
  obtain hw₃ := hw₂.of_kc K₃
  obtain hc₃ := hc₂.of_unch U₃ (by decide)
  -- `x`.
  refine WP.mono (affine_ok hw₃ (t := XM) (o := XO) (a := RX) (by decide) (by decide) (by decide) (by decide)
    lt₃ hc₃.one) fun s₄ ⟨K₄, U₄, lt₄, v₄⟩ => ?_
  obtain e₄ : ∀ i ∈ [RX, RY, RZ], sv base s₄ i = sv base s₂ i := fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    obtain h3 : sv base s₃ i = sv base s₂ i := sv_unch U₃ i (by rcases hi with rfl | rfl | rfl <;> decide)
      (by rcases hi with rfl | rfl | rfl <;> decide)
    rw [← h3]
    exact sv_unch U₄ i (by rcases hi with rfl | rfl | rfl <;> decide) (by rcases hi with rfl | rfl | rfl <;> decide)
  obtain fl₄ : word s₄.mem base FL = word s₁.mem base FL :=
    fl_unch ((U₂.trans U₃).trans U₄) (by decide)
  obtain k₁ : MC.scalar base s₁.mem = sv base s K := by
    rw [← e₁ K (by decide)]; exact coord_sv _ _ K
  obtain acc₄ : sv base s₄ ACC = sv base s₃ ACC := sv_unch U₄ ACC (by decide)
  have v₃' : toM W.p (2 ^ 256) (sv base s₃ ACC) = toM W.p (2 ^ 256) (sv base s₂ RZ) ^ (W.p - 2) := v₃
  refine ⟨K₁.kc.trans (K₂.kc.trans (K₃.trans K₄.kc)), ((U₁.trans U₂).trans U₃).trans U₄, by rw [fl₄, f₁], ?_, lt₄,
    ?_, by rw [acc₄]; exact lt₃, by rw [acc₄, v₃', e₄ RZ (by simp)]⟩
  · intro h1 hn
    rw [k₁, point_eq hL] at hR
    obtain ⟨⟨bx, by', bz⟩, hrep⟩ := hR h1 hn
    simp only [Impl.Weierstrass.Point.Curve.pointAt] at bx by' bz hrep
    obtain c0 : MC.toPoint.coordAt s₂.mem base MC.pAt = sv base s₂ RX := coord_sv _ _ RX
    obtain c1 : MC.toPoint.coordAt s₂.mem base (MC.pAt + Impl.Weierstrass.Point.elemBytes MC.toPoint.k) =
      sv base s₂ RY := coord_sv _ _ RY
    obtain c2 : MC.toPoint.coordAt s₂.mem base (MC.pAt + 2 * Impl.Weierstrass.Point.elemBytes MC.toPoint.k) =
      sv base s₂ RZ := coord_sv _ _ RZ
    rw [c0, c1, c2] at hrep
    rw [c0] at bx; rw [c1] at by'; rw [c2] at bz
    rw [dq hL, dq hL, dq hL] at hrep
    rw [e₄ RX (by simp), e₄ RY (by simp), e₄ RZ (by simp), ← e₁ RX (by decide), ← e₁ RY (by decide)]
    exact ⟨rep_of_represents hrep, bx, by', bz⟩
  · rw [v₄, v₃', e₄ RX (by simp), e₄ RZ (by simp),
      show sv base s₃ RX = sv base s₂ RX from sv_unch U₃ RX (by decide)]


/-- A byte of a region apart from the working space. -/
theorem out_of_disj {p base : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) (hn : p.toNat + n ≤ 2 ^ 64)
    {off i : Nat} (hi : off + i < n) : ¬ (⟨base, 8192⟩ : Region).Contains (p + BitVec.ofNat 64 (off + i)) 1 :=
  hd _ (Offset.contains_base p (by omega_using [hi]) (by omega_using [hn, hi]))

/-- Eight bytes of a region. -/
theorem in_rd8 {rs : List Region} {p : Addr} {n : Nat} (hr : (⟨p, n⟩ : Region) ∈ rs) {off : Nat} (ho : off + 8 ≤ n)
    (hn : n ≤ 8192 := by decide) :
    InRegions rs (p + BitVec.ofNat 64 off) 8 :=
  ⟨_, hr, Offset.contains_base p ho (by omega_using [ho, hn])⟩

/-- Bytes apart from the working space survive changes within it. -/
theorem bytesAt_unch {base q : Addr} {W : List (Nat × Nat)} {n : Nat} {m m' : Mem} (U : Unch base W m m')
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ 8192)
    (hsep : ∀ i < n, ¬ (⟨base, 8192⟩ : Region).Contains (q + BitVec.ofNat 64 i) 1) :
    bytesAt m' q n = bytesAt m q n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have := hsep i hi
  simp only [Region.Contains] at this
  exact U _ fun w hw => .inr (by have := hW w hw; simp only [ofs]; omega_arith)

/-- The value of a constant's slot. -/
theorem const_at {base : Addr} {s : State} (hc : ∀ e ∈ consts brainpoolp256r1, sv base s e.1 = e.2) (k : Nat)
    (hk : k < (consts brainpoolp256r1).length := by decide) : sv base s (consts brainpoolp256r1)[k].1 = (consts brainpoolp256r1)[k].2 :=
  hc _ (List.getElem_mem hk)

/-- The bytes just written. -/
theorem bytesAt_writeBytes (m : Mem) (q : Addr) (xs : List Byte) (h : xs.length ≤ 2 ^ 64) :
    bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem
  · simp [bytesAt]
  · intro i h₁ h₂
    have hi : i < xs.length := h₂
    simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes,
      Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hi h), hi,
      ite_true, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem and_one (b : Bool) : maskOf b &&& BitVec.ofInt 64 1 = if b then 1 else 0 := by cases b <;> decide

/-- Bytes of a region apart from the working space, from an offset. -/
theorem sep_at' {p base : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) (hn : p.toNat + n ≤ 2 ^ 64)
    {off k : Nat} (hk : off + k ≤ n) :
    ∀ i < k, ¬ (⟨base, 8192⟩ : Region).Contains (p + BitVec.ofNat 64 off + BitVec.ofNat 64 i) 1 := fun i hi => by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact out_of_disj hd hn (by omega_using [hk, hi])


/-- `tail` with `vg_brainpoolp256r1_mul`. -/
theorem tail_ok (hL : VG.Proof.Weierstrass.Law W) {s : State} {base : Addr} (hw : WsReg s base)
    (h3 : s.gpr .s3 = base) (hc : TailConsts base s) (hx : sv base s RX < W.p) (hy : sv base s RY < W.p)
    (hon : Spec.Weierstrass.onCurve W (.affine (toM W.p (2 ^ 256) (sv base s RX))
      (toM W.p (2 ^ 256) (sv base s RY))) = true) :
    WP isa (tail brainpoolp256r1 "vg_brainpoolp256r1_mul" mulBrainpoolP256r1) s fun s' =>
      Kc s s' ∧ Unch base tailW s.mem s'.mem ∧
      word s'.mem base FL = word s.mem base FL &&& maskOf (decide (sv base s K < W.n)) &&&
        maskOf (!decide (sv base s K = 0)) ∧
      (1 ≤ sv base s K → sv base s K < W.n →
        Rep W (toM W.p (2 ^ 256) (sv base s' RX)) (toM W.p (2 ^ 256) (sv base s' RY))
          (toM W.p (2 ^ 256) (sv base s' RZ))
          (Spec.Weierstrass.mul (sv base s K) (.affine (toM W.p (2 ^ 256) (sv base s RX))
            (toM W.p (2 ^ 256) (sv base s RY)))) ∧
        sv base s' RX < W.p ∧ sv base s' RY < W.p ∧ sv base s' RZ < W.p) ∧
      sv base s' XO < W.p ∧
      Fin.ofNat W.p (sv base s' XO) =
        toM W.p (2 ^ 256) (sv base s' RX) * toM W.p (2 ^ 256) (sv base s' RZ) ^ (W.p - 2) ∧
      sv base s' ACC < W.p ∧
      toM W.p (2 ^ 256) (sv base s' ACC) = toM W.p (2 ^ 256) (sv base s' RZ) ^ (W.p - 2) := by
  refine tailWith_ok hL hw h3 hc fun s₁ hw₁ h3₁ K₁ U₁ _ => ?_
  obtain hc₁ := hc.of_unch U₁ (by decide)
  obtain e₁ : ∀ i, i < 44 → sv base s₁ i = sv base s i := fun i hi =>
    sv_unch U₁ i (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; rw [sl_eq, FL]; omega_using [hi])
      (by omega_using [hi])
  refine wsCallR_ok Impl.Ecdsa.RISCV64.mulBrainpoolP256r1_noFrames (mul_rv hL) hw₁ h3₁
    (fun t r w a m => ?_)
    fun s₂' s₂ K₂ mm₂ t a₂ m₂ hp₂ => ⟨K₂, ?_⟩
  · refine ⟨r, by rw [w, a], by rw [a]; exact hw₁.nowrap, by rw [a]; exact hw₁.al, ?_, ?_⟩
    · rw [a, m]
      refine ⟨(coord_sv _ _ MP).trans hc₁.mp, (coord_sv _ _ ZERO).trans hc₁.zero,
        (coord_sv _ _ ONEP).trans hc₁.onep, (coord_sv _ _ AP).trans hc₁.ap, (coord_sv _ _ B3P).trans hc₁.b3p⟩
    · rw [a, m]
      refine ⟨?_, ?_, ?_⟩
      · show MC.toPoint.coordAt s₁.mem base (brainpoolp256r1.sl RX) < W.p
        rw [coord_sv _ _ RX]; exact Nat.lt_of_le_of_lt (Nat.le_of_eq (e₁ RX (by decide))) hx
      · show MC.toPoint.coordAt s₁.mem base (brainpoolp256r1.sl RY) < W.p
        rw [coord_sv _ _ RY]; exact Nat.lt_of_le_of_lt (Nat.le_of_eq (e₁ RY (by decide))) hy
      rw [point_eq hL]
      show Spec.Weierstrass.onCurve W (.affine (toM _ _ (sv base s₁ RX)) (toM _ _ (sv base s₁ RY))) = true
      rw [e₁ RX (by decide), e₁ RY (by decide)]; exact hon
  · have := hp₂
    simp only [mulRVc, State.withRegions_mem] at this
    rw [a₂, m₂, ← mm₂] at this
    exact this

end VG.Proof.Ecdh.RISCV64.BrainpoolP256r1
