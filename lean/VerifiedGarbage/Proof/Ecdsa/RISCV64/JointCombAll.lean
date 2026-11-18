module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyComb
public import VerifiedGarbage.Proof.Ecdh.RISCV64.ExchangeAll
import VerifiedGarbage.Proof.Ecdsa.RISCV64.SignAll
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Copy
import VerifiedGarbage.Proof.Ecdh.RISCV64.Masks
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Syms

/-!
# ECDSA verification on RISC-V: `[u]G` by the comb and `[v]Q` by windows, for every curve

`VerifyComb.Cfg.joint` leaves in `R` a representative of `[u]G + [v]Q`
(`Kit.jointComb_ok`), once for every curve with a comb: `[v]Q` by the call of
the curve's multiplication (ECDH's kit's, `mulCall_ok`), `O` instead if
`v = 0` (`zeroR_ok`), moved to `P = (GX : CPX : CPY)`; `[u]G` by the call of
the comb's, and `O` instead if `u = 0`; then their sum by the complete
addition. What the proof needs of a curve beside ECDH's kit is the comb's
call (`comb_ok`) with what it needs beside the working space, its table
(`Tab`, which code without frames and changes within the working space keep),
and the complete addition of `R` and `P` (`add_ok`). Each
`<Curve>/JointComb.lean` is the curve's kit, from its comb's and its
addition's proofs.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.JointCombAll

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.Verify
open VG.Impl.Ecdsa.RISCV64.VerifyComb
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Point Fe mul onCurve)
open VG.Proof.Ecdh.RISCV64 (TKit)
open VG.Proof.Ecdh.RISCV64.Kit (sv sl8 sl_le sl_sep sl_top all_app all_one wsCallR_ok rep_of_represents)
open VG.Proof.Ecdsa.RISCV64.SignAll (sl_64 all_cons sv_unch run_apart)

/-- `∀ w ∈ W, P w` for ranges `W` given as a list of lists: `t` proves it of each. -/
local macro "ranges" t:tacticSeq : tactic =>
  `(tactic| ((repeat' first | with_reducible apply all_app | with_reducible apply all_one); all_goals ($t)))

/-- What follows code may assume it names the same addresses of statics as before. -/
theorem wp_syms {c : Prog isa} {s : State} {Q R : State → Prop} (h : WP isa c s Q)
    (k : ∀ s', Q s' → s'.syms = s.syms → R s') : WP isa c s R := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, k s' hq (Exec.syms he)⟩

theorem wsCall_noFrames {f : String} {b : Prog isa} (h : b.noFrames = true) : (Cfg.wsCall f b).noFrames = true := by
  simp only [Cfg.wsCall, Code.noFrames, h, Bool.and_self]

theorem mul_zero' {C : Spec.Weierstrass.Curve} (P : Point C) : mul 0 P = .infinity := by
  rw [Spec.Weierstrass.mul]; rfl

/-! ## Points in slots -/

/-- A point in the slots `p`: its coordinates below `p`, representing `P`. -/
structure PtOk (c : Cfg) (base : Addr) (s : State) (p : Pt) (P : Point c.C) : Prop where
  rep : Rep c.C (tmv c.C c.n base s p.x) (tmv c.C c.n base s p.y) (tmv c.C c.n base s p.z) P
  x : wordsVal s.mem base p.x c.n < c.C.p
  y : wordsVal s.mem base p.y c.n < c.C.p
  z : wordsVal s.mem base p.z c.n < c.C.p

theorem PtOk.of_eq {c : Cfg} {base : Addr} {s s' : State} {p : Pt} {P : Point c.C} (h : PtOk c base s p P)
    (hx : wordsVal s'.mem base p.x c.n = wordsVal s.mem base p.x c.n)
    (hy : wordsVal s'.mem base p.y c.n = wordsVal s.mem base p.y c.n)
    (hz : wordsVal s'.mem base p.z c.n = wordsVal s.mem base p.z c.n) : PtOk c base s' p P :=
  ⟨by simp only [tmv]; rw [hx, hy, hz]; exact h.rep, by rw [hx]; exact h.x, by rw [hy]; exact h.y,
    by rw [hz]; exact h.z⟩

/-- A point copied to other slots. -/
theorem PtOk.move {c : Cfg} {base : Addr} {s s' : State} {p q : Pt} {P : Point c.C} (h : PtOk c base s p P)
    (hx : wordsVal s'.mem base q.x c.n = wordsVal s.mem base p.x c.n)
    (hy : wordsVal s'.mem base q.y c.n = wordsVal s.mem base p.y c.n)
    (hz : wordsVal s'.mem base q.z c.n = wordsVal s.mem base p.z c.n) : PtOk c base s' q P :=
  ⟨by simp only [tmv]; rw [hx, hy, hz]; exact h.rep, by rw [hx]; exact h.x, by rw [hy]; exact h.y,
    by rw [hz]; exact h.z⟩

/-! ## Slots and what the steps write -/

/-- What `zeroR` writes. -/
abbrev zW (c : Cfg) : List (Nat × Nat) :=
  [(c.sl RX, 8 * c.n), (c.sl RY, 8 * c.n), (c.sl RZ, 8 * c.n), (c.sl BP, 8 * c.n)]

theorem zW_keep (c : Cfg) {i : Nat} (h : i ≠ RX ∧ i ≠ RY ∧ i ≠ RZ ∧ i ≠ BP) :
    ∀ w ∈ zW c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  all_cons (sl_sep c h.1) (all_cons (sl_sep c h.2.1) (all_cons (sl_sep c h.2.2.1) (all_one (sl_sep c h.2.2.2))))

theorem zW_top {c : Cfg} (h9 : c.n ≤ 9) : ∀ w ∈ zW c, w.1 + w.2 ≤ 8192 :=
  all_cons (Nat.le_trans (sl_top h9 (by decide)) (by decide)) (all_cons (Nat.le_trans (sl_top h9 (by decide)) (by decide))
    (all_cons (Nat.le_trans (sl_top h9 (by decide)) (by decide))
      (all_one (Nat.le_trans (sl_top h9 (by decide)) (by decide)))))

/-- A multiplication keeps the slots that are not its own. -/
theorem mulKW_keep (c : Cfg) {i : Nat}
    (h : (i < 14 ∨ 14 + 3 ≤ i) ∧ (i < 17 ∨ 17 + 14 ≤ i) ∧ i ≠ 2 ∧ i ≠ 40 ∧ i < 45) :
    ∀ w ∈ TKit.mulKW c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  all_cons (run_apart c (by omega) h.1) (all_cons (run_apart c (by omega) h.2.1) (all_cons (sl_sep c h.2.2.1)
    (all_cons (sl_sep c h.2.2.2.1) (all_one (.inl (sl_le c h.2.2.2.2))))))

/-- The slots of the constants `tail` reads. -/
abbrev cst : List Nat := [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP]

/-- They are apart from the slots the steps write. -/
theorem cst_sep (c : Cfg) {i j : Nat} (hi : i ∈ cst) (hj : j ∈ [GX, RX, RY, RZ, K, CPX, BP, CPY]) :
    c.sl i + 8 * c.n ≤ c.sl j ∨ c.sl j + 8 * c.n ≤ c.sl i :=
  sl_sep c ((by decide : ∀ i ∈ cst, ∀ j ∈ [GX, RX, RY, RZ, K, CPX, BP, CPY], i ≠ j) i hi j hj)

theorem cst_mulKW (c : Cfg) {i : Nat} (hi : i ∈ cst) :
    ∀ w ∈ TKit.mulKW c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  mulKW_keep c ((by decide : ∀ i ∈ cst,
    (i < 14 ∨ 14 + 3 ≤ i) ∧ (i < 17 ∨ 17 + 14 ≤ i) ∧ i ≠ 2 ∧ i ≠ 40 ∧ i < 45) i hi)

theorem cst_zW (c : Cfg) {i : Nat} (hi : i ∈ cst) : ∀ w ∈ zW c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  zW_keep c ((by decide : ∀ i ∈ cst, i ≠ RX ∧ i ≠ RY ∧ i ≠ RZ ∧ i ≠ BP) i hi)

/-- A slot apart from ranges that are other slots, a multiplication's or `zeroR`'s. -/
local macro "apart" : tactic =>
  `(tactic| ranges (first
    | exact sl_sep _ (by decide)
    | exact mulKW_keep _ (by decide)
    | exact zW_keep _ (by decide)))

/-- The same of a constant's slot, the `hi`th of `cst`. -/
local macro "apart_cst" hi:term : tactic =>
  `(tactic| ranges (first
    | exact cst_sep _ $hi (by decide)
    | exact cst_mulKW _ $hi
    | exact cst_zW _ $hi))

/-- A copy of a number between slots. -/
theorem copySl_ok (c : Cfg) (h9 : c.n ≤ 9) {s : State} {base : Addr} (hw : WsReg s base) {o a : Nat}
    (ho : o ≤ 55) (ha : a ≤ 55) (hne : o ≠ a) :
    WP isa (.block (copy c.n (c.sl o) (c.sl a))) s fun s' =>
      sv c base s' o = sv c base s a ∧ Rest [.t0] s s' ∧ Unch base [(c.sl o, 8 * c.n)] s.mem s'.mem :=
  WP.mono (copy_ok c.n hw (sl8 _ _) (sl8 _ _) (sl_top h9 ho) (sl_top h9 ha)
    ((Nat.lt_or_gt_of_ne hne).imp (fun h => Nat.le_trans (Nat.le_add_right _ _) (sl_le c h)) (sl_le c)))
    fun _ ⟨e, r, O⟩ => ⟨e, r, O.unch⟩

/-- One coordinate of `R`, at slot `o`, set to the one at slot `b` if the mask
`a7` is all ones (`z`), as it is if it is zero. -/
theorem selR_ok (c : Cfg) (h9 : c.n ≤ 9) {s : State} {base : Addr} (hw : WsReg s base) (z : Bool)
    (hc : s.gpr .a7 = (if z then BitVec.allOnes 64 else 0)) {o b : Nat}
    (ho : o ∈ [RX, RY, RZ]) (hb : b ∈ [ZERO, ONEP]) :
    WP isa (.block (sel c.n (c.sl o) (c.sl o) (c.sl b))) s fun s' =>
      sv c base s' o = (if z then sv c base s b else sv c base s o) ∧ Rest [.t0, .t1] s s' ∧
      Outside base (c.sl o) (8 * c.n) s.mem s'.mem := by
  obtain ⟨h1, h2, h3⟩ := (by decide : ∀ o ∈ [RX, RY, RZ], ∀ b ∈ [ZERO, ONEP], o ≤ 55 ∧ b ≤ 55 ∧ b < o) o ho b hb
  exact sel_ok z c.n hw hc (sl8 _ _) (sl8 _ _) (sl8 _ _) (sl_top h9 h1) (sl_top h9 h1) (sl_top h9 h2)
    (.inl (Nat.le_refl _)) (.inr (sl_le c h3))

/-! ## The kit -/

/-- What the proof needs of a curve, beside ECDH's kit: its comb's call, with the table, and its
complete addition. -/
structure Kit extends VG.Proof.Ecdh.RISCV64.Kit where
  /-- The comb's multiplication of `G`: its name and its code. -/
  gN : String
  gC : Prog isa
  /-- What the comb needs beside the working space at `base`: its table. Code without frames keeps
  it, apart from the regions it may write, and so does what changes memory only in the working
  space. -/
  Tab : Addr → State → Prop
  tab_frame : ∀ {cd : Prog isa}, cd.noFrames = true → ∀ {s : State} {base : Addr} {Q : State → Prop},
    Tab base s → s.wr = [⟨base, 8192⟩] → WP isa cd s Q → WP isa cd s fun s' => Q s' ∧ Tab base s'
  tab_unch : ∀ {base : Addr} {s s' : State} {W : List (Nat × Nat)}, Tab base s → s'.syms = s.syms →
    s'.rd = s.rd → (∀ w ∈ W, w.1 + w.2 ≤ 8192) → Unch base W s.mem s'.mem → Tab base s'
  /-- `R = [k]G` by the comb's call, for `k` at `K`, with the table its readable region. -/
  comb_ok : Law c.C → ∀ {s : State} {base : Addr}, WsReg s base → s.gpr .s3 = base → TKit.Consts c base s →
    sv c base s BP = c.C.b * 2 ^ (64 * c.n) % c.C.p → Tab base s →
    WP isa (Cfg.wsCall gN gC) s fun s' => Kp s s' ∧
      toTKit.MC.ResultInRange (sv c base s K) (Spec.Weierstrass.G c.C) base s.mem s'.mem
  /-- What the complete addition writes. -/
  addW : List (Nat × Nat)
  /-- `T = R + P` by the complete addition, for `P` in `(GX, CPX, CPY)`. -/
  add_ok : Law c.C → ∀ {s : State} {base : Addr}, WsReg s base → TKit.Consts c base s →
    sv c base s BP = c.C.b * 2 ^ (64 * c.n) % c.C.p →
    ∀ {P P' : Point c.C}, onCurve c.C P = true → onCurve c.C P' = true →
    PtOk c base s (c.pt RX RY RZ) P → PtOk c base s (c.pt GX CPX CPY) P' →
    WP isa (Verify.Cfg.addPt c (c.pt RX RY RZ) (c.pt GX CPX CPY) (c.pt TX TY TZ)) s fun s' =>
      Kp s s' ∧ Unch base addW s.mem s'.mem ∧ PtOk c base s' (c.pt TX TY TZ) (Spec.Weierstrass.add P P')

namespace Kit

variable (Kt : Kit)

/-- `b` in Montgomery's form, as `zeroR` sets it. -/
theorem bp_val : Cfg.mont Kt.c Kt.c.C.b % 2 ^ (64 * Kt.c.n) = Kt.c.C.b * 2 ^ (64 * Kt.c.n) % Kt.c.C.p :=
  Nat.mod_eq_of_lt (Kt.consts_lt (BP, Cfg.mont Kt.c Kt.c.C.b) (by simp [Cfg.consts]))

/-- `R = O` if the number at slot `a` is zero, else `R` as it is, and `b` to `BP`. -/
theorem zeroR_ok (hL : Law Kt.c.C) {s : State} {base : Addr} (hw : WsReg s base) (hz : sv Kt.c base s ZERO = 0)
    (ho : sv Kt.c base s ONEP = 1 * 2 ^ (64 * Kt.c.n) % Kt.c.C.p) {a : Nat} (ha : a = UU ∨ a = VV)
    {P : Point Kt.c.C} (hR : sv Kt.c base s a ≠ 0 → PtOk Kt.c base s (Kt.c.pt RX RY RZ) P) :
    WP isa (.block (VerifyComb.Cfg.zeroR Kt.c a)) s fun s' =>
      Rest [.t0, .t1, .t3, .t4, .a7] s s' ∧ Unch base (zW Kt.c) s.mem s'.mem ∧
      PtOk Kt.c base s' (Kt.c.pt RX RY RZ) (if sv Kt.c base s a = 0 then .infinity else P) ∧
      sv Kt.c base s' BP = Kt.c.C.b * 2 ^ (64 * Kt.c.n) % Kt.c.C.p := by
  obtain h9 := Kt.n9
  obtain hU := Kt.unit
  obtain hp0 : 0 < Kt.c.C.p := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain ha' : a ≤ 55 := by rcases ha with rfl | rfl <;> decide
  rw [VerifyComb.Cfg.zeroR, List.append_assoc]
  refine WP.block_append (WP.mono (zeroMask_ok (n := Kt.c.n) hw (sl8 _ _) (sl_top h9 ha')) fun s₁ ⟨r₁, m₁, k₁⟩ => ?_)
  obtain hw₁ := hw.of_rest r₁
  generalize hzb : decide (sv Kt.c base s a = 0) = z
  obtain hc₁ : s₁.gpr .a7 = (if z then BitVec.allOnes 64 else 0) := by
    rw [k₁, ← hzb]
  obtain e₁ : ∀ i, sv Kt.c base s₁ i = sv Kt.c base s i := fun i => by
    show wordsVal s₁.mem _ _ _ = wordsVal s.mem _ _ _; rw [m₁]
  rw [show VerifyComb.Cfg.oPt Kt.c = Kt.c.pt ZERO ONEP ZERO from rfl, selPt, List.append_assoc, List.append_assoc]
  refine WP.block_append (WP.mono (selR_ok Kt.c h9 hw₁ z hc₁ (o := RX) (b := ZERO) (by decide) (by decide))
    fun s₂ ⟨x₂, r₂, O₂⟩ => ?_)
  obtain hw₂ := hw₁.of_rest r₂
  obtain hc₂ : s₂.gpr .a7 = _ := (r₂.gpr .a7 (by decide)).trans hc₁
  refine WP.block_append (WP.mono (selR_ok Kt.c h9 hw₂ z hc₂ (o := RY) (b := ONEP) (by decide) (by decide))
    fun s₃ ⟨y₃, r₃, O₃⟩ => ?_)
  obtain hw₃ := hw₂.of_rest r₃
  obtain hc₃ : s₃.gpr .a7 = _ := (r₃.gpr .a7 (by decide)).trans hc₂
  refine WP.block_append (WP.mono (selR_ok Kt.c h9 hw₃ z hc₃ (o := RZ) (b := ZERO) (by decide) (by decide))
    fun s₄ ⟨z₄, r₄, O₄⟩ => ?_)
  obtain hw₄ := hw₃.of_rest r₄
  refine WP.mono (setConst_ok Kt.c.n hw₄ (o := Kt.c.sl BP) (x := Cfg.mont Kt.c Kt.c.C.b) (sl8 _ _)
    (sl_top h9 (by decide))) fun s₅ ⟨r₅, O₅, b₅⟩ => ⟨?_, ?_, ?_, by rw [← Kt.bp_val]; exact b₅⟩
  · exact (r₁.mono (ws' := [.t0, .t1, .t3, .t4, .a7]) (by decide)).trans
      ((r₂.mono (by decide)).trans ((r₃.mono (by decide)).trans ((r₄.mono (by decide)).trans (r₅.mono (by decide)))))
  · rw [← m₁]
    exact ((O₂.unch.trans O₃.unch).trans O₄.unch).trans O₅.unch
  · -- Each coordinate, through the later steps.
    obtain U₂₅ := ((O₃.unch.trans O₄.unch).trans O₅.unch)
    obtain U₃₅ := (O₄.unch.trans O₅.unch)
    obtain fx : sv Kt.c base s₅ RX = sv Kt.c base s₂ RX := sv_unch h9 U₂₅ RX (by apart)
    obtain fy : sv Kt.c base s₅ RY = sv Kt.c base s₃ RY := sv_unch h9 U₃₅ RY (by apart)
    obtain fz : sv Kt.c base s₅ RZ = sv Kt.c base s₄ RZ := sv_unch h9 O₅.unch RZ (by apart)
    obtain gy : sv Kt.c base s₂ RY = sv Kt.c base s₁ RY := sv_unch h9 O₂.unch RY (by apart)
    obtain gz : sv Kt.c base s₃ RZ = sv Kt.c base s₁ RZ := sv_unch h9 (O₂.unch.trans O₃.unch) RZ (by apart)
    obtain g1 : sv Kt.c base s₂ ONEP = sv Kt.c base s₁ ONEP := sv_unch h9 O₂.unch ONEP (by apart)
    obtain g0' : sv Kt.c base s₃ ZERO = sv Kt.c base s₁ ZERO := sv_unch h9 (O₂.unch.trans O₃.unch) ZERO (by apart)
    obtain ex : sv Kt.c base s₅ RX = if z then 0 else sv Kt.c base s RX := by
      rw [fx, x₂, e₁ ZERO, e₁ RX, hz]
    obtain ey : sv Kt.c base s₅ RY = if z then 1 * 2 ^ (64 * Kt.c.n) % Kt.c.C.p else sv Kt.c base s RY := by
      rw [fy, y₃, g1, gy, e₁ ONEP, e₁ RY, ho]
    obtain ez : sv Kt.c base s₅ RZ = if z then 0 else sv Kt.c base s RZ := by
      rw [fz, z₄, g0', gz, e₁ ZERO, e₁ RZ, hz]
    by_cases h0 : sv Kt.c base s a = 0
    · rw [ite_eq_left h0]
      obtain hz' : z = true := by rw [← hzb]; exact decide_eq_true h0
      rw [hz'] at ex ey ez
      simp only [↓reduceIte] at ex ey ez
      refine ⟨?_, by show sv Kt.c base s₅ RX < Kt.c.C.p; rw [ex]; exact hp0,
        by show sv Kt.c base s₅ RY < Kt.c.C.p; rw [ey]; exact Nat.mod_lt _ hp0,
        by show sv Kt.c base s₅ RZ < Kt.c.C.p; rw [ez]; exact hp0⟩
      show Rep Kt.c.C (tmv Kt.c.C Kt.c.n base s₅ (Kt.c.sl RX)) (tmv Kt.c.C Kt.c.n base s₅ (Kt.c.sl RY))
        (tmv Kt.c.C Kt.c.n base s₅ (Kt.c.sl RZ)) _
      obtain t0 : tmv Kt.c.C Kt.c.n base s₅ (Kt.c.sl RX) = 0 := by
        simp only [tmv]; rw [show wordsVal _ _ _ _ = 0 from ex]; exact toM_zero _ _
      obtain t1 : tmv Kt.c.C Kt.c.n base s₅ (Kt.c.sl RY) = 1 := by
        simp only [tmv]; rw [show wordsVal _ _ _ _ = 1 * 2 ^ (64 * Kt.c.n) % Kt.c.C.p from ey, Nat.one_mul]
        exact toM_one hU
      obtain t2 : tmv Kt.c.C Kt.c.n base s₅ (Kt.c.sl RZ) = 0 := by
        simp only [tmv]; rw [show wordsVal _ _ _ _ = 0 from ez]; exact toM_zero _ _
      rw [t0, t1, t2]
      exact rep_infinity' hL
    · rw [ite_eq_right h0]
      obtain hz' : z = false := by rw [← hzb]; exact decide_eq_false h0
      rw [hz'] at ex ey ez
      simp only [Bool.false_eq_true, ↓reduceIte] at ex ey ez
      exact (hR h0).of_eq ex ey ez

/-! ## The calls -/

/-- The result of a call, as the contracts give it, in `R`'s slots. -/
theorem ptOk_of_result (hL : Law Kt.c.C) {base : Addr} {m : Mem} {s' : State} {k : Nat} {P : Point Kt.c.C}
    (hR : Kt.toTKit.MC.ResultInRange k P base m s'.mem) (h1 : 1 ≤ k) (hn : k < Kt.c.C.n) :
    PtOk Kt.c base s' (Kt.c.pt RX RY RZ) (mul k P) := by
  obtain ⟨⟨bx, by', bz⟩, hrep⟩ := hR.1 h1 hn
  simp only [Impl.Weierstrass.Point.Curve.pointAt] at bx by' bz hrep
  obtain c0 : Kt.toTKit.MC.toPoint.coordAt s'.mem base Kt.toTKit.MC.pAt = sv Kt.c base s' RX :=
    Kt.toTKit.coord_sv _ _ RX (by decide)
  obtain c1 : Kt.toTKit.MC.toPoint.coordAt s'.mem base
      (Kt.toTKit.MC.pAt + Impl.Weierstrass.Point.elemBytes Kt.toTKit.MC.toPoint.k) = sv Kt.c base s' RY := by
    rw [show Kt.toTKit.MC.pAt + Impl.Weierstrass.Point.elemBytes Kt.toTKit.MC.toPoint.k = Kt.c.sl RY from
      Kt.toTKit.pAt_y]
    exact Kt.toTKit.coord_sv _ _ RY (by decide)
  obtain c2 : Kt.toTKit.MC.toPoint.coordAt s'.mem base
      (Kt.toTKit.MC.pAt + 2 * Impl.Weierstrass.Point.elemBytes Kt.toTKit.MC.toPoint.k) = sv Kt.c base s' RZ := by
    rw [show Kt.toTKit.MC.pAt + 2 * Impl.Weierstrass.Point.elemBytes Kt.toTKit.MC.toPoint.k = Kt.c.sl RZ from
      Kt.toTKit.pAt_z]
    exact Kt.toTKit.coord_sv _ _ RZ (by decide)
  rw [c0, c1, c2] at hrep
  rw [c0] at bx; rw [c1] at by'; rw [c2] at bz
  rw [Kt.toTKit.dq hL, Kt.toTKit.dq hL, Kt.toTKit.dq hL] at hrep
  exact ⟨rep_of_represents hrep, bx, by', bz⟩

/-- `R = [k]Q` by the call of the curve's multiplication, for `k` at `K` and `Q` in `R`'s first two
slots. -/
theorem mulCall_ok (hL : Law Kt.c.C) {s : State} {base : Addr} (hw : WsReg s base) (h3 : s.gpr .s3 = base)
    (hc : TKit.Consts Kt.c base s) (hx : sv Kt.c base s RX < Kt.c.C.p) (hy : sv Kt.c base s RY < Kt.c.C.p)
    {P : Point Kt.c.C}
    (hP : Point.affine (toM Kt.c.C.p (2 ^ (64 * Kt.c.n)) (sv Kt.c base s RX))
      (toM Kt.c.C.p (2 ^ (64 * Kt.c.n)) (sv Kt.c base s RY)) = P)
    (hon : onCurve Kt.c.C P = true) :
    WP isa (Cfg.wsCall Kt.mulN Kt.mulC) s fun s' => Kp s s' ∧
      Kt.toTKit.MC.ResultInRange (sv Kt.c base s K) P base s.mem s'.mem := by
  refine wsCallR_ok Kt.mulNF (Kt.mul_rv hL) hw h3
    (fun t r w a m => ?_) fun s₂' s₂ K₂ mm₂ t a₂ m₂ hp₂ => ⟨K₂, ?_⟩
  · refine ⟨r, by rw [w, a], by rw [a]; exact hw.nowrap, by rw [a]; exact hw.al, ?_, ?_⟩
    · rw [a, m]
      exact ⟨(Kt.toTKit.coord_sv _ _ MP (by decide)).trans hc.mp, (Kt.toTKit.coord_sv _ _ ZERO (by decide)).trans hc.zero,
        (Kt.toTKit.coord_sv _ _ ONEP (by decide)).trans hc.onep, (Kt.toTKit.coord_sv _ _ AP (by decide)).trans hc.ap,
        (Kt.toTKit.coord_sv _ _ B3P (by decide)).trans hc.b3p⟩
    · rw [a, m]
      refine ⟨?_, ?_, ?_⟩
      · show Kt.toTKit.MC.toPoint.coordAt s.mem base (Kt.c.sl RX) < Kt.c.C.p
        rw [Kt.toTKit.coord_sv _ _ RX (by decide)]; exact hx
      · show Kt.toTKit.MC.toPoint.coordAt s.mem base (Kt.toTKit.MC.pAt + 8 * Kt.c.n) < Kt.c.C.p
        rw [Kt.toTKit.pAt_y, Kt.toTKit.coord_sv _ _ RY (by decide)]; exact hy
      rw [Kt.toTKit.point_eq hL]; exact hP ▸ hon
  · have := hp₂
    simp only [TKit.mulRVc, State.withRegions_mem] at this
    rw [a₂, m₂, ← mm₂] at this
    obtain hk : Kt.toTKit.MC.scalar base s.mem = sv Kt.c base s K := Kt.toTKit.coord_sv _ _ K (by decide)
    rw [hk, Kt.toTKit.point_eq hL] at this
    exact hP ▸ this

/-! ## `[u]G + [v]Q` -/

/-- What `joint` writes. -/
abbrev combW : List (Nat × Nat) :=
  [(Kt.c.sl K, 8 * Kt.c.n)] ++ [(Kt.c.sl RX, 8 * Kt.c.n)] ++ [(Kt.c.sl RY, 8 * Kt.c.n)] ++ TKit.mulKW Kt.c ++
    zW Kt.c ++ ([(Kt.c.sl GX, 8 * Kt.c.n)] ++ [(Kt.c.sl CPX, 8 * Kt.c.n)] ++ [(Kt.c.sl CPY, 8 * Kt.c.n)]) ++
    [(Kt.c.sl K, 8 * Kt.c.n)] ++ TKit.mulKW Kt.c ++ zW Kt.c ++ Kt.addW ++
    ([(Kt.c.sl RX, 8 * Kt.c.n)] ++ [(Kt.c.sl RY, 8 * Kt.c.n)] ++ [(Kt.c.sl RZ, 8 * Kt.c.n)])

/-- `R = [u]G + [v]Q`, for `u` and `v` in their slots and `Q` in the check's, with the comb's table. -/
theorem jointComb_ok (hL : Law Kt.c.C) {base : Addr} {s : State} {Q : Point Kt.c.C} (hw : WsReg s base)
    (h3 : s.gpr .s3 = base) (hc : TKit.Consts Kt.c base s) (hT : Kt.Tab base s) (hwr : s.wr = [⟨base, 8192⟩])
    (hqx : sv Kt.c base s CPX < Kt.c.C.p) (hqy : sv Kt.c base s CPY < Kt.c.C.p)
    (hq : Point.affine (toM Kt.c.C.p (2 ^ (64 * Kt.c.n)) (sv Kt.c base s CPX))
      (toM Kt.c.C.p (2 ^ (64 * Kt.c.n)) (sv Kt.c base s CPY)) = Q)
    (hon : onCurve Kt.c.C Q = true) (hu : sv Kt.c base s UU < Kt.c.C.n) (hv : sv Kt.c base s VV < Kt.c.C.n) :
    WP isa (VerifyComb.Cfg.joint Kt.c Kt.mulN Kt.mulC Kt.gN Kt.gC) s fun s' =>
      Kc s s' ∧ Unch base Kt.combW s.mem s'.mem ∧
      PtOk Kt.c base s' (Kt.c.pt RX RY RZ) (Spec.Weierstrass.add (mul (sv Kt.c base s UU) (Spec.Weierstrass.G Kt.c.C))
        (mul (sv Kt.c base s VV) Q)) := by
  obtain h9 := Kt.n9
  obtain top : ∀ {i : Nat}, i ≤ 55 → Kt.c.sl i + 8 * Kt.c.n ≤ 8192 := fun hi =>
    Nat.le_trans (sl_top h9 hi) (by decide)
  rw [VerifyComb.Cfg.joint]
  -- `K = v`, `Q` to `R`'s first two slots.
  obtain B1 : WP isa (.block (copy Kt.c.n (Kt.c.sl K) (Kt.c.sl VV) ++ copy Kt.c.n (Kt.c.sl RX) (Kt.c.sl CPX) ++
      copy Kt.c.n (Kt.c.sl RY) (Kt.c.sl CPY))) s fun s₁ =>
      sv Kt.c base s₁ K = sv Kt.c base s VV ∧ sv Kt.c base s₁ RX = sv Kt.c base s CPX ∧
      sv Kt.c base s₁ RY = sv Kt.c base s CPY ∧ Rest [.t0] s s₁ ∧
      Unch base ([(Kt.c.sl K, 8 * Kt.c.n)] ++ [(Kt.c.sl RX, 8 * Kt.c.n)] ++ [(Kt.c.sl RY, 8 * Kt.c.n)])
        s.mem s₁.mem := by
    rw [List.append_assoc]
    refine WP.block_append (WP.mono (copySl_ok Kt.c h9 hw (o := K) (a := VV) (by decide) (by decide) (by decide))
      fun t₁ ⟨k₁, r₁, U₁⟩ => ?_)
    refine WP.block_append (WP.mono (copySl_ok Kt.c h9 (hw.of_rest r₁) (o := RX) (a := CPX) (by decide) (by decide)
      (by decide)) fun t₂ ⟨x₂, r₂, U₂⟩ => ?_)
    refine WP.mono (copySl_ok Kt.c h9 ((hw.of_rest r₁).of_rest r₂) (o := RY) (a := CPY) (by decide) (by decide)
      (by decide)) fun t₃ ⟨y₃, r₃, U₃⟩ => ⟨?_, ?_, ?_, r₁.trans (r₂.trans r₃), (U₁.trans U₂).trans U₃⟩
    · exact (sv_unch h9 (U₂.trans U₃) K (by apart)).trans k₁
    · exact ((sv_unch h9 U₃ RX (by apart)).trans x₂).trans (sv_unch h9 U₁ CPX (by apart))
    · exact y₃.trans (sv_unch h9 (U₁.trans U₂) CPY (by apart))
  refine WP.seq (WP.mono (Kt.tab_frame rfl hT hwr B1) fun s₁ ⟨⟨k₁, x₁, y₁, r₁, U₁⟩, T₁⟩ => ?_)
  obtain hw₁ := hw.of_rest r₁
  obtain hwr₁ : s₁.wr = [⟨base, 8192⟩] := r₁.wr.trans hwr
  obtain hc₁ := hc.of_unch h9 U₁ fun i hi => by apart_cst hi
  obtain eQ : Point.affine (toM Kt.c.C.p (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₁ RX))
      (toM Kt.c.C.p (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₁ RY)) = Q := by
    rw [x₁, y₁]; exact hq
  -- `[v]Q`.
  refine WP.seq (WP.mono (Kt.tab_frame (wsCall_noFrames Kt.mulNF) T₁ hwr₁
    (Kt.mulCall_ok hL hw₁ ((r₁.gpr .s3 (by decide)).trans h3) hc₁ (by rw [x₁]; exact hqx) (by rw [y₁]; exact hqy)
      eQ hon)) fun s₂ ⟨⟨K₂, R₂⟩, T₂⟩ => ?_)
  rw [k₁] at R₂
  obtain U₂ : Unch base (TKit.mulKW Kt.c) s₁.mem s₂.mem := Kt.toTKit.unch_of_mulKeeps R₂.2
  obtain hw₂ := hw₁.of_kp K₂
  obtain hc₂ := hc₁.of_unch h9 U₂ fun i hi => cst_mulKW _ hi
  obtain v₂ : sv Kt.c base s₂ VV = sv Kt.c base s VV :=
    (sv_unch h9 U₂ VV (by apart)).trans (sv_unch h9 U₁ VV (by apart))
  -- `O` if `v = 0`, `P = R`, `K = u`.
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append (wp_syms (Kt.zeroR_ok hL hw₂ hc₂.zero hc₂.onep (a := VV) (.inr rfl)
    (P := mul (sv Kt.c base s VV) Q)
    (fun h0 => Kt.ptOk_of_result hL R₂ (by rw [v₂] at h0; omega_using [h0]) hv))
    fun s₃ ⟨r₃, U₃, pR₃, bp₃⟩ sy₃ => ?_))
  rw [v₂] at pR₃
  obtain pR₃' : PtOk Kt.c base s₃ (Kt.c.pt RX RY RZ) (mul (sv Kt.c base s VV) Q) := by
    by_cases h0 : sv Kt.c base s VV = 0
    · rw [ite_eq_left h0] at pR₃; rw [h0, mul_zero']; exact pR₃
    · rw [ite_eq_right h0] at pR₃; exact pR₃
  obtain hw₃ := hw₂.of_rest r₃
  rw [WindowA.Cfg.copyPt, List.append_assoc, List.append_assoc]
  refine WP.block_append (wp_syms (copySl_ok Kt.c h9 hw₃ (o := GX) (a := RX) (by decide) (by decide) (by decide))
    fun t₁ ⟨cx, q₁, V₁⟩ sy₄a => ?_)
  refine WP.block_append (wp_syms (copySl_ok Kt.c h9 (hw₃.of_rest q₁) (o := CPX) (a := RY) (by decide) (by decide)
    (by decide)) fun t₂ ⟨cy, q₂, V₂⟩ sy₄b => ?_)
  refine WP.block_append (wp_syms (copySl_ok Kt.c h9 ((hw₃.of_rest q₁).of_rest q₂) (o := CPY) (a := RZ) (by decide)
    (by decide) (by decide)) fun s₄ ⟨cz, q₃, V₃⟩ sy₄c => ?_)
  obtain r₄ : Rest [.t0] s₃ s₄ := q₁.trans (q₂.trans q₃)
  obtain U₄ : Unch base ([(Kt.c.sl GX, 8 * Kt.c.n)] ++ [(Kt.c.sl CPX, 8 * Kt.c.n)] ++ [(Kt.c.sl CPY, 8 * Kt.c.n)])
      s₃.mem s₄.mem := (V₁.trans V₂).trans V₃
  obtain ex₄ : sv Kt.c base s₄ GX = sv Kt.c base s₃ RX := (sv_unch h9 (V₂.trans V₃) GX (by apart)).trans cx
  obtain ey₄ : sv Kt.c base s₄ CPX = sv Kt.c base s₃ RY :=
    ((sv_unch h9 V₃ CPX (by apart)).trans cy).trans (sv_unch h9 V₁ RY (by apart))
  obtain ez₄ : sv Kt.c base s₄ CPY = sv Kt.c base s₃ RZ := cz.trans (sv_unch h9 (V₁.trans V₂) RZ (by apart))
  obtain pP₄ : PtOk Kt.c base s₄ (Kt.c.pt GX CPX CPY) (mul (sv Kt.c base s VV) Q) := pR₃'.move ex₄ ey₄ ez₄
  obtain hw₄ := hw₃.of_rest r₄
  refine wp_syms (copySl_ok Kt.c h9 hw₄ (o := K) (a := UU) (by decide) (by decide) (by decide))
    fun s₅ ⟨k₅, r₅, U₅⟩ sy₅ => ?_
  obtain hw₅ := hw₄.of_rest r₅
  obtain sy₂₅ : s₅.syms = s₂.syms := by rw [sy₅, sy₄c, sy₄b, sy₄a, sy₃]
  obtain rd₂₅ : s₅.rd = s₂.rd := by rw [r₅.rd, r₄.rd, r₃.rd]
  obtain U₃₅ := (U₃.trans U₄).trans U₅
  obtain T₅ : Kt.Tab base s₅ := Kt.tab_unch T₂ sy₂₅ rd₂₅
    (by ranges first | exact top (by decide) | exact zW_top h9) U₃₅
  obtain hc₅ := hc₂.of_unch h9 U₃₅ fun i hi => by apart_cst hi
  obtain uU : sv Kt.c base s₄ UU = sv Kt.c base s UU :=
    sv_unch h9 ((U₁.trans U₂).trans (U₃.trans U₄)) UU (by apart)
  obtain u₅ : sv Kt.c base s₅ K = sv Kt.c base s UU := k₅.trans uU
  obtain h3₅ : s₅.gpr .s3 = base := by
    rw [r₅.gpr .s3 (by decide), r₄.gpr .s3 (by decide), r₃.gpr .s3 (by decide), K₂.gpr _ (by decide),
      r₁.gpr .s3 (by decide), h3]
  obtain bp₅ : sv Kt.c base s₅ BP = Kt.c.C.b * 2 ^ (64 * Kt.c.n) % Kt.c.C.p :=
    (sv_unch h9 (U₄.trans U₅) BP (by apart)).trans bp₃
  -- `[u]G`.
  refine WP.seq (WP.mono (Kt.comb_ok hL hw₅ h3₅ hc₅ bp₅ T₅) fun s₆ ⟨K₆, R₆⟩ => ?_)
  rw [u₅] at R₆
  obtain U₆ : Unch base (TKit.mulKW Kt.c) s₅.mem s₆.mem := Kt.toTKit.unch_of_mulKeeps R₆.2
  obtain hw₆ := hw₅.of_kp K₆
  obtain hc₆ := hc₅.of_unch h9 U₆ fun i hi => cst_mulKW _ hi
  obtain u₆ : sv Kt.c base s₆ UU = sv Kt.c base s UU := (sv_unch h9 (U₅.trans U₆) UU (by apart)).trans uU
  -- `O` if `u = 0`.
  refine WP.seq (WP.mono (Kt.zeroR_ok hL hw₆ hc₆.zero hc₆.onep (a := UU) (.inl rfl)
    (P := mul (sv Kt.c base s UU) (Spec.Weierstrass.G Kt.c.C))
    (fun h0 => Kt.ptOk_of_result hL R₆ (by rw [u₆] at h0; omega_using [h0]) hu))
    fun s₇ ⟨r₇, U₇, pR₇, bp₇⟩ => ?_)
  rw [u₆] at pR₇
  obtain pR₇' : PtOk Kt.c base s₇ (Kt.c.pt RX RY RZ) (mul (sv Kt.c base s UU) (Spec.Weierstrass.G Kt.c.C)) := by
    by_cases h0 : sv Kt.c base s UU = 0
    · rw [ite_eq_left h0] at pR₇; rw [h0, mul_zero']; exact pR₇
    · rw [ite_eq_right h0] at pR₇; exact pR₇
  obtain hw₇ := hw₆.of_rest r₇
  obtain U₅₇ := (U₅.trans U₆).trans U₇
  obtain pP₇ : PtOk Kt.c base s₇ (Kt.c.pt GX CPX CPY) (mul (sv Kt.c base s VV) Q) :=
    pP₄.of_eq (sv_unch h9 U₅₇ GX (by apart)) (sv_unch h9 U₅₇ CPX (by apart)) (sv_unch h9 U₅₇ CPY (by apart))
  obtain hc₇ := hc₆.of_unch h9 U₇ fun i hi => cst_zW _ hi
  -- `T = R + P`.
  refine WP.seq (WP.mono (Kt.add_ok hL hw₇ hc₇ bp₇ (hL.onCurve_mul Kt.onG _) (hL.onCurve_mul hon _) pR₇' pP₇)
    fun s₈ ⟨K₈, U₈, pT₈⟩ => ?_)
  obtain hw₈ := hw₇.of_kp K₈
  -- `R = T`.
  rw [WindowA.Cfg.copyPt, List.append_assoc]
  refine WP.block_append (WP.mono (copySl_ok Kt.c h9 hw₈ (o := RX) (a := TX) (by decide) (by decide) (by decide))
    fun t₁ ⟨cx, q₁, V₁⟩ => ?_)
  refine WP.block_append (WP.mono (copySl_ok Kt.c h9 (hw₈.of_rest q₁) (o := RY) (a := TY) (by decide) (by decide)
    (by decide)) fun t₂ ⟨cy, q₂, V₂⟩ => ?_)
  refine WP.mono (copySl_ok Kt.c h9 ((hw₈.of_rest q₁).of_rest q₂) (o := RZ) (a := TZ) (by decide) (by decide)
    (by decide)) fun s₉ ⟨cz, q₃, V₃⟩ => ?_
  obtain r₉ : Rest [.t0] s₈ s₉ := q₁.trans (q₂.trans q₃)
  obtain U₉ := (V₁.trans V₂).trans V₃
  obtain ex₉ : sv Kt.c base s₉ RX = sv Kt.c base s₈ TX := (sv_unch h9 (V₂.trans V₃) RX (by apart)).trans cx
  obtain ey₉ : sv Kt.c base s₉ RY = sv Kt.c base s₈ TY :=
    ((sv_unch h9 V₃ RY (by apart)).trans cy).trans (sv_unch h9 V₁ TY (by apart))
  obtain ez₉ : sv Kt.c base s₉ RZ = sv Kt.c base s₈ TZ := cz.trans (sv_unch h9 (V₁.trans V₂) TZ (by apart))
  refine ⟨?_, ?_, pT₈.move ex₉ ey₉ ez₉⟩
  · exact (Kc.of_rest r₁).trans (K₂.kc.trans ((Kc.of_rest r₃).trans ((Kc.of_rest r₄).trans ((Kc.of_rest r₅).trans
      (K₆.kc.trans ((Kc.of_rest r₇).trans (K₈.kc.trans (Kc.of_rest r₉))))))))
  · exact (((((((U₁.trans U₂).trans U₃).trans U₄).trans U₅).trans U₆).trans U₇).trans U₈).trans U₉

end Kit

end VG.Proof.Ecdsa.RISCV64.JointCombAll
