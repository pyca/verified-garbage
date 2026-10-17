module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Points
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Window
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Prep
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.PubNaf
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-!
# `[v]Q` by the public NAF, in the verifier's slots

The window method's slots (`winQ`) suit the public NAF too for a modulus of
other than four words (`nafLayQ`): its digits go where the window method's
bits are, its eight odd multiples where its table is. `pubNafMul_ok` recodes
`v` and multiplies `Q` by it, leaving `R` representing `[v]Q`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (V)

variable {c : Cfg}

theorem nafLayQ (hc : CfgOk c) (hn4 : c.n ≠ 4) (hn6 : c.n ≤ 6) :
    PubNaf.NafLay (winQ c) size where
  win := winLayQ hc
  al := winAQ hc
  n4 := hn4
  n6 := hn6
  digits := by show 64 * c.n + 1 ≤ 4 * (16 * c.n + 1); omega
  rxy := by
    show c.sl RY = c.sl RX + 8 * c.n
    simp (disch := decide) only [sl_eq]; unfold RX RY; omega
  rxz := by
    show c.sl RZ = c.sl RX + 16 * c.n
    simp (disch := decide) only [sl_eq]; unfold RX RZ; omega
  exy := by
    show c.sl TY = c.sl TX + 8 * c.n
    simp (disch := decide) only [sl_eq]; unfold TX TY; omega
  exz := by
    show c.sl TZ = c.sl TX + 16 * c.n
    simp (disch := decide) only [sl_eq]; unfold TX TZ; omega

/-- The window method's bits, where the digits go, are below its table. -/
theorem winBits_le (c : Cfg) (h0 : 0 < c.n) : c.sl WB + 64 * (c.n + 1) ≤ c.sl WT := by
  simp (disch := decide) only [sl_eq]; unfold WB WT
  have : 8 * c.n * 87 = 8 * c.n * 55 + 256 * c.n := by omega_arith
  omega_arith

/-- What the recoding and the multiplication leave: `R` represents `[k]P`. -/
structure NafMulPost (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (winX c ++ slW c (otherI ++ tblI ++ [TMP])) s.mem s'.mem
  mod : ModOkA c.MP' size c.C.p s'.mem base
  lt : ∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p
  q : Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
    (tmv c.C c.n base s' (c.sl RZ)) (mul k P)

/-- The digits of `v`, and what the multiplication needs of the slots it reads. -/
theorem pubNafPrep_ok (hc : CfgOk c) (hn6 : c.n ≤ 6) (hC : Law c.C) {base : Addr} {s : State}
    (hs : Scr s base size) {g : Reg → BitVec 64} (F : Fixed c base g s.mem) {P : Point c.C}
    (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P) :
    WP isa (PubNaf.prep (winQ c) (c.sl V)) s fun t =>
      Scr t base size ∧ ModOkA c.MP' size c.C.p t.mem base ∧
      PubNaf.NafFixed (winQ c) c.C base t P (sv c base s V) ∧
      (∀ x ∈ winRo (winQ c), tmv c.C c.n base t x = tmv c.C c.n base s x) ∧
      t.sp = s.sp ∧ Unch base (winX c) s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Fixed c base g t.mem := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  have hB : (winQ c).bits = c.sl WB := rfl
  have hBs := winBits_le c hc.n0
  have hTs := sl_le' c h7 (i := WT) (by decide)
  have hb4 := (winAQ hc).bits4
  refine WP.mono (PubNaf.prep_ok (winQ c) (PubNaf.regs_ok c.n h0 hn6) hs
    (sl_le c h7 (i := V) (by decide)) (sl_mod8 c _) (by omega_arith)
    (by show c.sl WB + (64 * c.n + 1) ≤ size; omega_arith)) fun s₂ ⟨p₂, k₂, O₂⟩ => ?_
  have hs₂ := p₂.scr
  have U₂ : Unch base (winX c) s.mem s₂.mem := by
    have u := (O₂.mono (o' := c.sl WB) (n' := 64 * (c.n + 1)) (by rw [hB]) (by
      show c.sl WB + (64 * c.n + 1) ≤ c.sl WB + 64 * (c.n + 1); omega_arith)).unch
    exact u.mono (by
      intro w hw; simp only [List.mem_singleton] at hw; subst hw
      change _ ∈ [(c.winK, 16 * c.n), (c.winBits, 64 * (c.n + 1))]
      exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))
  have F₂ := F.unch h7 hn fixedOk_winX U₂
  have e₂ : ∀ {i}, i < 45 → i ≠ TMP → sv c base s₂ i = sv c base s i := fun hi hT =>
    sv_unch U₂ h7 hn hi (apart_winX hi hT)
  have tv : ∀ {i}, i < 45 → i ≠ TMP → tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun hi hT => by
      show toM _ _ (sv c base s₂ _) = toM _ _ (sv c base s _); rw [e₂ hi hT]
  have hlt : ∀ x ∈ winRo (winQ c), wordsVal s₂.mem base x c.n < c.C.p := by
    intro x hx
    simp only [winRo, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F₂.ap (hmont _)
    · exact lt_of_eq_of_lt F₂.bm (hmont _)
    · exact lt_of_eq_of_lt F₂.zero (by omega_arith)
    · exact lt_of_eq_of_lt (e₂ (i := PX) (by decide) (by decide)) hpx
    · exact lt_of_eq_of_lt (e₂ (i := PY) (by decide) (by decide)) hpy
    · exact lt_of_eq_of_lt F₂.onep (Nat.mod_lt _ (by omega_arith))
  have one : tmv c.C c.n base s₂ (c.sl ONEP) = 1 := by
    change toM _ _ (wordsVal s₂.mem base (c.sl ONEP) c.n) = 1
    rw [F₂.onep]
    have hm1 := toM_cmont hc.toBaseCfgOk 1
    have ho : Fin.ofNat c.C.p 1 = (1 : Fe c.C) := by rfl
    simpa only [Cfg.mont, Cfg.R, Nat.one_mul, ho] using hm1
  have hp : Rep c.C (tmv c.C c.n base s₂ (c.sl PX)) (tmv c.C c.n base s₂ (c.sl PY))
      (tmv c.C c.n base s₂ (c.sl ONEP)) P := by
    rw [tv (by decide) (by decide), tv (by decide) (by decide), tv (by decide) (by decide)]; exact hrep
  have hj : InvJ c.C (tmv c.C c.n base s₂ (c.sl PX)) (tmv c.C c.n base s₂ (c.sl PY))
      (tmv c.C c.n base s₂ (c.sl ONEP)) P := by
    have hh := InvJ.of_rep hC hp
    simpa only [one, Lean.Grind.Semiring.mul_one] using hh
  refine ⟨hs₂, modP_of hc F₂.mp, ⟨hlt, F₂.zero, hj, fun i hi => p₂.digits i hi⟩, ?_, k₂.sp, U₂,
    k₂.rd, k₂.wr, F₂⟩
  intro x hx
  simp only [winRo, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [tv (i := AP) (by decide) (by decide), tv (i := BM) (by decide) (by decide),
    tv (i := ZERO) (by decide) (by decide), tv (i := PX) (by decide) (by decide),
    tv (i := PY) (by decide) (by decide), tv (i := ONEP) (by decide) (by decide)]

/-- `[v]Q` by the public NAF, into `R`. -/
theorem pubNafMul_ok (hc : CfgOk c) (hn4 : c.n ≠ 4) (hn6 : c.n ≤ 6) (hC : Law c.C) {base : Addr}
    {s : State} (hs : Scr s base size) {g : Reg → BitVec 64} (F : Fixed c base g s.mem)
    {P : Point c.C} (hP : onCurve c.C P = true)
    (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P)
    {rest : Prog isa} {R : State → Prop}
    (h : ∀ s', NafMulPost c base P (sv c base s V) s s' → WP isa rest s' R) :
    WP isa (.seq (PubNaf.prep (winQ c) (c.sl V)) (.seq (PubNaf.window (winQ c)) rest)) s R := by
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by have := hc.p_ge; omega_arith)
  have hk : sv c base s V < 2 ^ (64 * c.n) := wordsVal_lt _ _ _ _
  apply WP.seq
  refine WP.mono (pubNafPrep_ok hc hn6 hC hs F hpx hpy hrep)
    fun s₂ ⟨hs₂, hM₂, hF₂, _, _, U₂, rd₂, wr₂, _⟩ => ?_
  refine WP.seq (WP.mono (PubNaf.window_ok (nafLayQ hc hn4 hn6) (unitMod_pow_two hc.p_odd (64 * c.n))
    hC hc.am3 hc.p_lt (hmont 1)
    (show toM c.C.p (2 ^ (64 * c.n)) (c.mont 1) = 1 by rw [toM_cmont hc]; rfl) hP hs₂ hM₂ hF₂ hk)
    fun s₃ ⟨S₃, L₃, R₃⟩ => h s₃ ?_)
  have U₃ := S₃.unch
  rw [winW_eq] at U₃
  exact ⟨S₃.scr, S₃.keep.rd.trans rd₂, S₃.keep.wr.trans wr₂, U₂.trans U₃, S₃.mod, L₃, R₃⟩

end VG.Proof.Ecdsa.Verify.AArch64
