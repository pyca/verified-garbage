module

public import VerifiedGarbage.Impl.Ecdsa.Arm
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
public import VerifiedGarbage.Proof.Ecdsa.Arm.Fixed
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.Arm.Ladder
public import VerifiedGarbage.Proof.Weierstrass.JacMul
public import VerifiedGarbage.Proof.Weierstrass.CombW
import VerifiedGarbage.Proof.Ecdsa.Arm.Lays
import VerifiedGarbage.Proof.Ecdsa.Arm.Flags
import VerifiedGarbage.Proof.Weierstrass.Arm.Window
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombCorrect
import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
import VerifiedGarbage.Proof.Weierstrass.Arm.Copy
import VerifiedGarbage.Proof.Weierstrass.Arm.Loop
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Weierstrass.JacDbl0
import VerifiedGarbage.Proof.Weierstrass.JacDblA
import VerifiedGarbage.Proof.Weierstrass.JacAdd
import VerifiedGarbage.Proof.Weierstrass.CombDigitTopW
import VerifiedGarbage.Proof.Weierstrass.Comb
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# `[k]Q` by windows on 32-bit ARM: correctness

`Cfg.mulBody` (`Impl/Ecdsa/Arm.lean`) leaves in `R` a representative of
`[k]Q`, for the affine point `Q` of the curve in `R`'s first two slots and
the number `k < 2^(8 len)` at `K`'s slot (`mulBody_ok`), for any curve the
code supports (`CfgOk`) whose group law the proofs support (`Law`):

* the points: `w` doublings of `[m]Q` are `[2^w m]Q` (`dblPt_mul`), and a
  window takes `[k / 2^(w (j + 1))]Q` to `[k / 2^(w j)]Q` (`win_pt`);
* a field program of numbered operations on the slots of points (`ptOp_ok`,
  from `fprog_ok`), which the complete addition, the Jacobian doublings
  (`WinDblOk`: for the curve's `a`, `winDbl_ok`) and the changes of
  coordinates all are;
* `winQuad_ok`: `R = 2^w R`, the point at infinity as `(0 : 1 : 0)`;
* `winDigit_ok`: the window, by the comb's code; `winEntry_ok`: its entry of
  the table, into `T`;
* `winBuild_ok`: the table holds `[e]Q` for every `e < 2^w` (`TblOk`).

Everything the code keeps (the constants, the table of the scalar's bits) is
apart from what it writes (`WinW`, `WinCtx.next`).
-/

-- separate module: the windows' proofs cost more than their imports, and changes to the stages of
-- `Main.lean` need not check them again

@[expose] public section

namespace VG.Proof.Ecdsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.X25519.Arm (Rest Upd wp_mov wp_dp wp_cmp op2_imm op2_reg dpVal)

variable {c : Cfg}

/-! ## The points -/

section
variable {C : Curve}

theorem mul_zero_pt (P : Point C) : Spec.Weierstrass.mul 0 P = .infinity := by
  rw [Spec.Weierstrass.mul]; simp

/-- `2^k Q`, by `k` doublings. -/
def dblPt (Q : Point C) : Nat → Point C
  | 0 => Q
  | k + 1 => dblPt (Spec.Weierstrass.add Q Q) k

theorem onCurve_dblPt (hC : Law C) : ∀ (k : Nat) {Q : Point C}, onCurve C Q = true → onCurve C (dblPt Q k) = true
  | 0, _, h => h
  | k + 1, _, h => onCurve_dblPt hC k (hC.onCurve_add h h)

theorem dblPt_mul (hC : Law C) {P : Point C} (hP : onCurve C P = true) :
    ∀ k m, dblPt (mul m P) k = mul (2 ^ k * m) P
  | 0, m => by rw [dblPt, Nat.pow_zero, Nat.one_mul]
  | k + 1, m => by
    rw [dblPt, hC.add_mul_mul hP, dblPt_mul hC hP k, Nat.pow_succ, ← Nat.two_mul, Nat.mul_assoc]

/-- A window: `2^w [k / 2^(w (j + 1))]P + [k_j]P = [k / 2^(w j)]P`. -/
theorem win_pt (hC : Law C) {P : Point C} (hP : onCurve C P = true) (w k j : Nat) :
    Spec.Weierstrass.add (dblPt (mul (k / 2 ^ (w * (j + 1))) P) w) (mul (combWin w k j) P) =
      mul (k / 2 ^ (w * j)) P := by
  rw [dblPt_mul hC hP, hC.add_mul_mul hP, combWin, Nat.mul_succ, Nat.pow_add, ← Nat.div_div_eq_div_mul,
    Nat.div_add_mod]

/-- `[e + 1]P = [e]P + P`. -/
theorem mul_succ_pt (hC : Law C) {P : Point C} (hP : onCurve C P = true) (e : Nat) :
    Spec.Weierstrass.add (mul e P) P = mul (e + 1) P := by
  have := hC.add_mul_mul hP e 1
  rwa [mul_one_pt] at this

/-- `a + 3 = p`: the curve's `a` is `-3`. -/
theorem am3_of_add (h : C.a + 3 = C.p) : AM3 C := by
  have e : (Fin.ofNat C.p C.a : Fe C) + Fin.ofNat C.p 3 = Fin.ofNat C.p 0 := by
    rw [← ofNat_add', ofNat_eq_ofNat, h, Nat.mod_self, Nat.zero_mod]
  have e3 : (Fin.ofNat C.p 3 : Fe C) = 3 := rfl
  have e0 : (Fin.ofNat C.p 0 : Fe C) = 0 := rfl
  rw [e3, e0] at e
  unfold AM3
  grind

/-- `dbl` doubles a Jacobian point of `C`: the same numbered field operations
`N` (`ofN`) wherever it runs, which, from a Jacobian triple of a point of `C`
in `p` (`11`–`13`) and the curve's `a` in the slot of `a` (`9`), leave one of
its double in `o` (`6`–`8`). -/
def WinDblOk (C : Curve) (dbl : RcbSlots → Pt → Pt → List FOp) : Prop :=
  ∃ N : List FOp, NumOk N ∧ (∀ S p o, dbl S p o = ofN N S p p o) ∧
    ∀ (e : Nat → Fe C) {Q : Point C}, onCurve C Q = true → e 9 = Fin.ofNat C.p C.a →
      InvJ C (e 11) (e 12) (e 13) Q →
      InvJ C (runOps N e 6) (runOps N e 7) (runOps N e 8) (Spec.Weierstrass.add Q Q)

/-- `add` adds two points of `C`: the same numbered field operations `N`
(`ofN`) wherever it runs, which, from representatives of two points of `C` in
`p` (`11`–`13`) and `q` (`14`–`16`), `q`'s `Z` being one if `affine`, and the
curve's `a` and `3b` in their slots (`9`, `10`), leave one of the points' sum
in `o` (`6`–`8`). -/
def WinAddOk (C : Curve) (affine : Bool) (add : RcbSlots → Pt → Pt → Pt → List FOp) : Prop :=
  ∃ N : List FOp, NumOk N ∧ (∀ S p q o, add S p q o = ofN N S p q o) ∧
    ∀ (e : Nat → Fe C) {P Q : Point C}, onCurve C P = true → onCurve C Q = true →
      e 9 = Fin.ofNat C.p C.a → e 10 = Fin.ofNat C.p (3 * C.b) → (affine = true → e 16 = 1) →
      Rep C (e 11) (e 12) (e 13) P → Rep C (e 14) (e 15) (e 16) Q →
      Rep C (runOps N e 6) (runOps N e 7) (runOps N e 8) (Spec.Weierstrass.add P Q)

theorem rcb_ofN (S : RcbSlots) (p q o : Pt) : rcb S p q o = ofN rcbN S p q o := rfl

/-- Algorithm 1 adds, whatever the second point's `Z`. -/
theorem winAddOk_rcb (hC : Law C) (affine : Bool) : WinAddOk C affine rcb :=
  ⟨rcbN, rcbN_ok, rcb_ofN, fun e _ _ hP hQ ha hb _ h1 h2 => hC.add hP hQ h1 h2 (by
    show rcbAdd (Fin.ofNat C.p C.a) (Fin.ofNat C.p (3 * C.b)) _ _ _ _ _ _ = _
    rw [← ha, ← hb]; exact (rcbN_run e).symm)⟩

end

/-- The windows' complete addition adds. -/
theorem winAdd_ok (hC : Law c.C) : WinAddOk c.C false c.winAdd := by
  unfold Cfg.winAdd
  split
  · have ha : (Fin.ofNat c.C.p c.C.a : Fe c.C) = 0 := by rw [‹c.C.a = 0›]; rfl
    exact ⟨rcb0N, rcb0N_ok, rcb0_eq, fun e _ _ hP hQ _ hb _ h1 h2 => hC.add hP hQ h1 h2 (by
      show rcbAdd (Fin.ofNat c.C.p c.C.a) (Fin.ofNat c.C.p (3 * c.C.b)) _ _ _ _ _ _ = _
      rw [ha, ← hb, ← rcbAdd0_eq]; exact (rcb0N_run e).symm)⟩
  · exact winAddOk_rcb hC false

/-- The table's complete addition adds an affine point. -/
theorem winAddM_ok (hC : Law c.C) : WinAddOk c.C true c.winAddM := by
  unfold Cfg.winAddM
  split
  · have ha : (Fin.ofNat c.C.p c.C.a : Fe c.C) = 0 := by rw [‹c.C.a = 0›]; rfl
    refine ⟨rcb0mN, rcb0mN_ok, rcb0m_eq, fun e _ Q hP hQ _ hb hz h1 h2 => ?_⟩
    have h2' : Rep c.C (e 14) (e 15) 1 Q := by rw [← hz rfl]; exact h2
    refine hC.add hP hQ h1 h2' ?_
    show rcbAdd (Fin.ofNat c.C.p c.C.a) (Fin.ofNat c.C.p (3 * c.C.b)) _ _ _ _ _ _ = _
    rw [ha, ← hb, ← rcbAdd0m_eq]; exact (rcb0mN_run e).symm
  · exact winAddOk_rcb hC true

/-- The curve's Jacobian doubling doubles. -/
theorem winDbl_ok (hC : Law c.C) : WinDblOk c.C c.winDbl := by
  unfold Cfg.winDbl
  split
  · obtain ⟨N, hN, he, h⟩ := jdblOk_dblJMul hC (am3_of_add ‹_›)
    exact ⟨N, hN, he, fun e _ hQ _ hJ => h e hQ hJ⟩
  · split
    · obtain ⟨N, hN, he, h⟩ := jdblOk_dblJ0 hC (show A0 c.C by unfold A0; rw [‹c.C.a = 0›]; rfl)
      exact ⟨N, hN, he, fun e _ hQ _ hJ => h e hQ hJ⟩
    · exact ⟨dblJaN, dblJaN_ok, dblJa_eq, fun e _ hQ ha hJ => InvJ.dblA' hC hQ hJ ha (dblJaN_run e)⟩

/-! ## The slots -/

/-- The numbered slots the windows' field programs use. -/
def winIds : List Nat := [AP, B3P, ZERO, ONEP, RX, RY, RZ, DX, DY, DZ, TX, TY, TZ, T0, T1, T2, T3, T4, T5]

/-- A slot of the windows' field programs. -/
abbrev winSl (c : Cfg) (x : Nat) : Prop := x ∈ winIds.map c.sl

theorem winLay (hc : CfgOk c) : Lay c.MP' size (winSl c) := lay_map hc rfl rfl rfl (by decide)

theorem winWk (hc : CfgOk c) : WkOk c.MP' size c.wk (winSl c) :=
  ⟨wk_le c hc.n10 rfl, fun x hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact sl_below_wk c hc.n10 ((by decide : ∀ i ∈ winIds, i < 45) i hi),
    sl_below_wk c hc.n10 (i := MP) (by decide), sl_below_wk c hc.n10 (i := TMP) (by decide)⟩

/-- What the slot `i` stands for. -/
abbrev fv (c : Cfg) (base : Addr) (s : State) (i : Nat) : Fe c.C := tmv c.C c.n base s (c.sl i)

theorem toM_cmont (hc : CfgOk c) (x : Nat) : toM c.C.p (2 ^ (64 * c.n)) (c.mont x) = Fin.ofNat c.C.p x :=
  toM_mont (unitMod_pow_two hc.p_odd _)

/-- The ranges of the numbered slots `l` and of the field arithmetic's own
working space: what a field program writing `l` may change. -/
abbrev pW (c : Cfg) (l : List Nat) : List (Nat × Nat) := slW c l ++ [(c.wk, 64 * c.n)]

/-- Where coordinate `j` of entry `e` of the table is. -/
abbrev tblAt (c : Cfg) (e j : Nat) : Nat := c.winTbl + 4 * (6 * c.n) * e + 8 * c.n * j

/-! ### What the windows write, and what they keep -/

/-- A range the windows' code writes: the temporary slot, within the slots
from 12 and the field arithmetic's own working space, or in the table. -/
def WinW (c : Cfg) (W : List (Nat × Nat)) : Prop :=
  ∀ w ∈ W, (w.1 = c.sl TMP ∧ w.2 = 8 * c.n) ∨ (c.sl 12 ≤ w.1 ∧ w.1 + w.2 ≤ size) ∨ c.winTbl ≤ w.1

theorem WinW.append {W W' : List (Nat × Nat)} (h : WinW c W) (h' : WinW c W') : WinW c (W ++ W') :=
  fun w hw => (List.mem_append.mp hw).elim (h w) (h' w)

theorem winW_slW (h7 : c.n < 10) {l : List Nat} (hl : ∀ i ∈ l, i = TMP ∨ (12 ≤ i ∧ i < 45)) :
    WinW c (slW c l) := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  rcases hl i hi with h | ⟨h, h'⟩
  · exact Or.inl ⟨by rw [h], rfl⟩
  · refine Or.inr (Or.inl ⟨?_, sl_le c h7 h'⟩)
    rcases Nat.eq_or_lt_of_le h with h | h
    · rw [h]
    · exact Nat.le_trans (Nat.le_add_right _ _) (sl_lt c h)

theorem winW_pW (h7 : c.n < 10) {l : List Nat} (hl : ∀ i ∈ l, i = TMP ∨ (12 ≤ i ∧ i < 45)) :
    WinW c (pW c l) := by
  refine (winW_slW h7 hl).append fun w hw => ?_
  rw [List.mem_singleton.mp hw]
  exact Or.inr (Or.inl ⟨Nat.le_trans (Nat.le_add_right _ _) (sl_below_wk c h7 (i := 12) (by decide)),
    wk_le c h7 (M := c.MP') rfl⟩)

theorem winW_tbl {o n : Nat} (h : c.winTbl ≤ o) : WinW c [(o, n)] := fun w hw => by
  rw [List.mem_singleton.mp hw]; exact Or.inr (Or.inr h)

/-- A numbered slot below 12 other than the temporary one is apart from what
the windows write. -/
theorem WinW.apart_const {W : List (Nat × Nat)} (hW : WinW c W) (h7 : c.n < 10) {i : Nat} (hi : i < 12)
    (hit : i ≠ TMP) : ∀ w ∈ W, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  rcases hW w hw with ⟨h1, h2⟩ | ⟨h, -⟩ | h
  · rw [h1, h2]; exact sl_apart c hit
  · exact Or.inl (Nat.le_trans (sl_lt c hi) h)
  · have := sl_le c h7 (i := i) (by omega_using [hi])
    have hsz : size = 4096 := rfl
    rw [Cfg.winTbl, bitsAt_eq] at h
    exact Or.inl (by omega_using [h, this, hsz])

/-- A byte of table 0 is apart from what the windows write. -/
theorem WinW.apart_bits {W : List (Nat × Nat)} (hW : WinW c W) (h7 : c.n < 10) {t : Nat} (ht : t < 64 * c.n) :
    ∀ w ∈ W, bitsAt c.n 0 + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n 0 + t := by
  intro w hw
  have hsz : size = 4096 := rfl
  rw [bitsAt_eq]
  rcases hW w hw with ⟨h1, h2⟩ | ⟨-, h⟩ | h
  · rw [h1, h2]; have := sl_le c h7 (i := TMP) (by decide); exact Or.inr (by omega_using [this, hsz])
  · exact Or.inr (by omega_using [h, hsz])
  · rw [Cfg.winTbl, bitsAt_eq] at h
    exact Or.inl (by omega_using [h, ht])

/-- What the code of a point's multiplication keeps throughout: the working
space, the prime and the constants of the formulas. -/
structure CoreCtx (c : Cfg) (base : Addr) (s : State) : Prop where
  scr : Scr s base size
  far : Far s base 8192
  mp : sv c base s MP = c.C.p
  ap : sv c base s AP = c.mont c.C.a
  b3p : sv c base s B3P = c.mont (3 * c.C.b)
  zero : sv c base s ZERO = 0
  onep : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p

/-- What the windows' code keeps throughout: the working space, the prime,
the constants of the formulas, and the table of the bits of `k`. -/
structure WinCtx (c : Cfg) (base : Addr) (k : Nat) (s : State) : Prop extends CoreCtx c base s where
  bits : ∀ t < 8 * c.C.len, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0

/-- Code that keeps `r12` and writes only what the windows write keeps the
working space and the constants. -/
theorem CoreCtx.next {base : Addr} {s s' : State} (h : CoreCtx c base s) (hc : CfgOk c)
    {rs : List Reg} (hr : Rest rs s s') (h12 : .r12 ∉ rs) {W : List (Nat × Nat)}
    (hu : Unch base W s.mem s'.mem) (hW : WinW c W) : CoreCtx c base s' := by
  have h7 := hc.n10
  have hn := h.scr.nowrap
  have e : ∀ i, i < 12 → i ≠ TMP → sv c base s' i = sv c base s i := fun i hi hit =>
    sv_unch hu h7 hn (by omega_using [hi]) (hW.apart_const h7 hi hit)
  exact ⟨h.scr.of_rest hr h12, h.far.of_rest hr, (e MP (by decide) (by decide)).trans h.mp,
    (e AP (by decide) (by decide)).trans h.ap, (e B3P (by decide) (by decide)).trans h.b3p,
    (e ZERO (by decide) (by decide)).trans h.zero, (e ONEP (by decide) (by decide)).trans h.onep⟩

/-- Code that keeps `r12` and writes only what the windows write keeps
it. -/
theorem WinCtx.next {base : Addr} {k : Nat} {s s' : State} (h : WinCtx c base k s) (hc : CfgOk c)
    {rs : List Reg} (hr : Rest rs s s') (h12 : .r12 ∉ rs) {W : List (Nat × Nat)}
    (hu : Unch base W s.mem s'.mem) (hW : WinW c W) : WinCtx c base k s' := by
  refine ⟨h.toCoreCtx.next hc hr h12 hu hW, fun t ht => ?_⟩
  have ht' : t < 64 * c.n := Nat.lt_of_lt_of_le ht (scalarBits_le hc)
  rw [tbl_unch hu hc.n10 (j := 0) (by decide) ht' (hW.apart_bits hc.n10 ht'), h.bits t ht]

theorem CoreCtx.p_pos {base : Addr} {s : State} (_ : CoreCtx c base s) (hc : CfgOk c) : 0 < c.C.p := by
  have := hc.p_ge; omega_using [this]

/-- The constants are below `p`. -/
theorem CoreCtx.lt {base : Addr} {s : State} (h : CoreCtx c base s) (hc : CfgOk c) :
    ∀ i ∈ [AP, B3P, ZERO, ONEP], sv c base s i < c.C.p := by
  have hp := h.p_pos hc
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · rw [h.ap]; exact Nat.mod_lt _ hp
  · rw [h.b3p]; exact Nat.mod_lt _ hp
  · rw [h.zero]; exact hp
  · rw [h.onep]; exact Nat.mod_lt _ hp

theorem CoreCtx.fv_ap {base : Addr} {s : State} (h : CoreCtx c base s) (hc : CfgOk c) :
    fv c base s AP = Fin.ofNat c.C.p c.C.a := by
  show toM _ _ (sv c base s AP) = _; rw [h.ap]; exact toM_cmont hc _

theorem CoreCtx.fv_b3p {base : Addr} {s : State} (h : CoreCtx c base s) (hc : CfgOk c) :
    fv c base s B3P = Fin.ofNat c.C.p (3 * c.C.b) := by
  show toM _ _ (sv c base s B3P) = _; rw [h.b3p]; exact toM_cmont hc _

theorem CoreCtx.fv_zero {base : Addr} {s : State} (h : CoreCtx c base s) : fv c base s ZERO = 0 := by
  show toM _ _ (sv c base s ZERO) = _; rw [h.zero]; exact toM_zero _ _

theorem CoreCtx.fv_onep {base : Addr} {s : State} (h : CoreCtx c base s) (hc : CfgOk c) :
    fv c base s ONEP = 1 := by
  show toM _ _ (sv c base s ONEP) = _; rw [h.onep]; exact toM_one (unitMod_pow_two hc.p_odd _)

/-- A numbered slot a field program does not write keeps its number. -/
theorem sv_pW {base : Addr} {l : List Nat} {m m' : Mem} (hu : Unch base (pW c l) m m') (h7 : c.n < 10)
    (hn : base.toNat + size ≤ 2 ^ 32) {i : Nat} (hi : i < 45) (hl : i ∉ l) :
    wordsVal m' base (c.sl i) c.n = wordsVal m base (c.sl i) c.n :=
  sv_unch hu h7 hn hi (apart_append (apart_slW hl) (apart_wk h7 hi))

/-! ## Field programs on the slots of points -/

/-- A field program of the numbered operations `N` (`ofN`) on the slots of
the points `p`, `q` and `o`, `o`'s apart from the others' and the
temporaries': `o` holds, below `p`, what `N` computes of what `a`, `3b`, `p`
and `q` hold; only the temporaries, `o`, the temporary slot and the field
arithmetic's own working space change. -/
theorem ptOp_ok (hc : CfgOk c) {N : List FOp} (hN : NumOk N) {p₁ p₂ p₃ q₁ q₂ q₃ o₁ o₂ o₃ : Nat}
    (hnd : [T0, T1, T2, T3, T4, T5, o₁, o₂, o₃].Nodup)
    (hap : ∀ i ∈ [AP, B3P, p₁, p₂, p₃, q₁, q₂, q₃], i ∉ [T0, T1, T2, T3, T4, T5, o₁, o₂, o₃])
    (hin : ∀ i ∈ [p₁, p₂, p₃, q₁, q₂, q₃, o₁, o₂, o₃], i ∈ winIds)
    {s : State} {base : Addr} (hs : Scr s base size) (hf : Far s base 8192) (hM : sv c base s MP = c.C.p)
    (hlt : ∀ i ∈ [AP, B3P, p₁, p₂, p₃, q₁, q₂, q₃], sv c base s i < c.C.p) :
    WP isa (fprog c.SP (ofN N c.rcbSlots (c.pt p₁ p₂ p₃) (c.pt q₁ q₂ q₃) (c.pt o₁ o₂ o₃)) c.umaal) s fun s' =>
      Rest Mont.callClob s s' ∧
      Unch base (pW c [T0, T1, T2, T3, T4, T5, o₁, o₂, o₃, TMP]) s.mem s'.mem ∧
      (∀ i ∈ [o₁, o₂, o₃], sv c base s' i < c.C.p) ∧
      (fv c base s' o₁, fv c base s' o₂, fv c base s' o₃) =
        (runOps N (fun y => tmv c.C c.n base s
            (rcbσ c.rcbSlots (c.pt p₁ p₂ p₃) (c.pt q₁ q₂ q₃) (c.pt o₁ o₂ o₃) y)) 6,
          runOps N (fun y => tmv c.C c.n base s
            (rcbσ c.rcbSlots (c.pt p₁ p₂ p₃) (c.pt q₁ q₂ q₃) (c.pt o₁ o₂ o₃) y)) 7,
          runOps N (fun y => tmv c.C c.n base s
            (rcbσ c.rcbSlots (c.pt p₁ p₂ p₃) (c.pt q₁ q₂ q₃) (c.pt o₁ o₂ o₃) y)) 8) := by
  have hn := hc.n0
  obtain hA : RcbApart c.rcbSlots (c.pt p₁ p₂ p₃) (c.pt q₁ q₂ q₃) (c.pt o₁ o₂ o₃) :=
    rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, o₁, o₂, o₃]) (lr := [AP, B3P, p₁, p₂, p₃, q₁, q₂, q₃])
      rfl rfl hnd hap
  obtain hids : ∀ i ∈ [T0, T1, T2, T3, T4, T5, o₁, o₂, o₃] ++ [AP, B3P, p₁, p₂, p₃, q₁, q₂, q₃], i ∈ winIds := by
    intro i hi
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hi hin
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | h | h | h | rfl | rfl | h | h | h | h | h | h
    all_goals first | decide | exact hin i (by simp only [h, true_or, or_true])
  obtain hSl : ∀ x ∈ rcbW c.rcbSlots (c.pt o₁ o₂ o₃) ++ rcbR c.rcbSlots (c.pt p₁ p₂ p₃) (c.pt q₁ q₂ q₃),
      winSl c x := by
    intro x hx
    have hx' : x ∈ ([T0, T1, T2, T3, T4, T5, o₁, o₂, o₃] ++ [AP, B3P, p₁, p₂, p₃, q₁, q₂, q₃]).map c.sl := hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    exact List.mem_map_of_mem (hids i hi)
  obtain I : Inv c.MP' base size c.C.p (winSl c) (rcbR c.rcbSlots (c.pt p₁ p₂ p₃) (c.pt q₁ q₂ q₃))
      (tmv c.C c.n base s) s :=
    ⟨hs, modP_of hc hM, fun x hx => hSl x (List.mem_append_right _ hx), fun x hx => by
      have hx' : x ∈ [AP, B3P, p₁, p₂, p₃, q₁, q₂, q₃].map c.sl := hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
      exact hlt i hi, fun _ _ => rfl, hf⟩
  refine WP.mono (fprog_ok (winLay hc) (winWk hc) hc.fp (unitMod_pow_two hc.p_odd (64 * c.n)) _ I
    (fun op hop x hx => hSl x (ofN_slots op hop x hx)) (ofN_readsOk hN _ _ _ _)) fun s' ⟨hk, I'⟩ => ?_
  obtain hval : ∀ x ∈ [(c.pt o₁ o₂ o₃).x, (c.pt o₁ o₂ o₃).y, (c.pt o₁ o₂ o₃).z],
      x ∈ validAfter (ofN N c.rcbSlots (c.pt p₁ p₂ p₃) (c.pt q₁ q₂ q₃) (c.pt o₁ o₂ o₃))
        (rcbR c.rcbSlots (c.pt p₁ p₂ p₃) (c.pt q₁ q₂ q₃)) := fun x hx => by
    rw [mem_validAfter]; exact Or.inr (ofN_out_mem hN hx)
  refine ⟨hk.rest, ?_, fun i hi => ?_, ?_⟩
  · obtain hk' : ProgKeep c.MP' base c.wk (rcbW c.rcbSlots (c.pt o₁ o₂ o₃)) s s' := hk.mono fun w hw => by
      obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
      exact ofN_out hN op hop
    refine hk'.unch.mono fun w hw => ?_
    · have hw' : w ∈ ([T0, T1, T2, T3, T4, T5, o₁, o₂, o₃].map c.sl).map (·, 8 * c.n) ++
          [(c.sl TMP, 8 * c.n), (c.wk, 64 * c.n)] := hw
      simp only [pW, slW, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hw' ⊢
      rcases hw' with h | h | h | h | h | h | h | h | h | h | h <;> simp only [h, true_or, or_true]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact I'.lt _ (hval _ List.mem_cons_self)
    · exact I'.lt _ (hval _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · exact I'.lt _ (hval _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  · have e6 := ofN_run hN hA (tmv c.C c.n base s) 6
    have e7 := ofN_run hN hA (tmv c.C c.n base s) 7
    have e8 := ofN_run hN hA (tmv c.C c.n base s) 8
    rw [← e6, ← e7, ← e8]
    exact Prod.ext (I'.val _ (hval _ List.mem_cons_self))
      (Prod.ext (I'.val _ (hval _ (List.mem_cons_of_mem _ List.mem_cons_self)))
        (I'.val _ (hval _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))

/-! ## `R = 2^w R` -/

/-- The slots the windows write. -/
def winWr : List Nat := [RX, RY, RZ, DX, DY, DZ, TX, TY, TZ, T0, T1, T2, T3, T4, T5, TMP]

theorem pW_mono {l l' : List Nat} (h : ∀ i ∈ l, i ∈ l') : ∀ w ∈ pW c l, w ∈ pW c l' := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact List.mem_append_left _ (List.mem_map_of_mem (h i hi))
  · exact List.mem_append_right _ hw

theorem slot_pW {l : List Nat} {i : Nat} (h : i ∈ l) : (c.sl i, 8 * c.n) ∈ pW c l :=
  List.mem_append_left _ (List.mem_map_of_mem (f := fun i => (c.sl i, 8 * c.n)) h)

theorem winW_winWr (h7 : c.n < 10) : WinW c (pW c winWr) := winW_pW h7 (by decide)

/-- The working points: `D`, and `T`. -/
def wpt : Bool → Nat × Nat × Nat
  | true => (DX, DY, DZ)
  | false => (TX, TY, TZ)

/-- The numbers a field program reads are below `p`. -/
theorem CoreCtx.lt8 {base : Addr} {s : State} (h : CoreCtx c base s) (hc : CfgOk c)
    {p₁ p₂ p₃ q₁ q₂ q₃ : Nat} (hp : ∀ i ∈ [p₁, p₂, p₃], sv c base s i < c.C.p)
    (hq : ∀ i ∈ [q₁, q₂, q₃], sv c base s i < c.C.p) :
    ∀ i ∈ [AP, B3P, p₁, p₂, p₃, q₁, q₂, q₃], sv c base s i < c.C.p := by
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.lt hc _ (by decide)
  · exact h.lt hc _ (by decide)
  · exact hp _ List.mem_cons_self
  · exact hp _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact hp _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact hq _ List.mem_cons_self
  · exact hq _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact hq _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem CoreCtx.lt_zero {base : Addr} {s : State} (h : CoreCtx c base s) (hc : CfgOk c) :
    ∀ i ∈ [ZERO, ZERO, ZERO], sv c base s i < c.C.p := fun i hi => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hi
  rw [hi]; exact h.lt hc _ (by decide)

/-- `k` doublings from the Jacobian point in `D` (`b`) or `T`, and back to
projective coordinates: `R` holds `(XZ : Y : Z³)` for a Jacobian triple of
`2^k Q`. -/
theorem winDbls_ok (hc : CfgOk c) (hC : Law c.C) {base : Addr} {kk : Nat} :
    ∀ (k : Nat) (b : Bool) {s : State} {Q : Point c.C}, WinCtx c base kk s → onCurve c.C Q = true →
    (∀ i ∈ [(wpt b).1, (wpt b).2.1, (wpt b).2.2], sv c base s i < c.C.p) →
    InvJ c.C (fv c base s (wpt b).1) (fv c base s (wpt b).2.1) (fv c base s (wpt b).2.2) Q →
    WP isa (c.winDbls k (c.pt (wpt b).1 (wpt b).2.1 (wpt b).2.2)
        (c.pt (wpt !b).1 (wpt !b).2.1 (wpt !b).2.2)) s fun s' =>
      Rest Mont.callClob s s' ∧ Unch base (pW c winWr) s.mem s'.mem ∧
      (∀ i ∈ [RX, RY, RZ], sv c base s' i < c.C.p) ∧
      ∃ X Y Z : Fe c.C, InvJ c.C X Y Z (dblPt Q k) ∧ fv c base s' RX = X * Z ∧ fv c base s' RY = Y ∧
        fv c base s' RZ = Z * Z * Z
  | 0, b, s, Q, ctx, _, hlt, hJ => by
    rw [Cfg.winDbls, fromJ_eq]
    refine WP.mono (ptOp_ok hc fromJN_ok (q₁ := ZERO) (q₂ := ZERO) (q₃ := ZERO) (o₁ := RX) (o₂ := RY)
      (o₃ := RZ) (by decide) (by cases b <;> decide) (by cases b <;> decide) ctx.scr ctx.far ctx.mp
      (ctx.lt8 hc hlt (ctx.lt_zero hc))) fun s' ⟨K, U, L, V⟩ => ?_
    obtain V' := V.trans (fromJN_run _)
    simp only [Prod.mk.injEq] at V'
    obtain ⟨vx, vy, vz⟩ := V'
    refine ⟨K, U.mono (pW_mono (by decide)), L, _, _, _, hJ, vx, vy.trans ?_, vz⟩
    show fv c base s (wpt b).2.1 + fv c base s ZERO = _
    rw [ctx.fv_zero]; grind
  | k + 1, b, s, Q, ctx, hQ, hlt, hJ => by
    obtain ⟨N, hN, he, hd⟩ := winDbl_ok (c := c) hC
    rw [Cfg.winDbls, he]
    refine WP.seq (WP.mono (ptOp_ok hc hN (by cases b <;> decide) (by cases b <;> decide)
      (by cases b <;> decide) ctx.scr ctx.far ctx.mp (ctx.lt8 hc hlt hlt)) fun s₁ ⟨K₁, U₁, L₁, V₁⟩ => ?_)
    obtain ctx₁ := ctx.next hc K₁ (by decide) U₁ (winW_pW hc.n10 (by cases b <;> decide))
    obtain J₁ : InvJ c.C (fv c base s₁ (wpt !b).1) (fv c base s₁ (wpt !b).2.1) (fv c base s₁ (wpt !b).2.2)
        (Spec.Weierstrass.add Q Q) := by
      have := hd (fun y => tmv c.C c.n base s (rcbσ c.rcbSlots (c.pt (wpt b).1 (wpt b).2.1 (wpt b).2.2)
        (c.pt (wpt b).1 (wpt b).2.1 (wpt b).2.2) (c.pt (wpt !b).1 (wpt !b).2.1 (wpt !b).2.2) y)) hQ
        (ctx.fv_ap hc) hJ
      simp only [Prod.mk.injEq] at V₁
      rw [V₁.1, V₁.2.1, V₁.2.2]; exact this
    have ih := winDbls_ok hc hC k (!b) ctx₁ (hC.onCurve_add hQ hQ) L₁ J₁
    rw [Bool.not_not] at ih
    refine WP.mono ih fun s₂ ⟨K₂, U₂, L₂, R₂⟩ => ⟨K₁.trans K₂, ?_, L₂, R₂⟩
    exact (U₁.trans U₂).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact pW_mono (by cases b <;> decide) w hw
      · exact hw

/-- `winQuad`: `R = 2^w R`, the point at infinity as `(0 : 1 : 0)`. -/
theorem winQuad_ok (hc : CfgOk c) (hC : Law c.C) {base : Addr} {kk : Nat} {s : State}
    (ctx : WinCtx c base kk s) {Q : Point c.C} (hQ : onCurve c.C Q = true)
    (hlt : ∀ i ∈ [RX, RY, RZ], sv c base s i < c.C.p)
    (hR : Rep c.C (fv c base s RX) (fv c base s RY) (fv c base s RZ) Q) :
    WP isa c.winQuad s fun s' => Rest Mont.callClob s s' ∧ Unch base (pW c winWr) s.mem s'.mem ∧
      (∀ i ∈ [RX, RY, RZ], sv c base s' i < c.C.p) ∧
      Rep c.C (fv c base s' RX) (fv c base s' RY) (fv c base s' RZ) (dblPt Q c.winW) := by
  have h7 := hc.n10
  have hn0 := hc.n0
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  rw [Cfg.winQuad, toJ_eq]
  -- To Jacobian coordinates, in `D`.
  refine WP.seq (WP.mono (ptOp_ok hc toJN_ok (p₁ := RX) (p₂ := RY) (p₃ := RZ) (q₁ := ZERO) (q₂ := ZERO)
    (q₃ := ZERO) (o₁ := DX) (o₂ := DY) (o₃ := DZ) (by decide) (by decide) (by decide) ctx.scr ctx.far
    ctx.mp (ctx.lt8 hc hlt (ctx.lt_zero hc))) fun s₁ ⟨K₁, U₁, L₁, V₁⟩ => ?_)
  obtain ctx₁ := ctx.next hc K₁ (by decide) U₁ (winW_pW h7 (by decide))
  obtain J₁ : InvJ c.C (fv c base s₁ DX) (fv c base s₁ DY) (fv c base s₁ DZ) Q :=
    InvJ.of_toJ hC hR ctx.fv_zero (V₁.trans (toJN_run _))
  -- The doublings, and back.
  refine WP.seq (WP.mono (winDbls_ok hc hC c.winW true ctx₁ hQ L₁ J₁)
    fun s₂ ⟨K₂, U₂, L₂, X, Y, Z, J₂, rx₂, ry₂, rz₂⟩ => ?_)
  obtain ctx₂ := ctx₁.next hc K₂ (by decide) U₂ (winW_winWr h7)
  have hs₂ := ctx₂.scr
  have hn := hs₂.nowrap
  -- `Y = 1` where `Z = 0`.
  rw [List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (nonzero_ok c hs₂ hn0 (sl_le c h7 (i := RZ) (by decide)))
    fun s₃ ⟨g₃, k₃, m₃⟩ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => ?_
  obtain k₄ : Rest [.r4, .r5, .r10] s₂ s₄ := (k₃.mono (by simp)).trans (u₄.rest (by simp))
  obtain m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, m₃]
  have hRY := sl_le c h7 (i := RY) (by decide)
  have hONE := sl_le c h7 (i := ONEP) (by decide)
  have h15 := sl_lt c (i := ONEP) (j := RY) (by decide)
  refine WP.mono (sel_ok (decide (sv c base s₂ RZ ≠ 0)) (2 * c.n) (hs₂.of_rest k₄ (by decide))
    (by rw [u₄.gpr, g₃]; simp only [mask32, decide_eq_true_eq]) (o := c.sl RY) (a := c.sl ONEP)
    (b := c.sl RY) (by omega_using [hRY]) (by omega_using [hONE]) (by omega_using [hRY])
    (Or.inr (by omega_using [h15])) (Or.inl (Nat.le_refl _))) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  rw [show 4 * (2 * c.n) = 8 * c.n by omega_using []] at O₅
  rw [← wordsVal_eq_val32, ← wordsVal_eq_val32, ← wordsVal_eq_val32, m₄] at e₅
  obtain U₅ : Unch base (pW c winWr) s₂.mem s₅.mem := by
    rw [← m₄]
    exact O₅.unch.mono fun w hw => by rw [List.mem_singleton.mp hw]; exact slot_pW (by decide)
  obtain o₅ : ∀ {i}, i < 45 → i ≠ RY → sv c base s₅ i = sv c base s₂ i := fun {i} hi hne => by
    have := sv_unch (c := c) O₅.unch h7 hn hi (apart_slW (l := [RY]) (by simpa using hne))
    exact this.trans (by rw [m₄])
  obtain K₅ : Rest Mont.callClob s₂ s₅ := (k₄.mono (by decide)).trans (k₅.mono (by decide))
  -- `Z³ = 0` iff the number in `RZ` is zero.
  obtain hz : sv c base s₂ RZ = 0 ↔ Z = 0 := by
    rw [← toM_eq_zero_iff hpR (L₂ RZ (by decide))]
    show fv c base s₂ RZ = 0 ↔ _
    rw [rz₂]
    constructor
    · intro h; by_contra hZ; exact cube_ne_zero hC hZ h
    · intro h; rw [h]; grind
  have hout := J₂.out hC
  refine ⟨(K₁.trans K₂).trans K₅, ?_, fun i hi => ?_, ?_⟩
  · refine ((U₁.trans U₂).trans U₅).mono fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_append.mp hw with hw | hw
      · exact pW_mono (by decide) w hw
      · exact hw
    · exact hw
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · rw [o₅ (by decide) (by decide)]; exact L₂ _ (by decide)
    · show wordsVal s₅.mem base (c.sl RY) c.n < _
      rw [e₅]; split
      · exact L₂ _ (by decide)
      · exact ctx₂.lt hc _ (by decide)
    · rw [o₅ (by decide) (by decide)]; exact L₂ _ (by decide)
  · obtain ex : fv c base s₅ RX = X * Z := by
      show toM _ _ (sv c base s₅ RX) = _; rw [o₅ (by decide) (by decide)]; exact rx₂
    obtain ez : fv c base s₅ RZ = Z * Z * Z := by
      show toM _ _ (sv c base s₅ RZ) = _; rw [o₅ (by decide) (by decide)]; exact rz₂
    obtain ey : fv c base s₅ RY = if Z = 0 then 1 else Y := by
      show toM _ _ (wordsVal s₅.mem base (c.sl RY) c.n) = _
      rw [e₅]
      by_cases h0 : sv c base s₂ RZ = 0
      · have hZ := hz.mp h0
        simp only [h0, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, hZ]
        exact ctx₂.fv_onep hc
      · have hZ : ¬Z = 0 := fun h => h0 (hz.mpr h)
        simp only [h0, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, hZ]
        exact ry₂
    rw [ex, ey, ez]
    exact hout

/-! ## The windows and the table: sizes -/

theorem winW_cases (c : Cfg) : c.winW = 4 ∨ c.winW = 3 := by
  unfold Cfg.winW; split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The windows cover the encoded scalar's bits, the last one in part. -/
theorem winJ_bounds (hc : CfgOk c) : 1 ≤ c.winJ ∧ c.winJ < 256 ∧ c.winW * (c.winJ - 1) ≤ 8 * c.C.len ∧
    8 * c.C.len ≤ c.winW * c.winJ := by
  have h8 := hc.len8
  have hh := hc.len_hi
  have h7 := hc.n10
  unfold Cfg.winJ
  rcases winW_cases c with h | h <;> rw [h] <;> omega_using [h8, hh, h7]

/-- The table is past the working space and the tables of bits, within the
`8192` bytes. -/
theorem winTbl_fit (h7 : c.n < 10) : c.winTbl + 4 * (6 * c.n) * 2 ^ c.winW ≤ 8192 := by
  unfold Cfg.winTbl Cfg.winW
  rw [bitsAt_eq]
  split <;> omega_arith

theorem winTbl_ge (c : Cfg) : size ≤ c.winTbl := by
  unfold Cfg.winTbl; rw [bitsAt_eq]; exact Nat.le_add_right _ _

theorem pow_winW (c : Cfg) : 2 ^ c.winW = 16 ∨ 2 ^ c.winW = 8 := by
  rcases winW_cases c with h | h <;> rw [h]
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- What a field program writes is below the table. -/
theorem pW_below_tbl (h7 : c.n < 10) {l : List Nat} (hl : ∀ i ∈ l, i < 45) :
    ∀ w ∈ pW c l, w.1 + w.2 ≤ c.winTbl := by
  intro w hw
  refine Nat.le_trans ?_ (winTbl_ge c)
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact sl_le c h7 (hl i hi)
  · rw [List.mem_singleton.mp hw]; exact wk_le c h7 (M := c.MP') rfl

/-! ## The table -/

/-- The first `cnt` entries of the table are, below `p`, representatives of
`[e]P`. -/
def TblOk (c : Cfg) (base : Addr) (P : Point c.C) (m : Mem) (cnt : Nat) : Prop :=
  ∀ e < cnt, (∀ j < 3, wordsVal m base (tblAt c e j) c.n < c.C.p) ∧
    Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (wordsVal m base (tblAt c e 0) c.n))
      (toM c.C.p (2 ^ (64 * c.n)) (wordsVal m base (tblAt c e 1) c.n))
      (toM c.C.p (2 ^ (64 * c.n)) (wordsVal m base (tblAt c e 2) c.n)) (mul e P)

/-- A coordinate of an entry apart from what changed. -/
theorem winTbl_unch {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (hu : Unch base W m m') {cnt e j : Nat}
    (he : e < cnt) (hj : j < 3) (hfit : c.winTbl + 4 * (6 * c.n) * cnt ≤ 8192)
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ c.winTbl ∨ c.winTbl + 4 * (6 * c.n) * cnt ≤ w.1) :
    wordsVal m' base (tblAt c e j) c.n = wordsVal m base (tblAt c e j) c.n := by
  have hmul := Nat.mul_le_mul_left (4 * (6 * c.n)) (Nat.succ_le_of_lt he)
  rw [Nat.mul_succ] at hmul
  have hj2 : 8 * c.n * j ≤ 8 * c.n * 2 := Nat.mul_le_mul_left _ (by omega_using [hj])
  refine hu.wordsVal (fun w hw => ?_) (by dsimp only [tblAt]; omega_using [hmul, hfit, hj2])
  rcases hW w hw with h | h
  · exact Or.inr (by dsimp only [tblAt]; omega_using [h])
  · exact Or.inl (by dsimp only [tblAt]; omega_using [h, hmul, hj2])

theorem TblOk.unch {base : Addr} {P : Point c.C} {W : List (Nat × Nat)} {m m' : Mem} {cnt : Nat}
    (h : TblOk c base P m cnt) (hu : Unch base W m m') (hfit : c.winTbl + 4 * (6 * c.n) * cnt ≤ 8192)
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ c.winTbl ∨ c.winTbl + 4 * (6 * c.n) * cnt ≤ w.1) :
    TblOk c base P m' cnt := by
  intro e he
  obtain ⟨hl, hr⟩ := h e he
  refine ⟨fun j hj => by rw [winTbl_unch hu he hj hfit hW]; exact hl j hj, ?_⟩
  rw [winTbl_unch hu he (by decide) hfit hW, winTbl_unch hu he (by decide) hfit hW,
    winTbl_unch hu he (by decide) hfit hW]
  exact hr

/-! ## Copies of points -/

/-- `o = a`, for points of numbered slots, `o`'s apart from each other and
from `a`'s. -/
theorem copySlots_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size)
    {o₁ o₂ o₃ a₁ a₂ a₃ : Nat} (h45 : ∀ i ∈ [o₁, o₂, o₃, a₁, a₂, a₃], i < 45) (hnd : [o₁, o₂, o₃].Nodup)
    (hoa : ∀ i ∈ [o₁, o₂, o₃], i ∉ [a₁, a₂, a₃]) :
    WP isa (.block (Point.copyPt c.n (c.pt o₁ o₂ o₃) (c.pt a₁ a₂ a₃))) s fun s' =>
      sv c base s' o₁ = sv c base s a₁ ∧ sv c base s' o₂ = sv c base s a₂ ∧
      sv c base s' o₃ = sv c base s a₃ ∧ Rest [.r4] s s' ∧ Unch base (slW c [o₁, o₂, o₃]) s.mem s'.mem := by
  have h7 := hc.n10
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true, not_false_eq_true] at hnd
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, forall_eq_or_imp, forall_eq] at hoa h45
  obtain ⟨⟨n12, n13⟩, n23⟩ := hnd
  obtain ⟨⟨x1, x2, x3⟩, ⟨y1, y2, y3⟩, ⟨z1, z2, z3⟩⟩ := hoa
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := h45
  refine WP.mono (Point.copyPt_ok hs (n := c.n) (o := c.pt o₁ o₂ o₃) (a := c.pt a₁ a₂ a₃) ?_ ?_ ?_)
    fun s' ⟨ex, ey, ez, k, O⟩ => ⟨ex, ey, ez, k, VG.Proof.Weierstrass.Arm.Outs.unch O⟩
  · intro d hd
    have hd' : d ∈ [o₁, o₂, o₃, a₁, a₂, a₃].map c.sl := hd
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> exact sl_le c h7 ‹_›
  · exact ⟨sl_apart c n12, sl_apart c n13, sl_apart c n23⟩
  · intro d hd e he
    have hd' : d ∈ [o₁, o₂, o₃].map c.sl := hd
    have he' : e ∈ [a₁, a₂, a₃].map c.sl := he
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi hj
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> exact sl_apart c ‹_›

/-! ## The window, and its entry -/

/-- `winDigit`: `r9` is window `j` of `k`, for `j` in `r11`. -/
theorem winDigit_ok (hc : CfgOk c) {base : Addr} {k : Nat} {s : State} (ctx : WinCtx c base k s)
    (hk : k < 2 ^ (8 * c.C.len)) {j : Nat} (hj : j < c.winJ) (gj : s.gpr .r11 = BitVec.ofNat 32 j) :
    WP isa c.winDigit s fun t =>
      t.gpr .r9 = BitVec.ofNat 32 (combWin c.winW k j) ∧ Rest [.r4, .r5, .r9] s t ∧ t.mem = s.mem := by
  obtain ⟨hJ1, hJ, hstart, hcover⟩ := winJ_bounds hc
  have h7 := hc.n10
  have hlen := hc.len_hi
  have hw : c.winK.w < 9 := by
    show c.winW < 9
    rcases winW_cases c with h | h <;> rw [h] <;> decide
  have hw4 : c.winW ≤ 4 := by rcases winW_cases c with h | h <;> rw [h] <;> decide
  have enc : encodable (BitVec.ofNat 32 (c.winK.J - 1)) = true :=
    (by decide +kernel : ∀ x < 256, encodable (BitVec.ofNat 32 x) = true) _ (by show c.winJ - 1 < 256; omega_using [hJ])
  have bounds := windowBits_bounds (w := c.winW) (J := c.winJ) (bits := 8 * c.C.len) hj hstart hcover
  dsimp only at bounds
  generalize hcount : (if j = c.winJ - 1 then 8 * c.C.len - c.winW * (c.winJ - 1) else c.winW) = count at bounds
  obtain ⟨hcw, hcb, hcl⟩ := bounds
  have hv : ∀ i, (fun i => (k.testBit (c.winW * j + i)).toNat) i ≤ 1 := fun i => by
    dsimp only; cases k.testBit (c.winW * j + i) <;> decide
  have bytes : ∀ i < count, s.mem (off base (bitsAt c.n 0 + c.winW * j + i)) =
      BitVec.ofNat 8 ((fun i => (k.testBit (c.winW * j + i)).toNat) i) := fun i hi => by
    rw [show bitsAt c.n 0 + c.winW * j + i = bitsAt c.n 0 + (c.winW * j + i) by omega_using [],
      ctx.bits _ (by omega_using [hcb, hi])]
    dsimp only
    cases k.testBit (c.winW * j + i) <;> rfl
  have hb0 : bitsAt c.n 0 = 4096 := by rw [bitsAt_eq]; omega_arith
  unfold Cfg.winDigit
  rw [WP.seq_iff]
  refine WP.mono (TComb.windowIndex_ok c.winK hw gj) fun s₁ ⟨p₁, k₁⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (TComb.lastTest_ok c.winK (j := j) (by omega_using [hj, hJ]) (by show c.winJ - 1 < 2 ^ 32; omega_using [hJ]) enc
    (by rw [k₁.keep.gpr .r11 (by decide), gj])) fun s₂ ⟨z₂, k₂⟩ => ?_
  have keep₂ : Rest [.r4] s s₂ := k₁.keep.trans (k₂.keep.mono (by simp))
  have mem₂ : s₂.mem = s.mem := k₂.mem.trans k₁.mem
  have hs₂ := ctx.scr.of_rest keep₂ (by decide)
  have hf₂ := ctx.far.of_rest keep₂
  have p₂ : s₂.gpr .r4 = s₂.gpr .r12 + BitVec.ofNat 32 (c.winK.w * j + farOff c.winK.L.bits) := by
    rw [k₂.keep.gpr .r4 (by decide), p₁, k₂.keep.gpr .r12 (by decide)]
  have hh := TComb.hornerWindow_ok c.winK hs₂ hf₂ hw (count := count) hcw
    (show bitsAt c.n 0 < 8192 by rw [hb0]; decide)
    (show bitsAt c.n 0 % 4096 + c.winW ≤ 4096 by rw [hb0]; omega_using [hw4])
    (show bitsAt c.n 0 + c.winW * j + count ≤ 8192 by rw [hb0]; omega_using [hcb, hlen, h7]) p₂ hv
    (by intro i hi; rw [mem₂]; exact bytes i hi)
  have hval : hornerVal (fun i => (k.testBit (c.winW * j + i)).toNat) 0 count = combWin c.winW k j :=
    window_without_padding hcw hcl hk
  have fin : ∀ t, (t.gpr .r9 = BitVec.ofNat 32 (hornerVal (fun i => (k.testBit (c.winW * j + i)).toNat) 0 count) ∧
      TComb.RegOnly [.r5, .r9] s₂ t) →
      t.gpr .r9 = BitVec.ofNat 32 (combWin c.winW k j) ∧ Rest [.r4, .r5, .r9] s t ∧ t.mem = s.mem :=
    fun t ⟨v, r⟩ => ⟨by rw [v, hval], (keep₂.mono (by simp)).trans (r.keep.mono (by simp)), r.mem.trans mem₂⟩
  by_cases h : j = c.winJ - 1
  · simp only [h, ↓reduceIte] at hcount
    subst hcount
    exact WP.ite true (by change some s₂.z = some true; simp only [z₂]; exact congrArg some (decide_eq_true h))
      (fun _ => WP.mono hh fin) (fun impossible => nomatch impossible)
  · simp only [h, ↓reduceIte] at hcount
    subst hcount
    exact WP.ite false (by change some s₂.z = some false; simp only [z₂]; exact congrArg some (decide_eq_false h))
      (fun impossible => nomatch impossible) (fun _ => WP.mono hh fin)

/-- The scan: `T` holds entry `a` of the table, for `a` in `r9`. -/
theorem winScan_ok (hc : CfgOk c) {base : Addr} {kk : Nat} {s : State} (ctx : WinCtx c base kk s)
    {a : Nat} (ha : a < 2 ^ c.winW) (ga : s.gpr .r9 = BitVec.ofNat 32 a) :
    WP isa (scan (c.sl TX) (6 * c.n) (2 ^ c.winW) c.winTbl) s fun t =>
      sv c base t TX = wordsVal s.mem base (tblAt c a 0) c.n ∧
      sv c base t TY = wordsVal s.mem base (tblAt c a 1) c.n ∧
      sv c base t TZ = wordsVal s.mem base (tblAt c a 2) c.n ∧
      Rest [.r4, .r5, .r7, .r8, .r10] s t ∧ Unch base (slW c [TX, TY, TZ]) s.mem t.mem := by
  have h7 := hc.n10
  have hfit := winTbl_fit hc.n10
  have hge := winTbl_ge c
  have hTZ := sl_le c h7 (i := TZ) (by decide)
  have hsz : size = 4096 := rfl
  have eX : c.sl TX = 64 + 8 * c.n * 20 := rfl
  have eY : c.sl TY = 64 + 8 * c.n * 21 := rfl
  have eZ : c.sl TZ = 64 + 8 * c.n * 22 := rfl
  refine WP.mono (scan_ok ctx.scr ctx.far ga ha
    (by rcases pow_winW c with h | h <;> rw [h] <;> decide) (o := c.sl TX) (k := 6 * c.n) (tbl := c.winTbl)
    (by omega_using [hTZ, eX, eZ, hsz]) hge hfit (by omega_using [h7]) (by omega_using [hfit])
    ((by decide : ∀ n < 10, encodable (BitVec.ofNat 32 (4 * (6 * n))) = true) _ h7)
    (by rcases pow_winW c with h | h <;> rw [h] <;> decide)) fun t ⟨V, K, O⟩ => ?_
  refine ⟨?_, ?_, ?_, K, ?_⟩
  · refine wordsVal_of_w32 fun i hi => ?_
    have := V i (by omega_using [hi])
    rw [show tblAt c a 0 + 4 * i = c.winTbl + 4 * (6 * c.n) * a + 4 * i by dsimp only [tblAt]; omega_using []]
    exact this
  · refine wordsVal_of_w32 fun i hi => ?_
    have := V (2 * c.n + i) (by omega_using [hi])
    rw [show c.sl TX + 4 * (2 * c.n + i) = c.sl TY + 4 * i by omega_using [eX, eY],
      show c.winTbl + 4 * (6 * c.n) * a + 4 * (2 * c.n + i) = tblAt c a 1 + 4 * i by
        dsimp only [tblAt]; omega_using []] at this
    exact this
  · refine wordsVal_of_w32 fun i hi => ?_
    have := V (4 * c.n + i) (by omega_using [hi])
    rw [show c.sl TX + 4 * (4 * c.n + i) = c.sl TZ + 4 * i by omega_using [eX, eZ],
      show c.winTbl + 4 * (6 * c.n) * a + 4 * (4 * c.n + i) = tblAt c a 2 + 4 * i by
        dsimp only [tblAt]; omega_using []] at this
    exact this
  · intro x hx
    have h1 := hx (c.sl TX, 8 * c.n) (List.mem_cons_self)
    have h2 := hx (c.sl TY, 8 * c.n) (List.mem_cons_of_mem _ List.mem_cons_self)
    have h3 := hx (c.sl TZ, 8 * c.n) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    dsimp only at h1 h2 h3
    exact O x (by omega_using [h1, h2, h3, eX, eY, eZ])

/-! ## A window -/


/-- Code that keeps `r12` and the memory keeps what the windows keep. -/
theorem WinCtx.same {base : Addr} {k : Nat} {s s' : State} (h : WinCtx c base k s) (hc : CfgOk c)
    {rs : List Reg} (hr : Rest rs s s') (h12 : .r12 ∉ rs) (hm : s'.mem = s.mem) : WinCtx c base k s' :=
  h.next hc hr h12 (W := []) (by rw [hm]; exact Unch.refl _ _ _) (fun _ h => nomatch h)

theorem unch_winWr_slW {base : Addr} {m m' : Mem} {l : List Nat} (hl : ∀ i ∈ l, i ∈ winWr)
    (h : Unch base (slW c l) m m') : Unch base (pW c winWr) m m' :=
  h.mono fun w hw => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact slot_pW (hl i hi)

theorem unch_winWr_pW {base : Addr} {m m' : Mem} {l : List Nat} (hl : ∀ i ∈ l, i ∈ winWr)
    (h : Unch base (pW c l) m m') : Unch base (pW c winWr) m m' :=
  h.mono (pW_mono hl)

theorem unch_winWr_trans {base : Addr} {m₁ m₂ m₃ : Mem} (h₁ : Unch base (pW c winWr) m₁ m₂)
    (h₂ : Unch base (pW c winWr) m₂ m₃) : Unch base (pW c winWr) m₁ m₃ :=
  (h₁.trans h₂).mono fun _ hw => (List.mem_append.mp hw).elim id id

/-- The windows' invariant at `r11 = j`: `R` represents `[k / 2^(w j)]P`,
below `p`, and the table holds the multiples of `P`. -/
structure WinInv (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s₀ s : State) (j : Nat) : Prop where
  ctx : WinCtx c base k s
  r11 : s.gpr .r11 = BitVec.ofNat 32 j
  keep : Rest powClob s₀ s
  unch : Unch base (pW c winWr) s₀.mem s.mem
  tbl : TblOk c base P s.mem (2 ^ c.winW)
  lt : ∀ i ∈ [RX, RY, RZ], sv c base s i < c.C.p
  rep : Rep c.C (fv c base s RX) (fv c base s RY) (fv c base s RZ) (mul (k / 2 ^ (c.winW * j)) P)

/-- A window. -/
theorem winStep_ok (hc : CfgOk c) (hC : Law c.C) {base : Addr} {P : Point c.C} (hP : onCurve c.C P = true)
    {k : Nat} (hk : k < 2 ^ (8 * c.C.len)) {s₀ s : State} {j : Nat} (hj : 1 ≤ j) (hjn : j ≤ c.winJ)
    (I : WinInv c base P k s₀ s j) :
    WP isa c.winStep s fun s' => WinInv c base P k s₀ s' (j - 1) ∧ s'.z = decide (j - 1 = 0) := by
  have h7 := hc.n10
  obtain ⟨hJ1, hJ, -, -⟩ := winJ_bounds hc
  have hfit := winTbl_fit hc.n10
  have hn := I.ctx.scr.nowrap
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega_using [hj]⟩
  rw [Nat.add_sub_cancel]
  have hQ := hC.onCurve_mul hP (k / 2 ^ (c.winW * (i + 1)))
  have below : ∀ {l : List Nat}, (∀ i ∈ l, i < 45) → ∀ w ∈ pW c l,
      w.1 + w.2 ≤ c.winTbl ∨ c.winTbl + 4 * (6 * c.n) * 2 ^ c.winW ≤ w.1 :=
    fun hl w hw => Or.inl (pW_below_tbl h7 hl w hw)
  rw [Cfg.winStep]
  refine WP.seq (wp_decCounter hj I.r11 fun s₁ u₁ => WP.block_nil ?_)
  rw [Nat.add_sub_cancel] at u₁
  obtain k₁ : Rest [.r11] s s₁ := u₁.rest (by simp)
  obtain ctx₁ := I.ctx.same hc k₁ (by decide) u₁.mem
  -- `R = 2^w R`.
  refine WP.seq (WP.mono (winQuad_ok hc hC ctx₁ hQ
    (fun i hi => by show wordsVal s₁.mem _ _ _ < _; rw [u₁.mem]; exact I.lt i hi)
    (by show Rep _ (toM _ _ (wordsVal s₁.mem _ _ _)) (toM _ _ (wordsVal s₁.mem _ _ _))
          (toM _ _ (wordsVal s₁.mem _ _ _)) _
        rw [u₁.mem]; exact I.rep)) fun s₂ ⟨K₂, U₂, L₂, R₂⟩ => ?_)
  obtain ctx₂ := ctx₁.next hc K₂ (by decide) U₂ (winW_winWr h7)
  obtain g₂ : s₂.gpr .r11 = BitVec.ofNat 32 i := by rw [K₂.gpr _ r11_not_clob, u₁.gpr]
  obtain U₂' : Unch base (pW c winWr) s.mem s₂.mem := by rw [← u₁.mem]; exact U₂
  obtain tbl₂ : TblOk c base P s₂.mem (2 ^ c.winW) := I.tbl.unch U₂' hfit (below (by decide))
  -- The window, and its entry.
  refine WP.seq (WP.mono (winDigit_ok hc ctx₂ hk (j := i) (by omega_using [hjn]) g₂) fun s₃ ⟨g₃, k₃, m₃⟩ => ?_)
  obtain ctx₃ := ctx₂.same hc k₃ (by decide) m₃
  refine WP.seq (WP.mono (winScan_ok hc ctx₃ (combWin_lt _ _ _) g₃) fun s₄ ⟨ex₄, ey₄, ez₄, k₄, U₄⟩ => ?_)
  obtain ctx₄ := ctx₃.next hc k₄ (by decide) U₄ (winW_slW h7 (by decide))
  obtain U₄' : Unch base (slW c [TX, TY, TZ]) s₂.mem s₄.mem := by rw [← m₃]; exact U₄
  rw [m₃] at ex₄ ey₄ ez₄
  obtain ⟨tl, tr⟩ := tbl₂ (combWin c.winW k i) (combWin_lt _ _ _)
  obtain r₄ : ∀ i ∈ [RX, RY, RZ], sv c base s₄ i = sv c base s₂ i := fun i hi =>
    sv_unch U₄' h7 hn ((by decide : ∀ i ∈ [RX, RY, RZ], i < 45) i hi)
      (apart_slW ((by decide : ∀ i ∈ [RX, RY, RZ], i ∉ [TX, TY, TZ]) i hi))
  obtain ltR₄ : ∀ i ∈ [RX, RY, RZ], sv c base s₄ i < c.C.p := fun i hi => by rw [r₄ i hi]; exact L₂ i hi
  obtain ltT₄ : ∀ i ∈ [TX, TY, TZ], sv c base s₄ i < c.C.p := fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · rw [ex₄]; exact tl 0 (by decide)
    · rw [ey₄]; exact tl 1 (by decide)
    · rw [ez₄]; exact tl 2 (by decide)
  obtain repR₄ : Rep c.C (fv c base s₄ RX) (fv c base s₄ RY) (fv c base s₄ RZ)
      (dblPt (mul (k / 2 ^ (c.winW * (i + 1))) P) c.winW) := by
    show Rep _ (toM _ _ (sv c base s₄ RX)) (toM _ _ (sv c base s₄ RY)) (toM _ _ (sv c base s₄ RZ)) _
    rw [r₄ RX (by decide), r₄ RY (by decide), r₄ RZ (by decide)]; exact R₂
  obtain repT₄ : Rep c.C (fv c base s₄ TX) (fv c base s₄ TY) (fv c base s₄ TZ) (mul (combWin c.winW k i) P) := by
    show Rep _ (toM _ _ (sv c base s₄ TX)) (toM _ _ (sv c base s₄ TY)) (toM _ _ (sv c base s₄ TZ)) _
    rw [ex₄, ey₄, ez₄]; exact tr
  -- `D = R + T`.
  obtain ⟨N, hN, eN, hadd⟩ := winAdd_ok (c := c) hC
  rw [eN]
  refine WP.seq (WP.mono (ptOp_ok hc hN (p₁ := RX) (p₂ := RY) (p₃ := RZ) (q₁ := TX) (q₂ := TY)
    (q₃ := TZ) (o₁ := DX) (o₂ := DY) (o₃ := DZ) (by decide) (by decide) (by decide) ctx₄.scr ctx₄.far
    ctx₄.mp (ctx₄.lt8 hc ltR₄ ltT₄)) fun s₅ ⟨K₅, U₅, L₅, V₅⟩ => ?_)
  obtain ctx₅ := ctx₄.next hc K₅ (by decide) U₅ (winW_pW h7 (by decide))
  obtain repD₅ : Rep c.C (fv c base s₅ DX) (fv c base s₅ DY) (fv c base s₅ DZ) (mul (k / 2 ^ (c.winW * i)) P) := by
    rw [← win_pt hC hP c.winW k i]
    have := hadd (fun y => tmv c.C c.n base s₄ (rcbσ c.rcbSlots (c.pt RX RY RZ) (c.pt TX TY TZ)
      (c.pt DX DY DZ) y)) (onCurve_dblPt hC _ hQ) (hC.onCurve_mul hP _) (ctx₄.fv_ap hc) (ctx₄.fv_b3p hc)
      nofun repR₄ repT₄
    simp only [Prod.mk.injEq] at V₅
    rw [V₅.1, V₅.2.1, V₅.2.2]; exact this
  -- `R = D`.
  refine VG.Proof.X25519.Arm.WP.append (copySlots_ok hc ctx₅.scr (o₁ := RX) (o₂ := RY) (o₃ := RZ)
    (a₁ := DX) (a₂ := DY) (a₃ := DZ) (by decide) (by decide) (by decide))
    fun s₆ ⟨ex₆, ey₆, ez₆, k₆, U₆⟩ => ?_
  obtain ctx₆ := ctx₅.next hc k₆ (by decide) U₆ (winW_slW h7 (by decide))
  obtain g₆ : s₆.gpr .r11 = BitVec.ofNat 32 i := by
    rw [k₆.gpr _ (by decide), K₅.gpr _ r11_not_clob, k₄.gpr _ (by decide), k₃.gpr _ (by decide), g₂]
  refine wp_testCounter (by omega_using [hjn, hJ]) g₆ fun s₇ f₇ z₇ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, z₇⟩
  · exact ctx₆.same hc (f₇.rest []) (by decide) f₇.mem
  · rw [f₇.gpr, g₆]
  · exact ((((((I.keep.trans (k₁.mono (by decide))).trans (K₂.mono (by decide))).trans
      (k₃.mono (by decide))).trans (k₄.mono (by decide))).trans (K₅.mono (by decide))).trans
      (k₆.mono (by decide))).trans (f₇.rest _)
  · rw [f₇.mem]
    exact unch_winWr_trans I.unch (unch_winWr_trans U₂' (unch_winWr_trans (unch_winWr_slW (by decide) U₄')
      (unch_winWr_trans (unch_winWr_pW (by decide) U₅) (unch_winWr_slW (by decide) U₆))))
  · rw [f₇.mem]
    exact ((tbl₂.unch (unch_winWr_slW (by decide) U₄') hfit (below (by decide))).unch U₅ hfit
      (below (by decide))).unch (unch_winWr_slW (by decide) U₆) hfit (below (by decide))
  · intro i hi
    show wordsVal s₇.mem _ _ _ < _
    rw [f₇.mem]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact lt_of_eq_of_lt ex₆ (L₅ _ (by decide))
    · exact lt_of_eq_of_lt ey₆ (L₅ _ (by decide))
    · exact lt_of_eq_of_lt ez₆ (L₅ _ (by decide))
  · show Rep _ (toM _ _ (wordsVal s₇.mem _ _ _)) (toM _ _ (wordsVal s₇.mem _ _ _))
      (toM _ _ (wordsVal s₇.mem _ _ _)) _
    rw [f₇.mem]
    show Rep _ (toM _ _ (sv c base s₆ RX)) (toM _ _ (sv c base s₆ RY)) (toM _ _ (sv c base s₆ RZ)) _
    rw [ex₆, ey₆, ez₆]; exact repD₅

/-! ## The table's entries -/

/-- An entry is within the table. -/
theorem tblAt_le (hc : CfgOk c) {e : Nat} (he : e < 2 ^ c.winW) : tblAt c e 0 + 24 * c.n ≤ 8192 := by
  have hfit := winTbl_fit hc.n10
  have hmul := Nat.mul_le_mul_left (4 * (6 * c.n)) (Nat.succ_le_of_lt he)
  rw [Nat.mul_succ] at hmul
  dsimp only [tblAt]; omega_using [hfit, hmul]

/-- `storePt` to entry `e`, which `r5 + d` is at. -/
theorem storeEntry_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) (hf : Far s base 8192)
    {K d e p₁ p₂ p₃ : Nat} (hp : s.gpr .r5 = s.gpr .r12 + BitVec.ofNat 32 K) (hK : K + d = tblAt c e 0)
    (he : e < 2 ^ c.winW) (hd : d + 24 * c.n ≤ 4096) (h45 : ∀ i ∈ [p₁, p₂, p₃], i < 45) :
    WP isa (.block (storePt c.n d (c.pt p₁ p₂ p₃))) s fun s' =>
      wordsVal s'.mem base (tblAt c e 0) c.n = sv c base s p₁ ∧
      wordsVal s'.mem base (tblAt c e 1) c.n = sv c base s p₂ ∧
      wordsVal s'.mem base (tblAt c e 2) c.n = sv c base s p₃ ∧
      Rest [.r4] s s' ∧ Outside base (tblAt c e 0) (24 * c.n) s.mem s'.mem := by
  have h7 := hc.n10
  have hle := tblAt_le hc he
  have hge : size ≤ tblAt c e 0 := Nat.le_trans (winTbl_ge c) (by dsimp only [tblAt]; omega_using [])
  refine WP.mono (storePt_ok hs hf (n := c.n) (K := K) (d := d) (p := c.pt p₁ p₂ p₃) hp ?_ (by rw [hK]; exact hge)
    (by rw [hK]; exact hle) hd) fun s' ⟨ex, ey, ez, k, O⟩ => ?_
  · intro x hx
    have hx' : x ∈ [p₁, p₂, p₃].map c.sl := hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    exact sl_le c h7 (h45 i hi)
  · rw [hK] at ex ey ez O
    rw [show tblAt c e 0 + 8 * c.n = tblAt c e 1 by dsimp only [tblAt]; omega_using []] at ey
    rw [show tblAt c e 0 + 16 * c.n = tblAt c e 2 by dsimp only [tblAt]; omega_using []] at ez
    exact ⟨ex, ey, ez, k, O⟩

/-- A point stored as entry `e` extends the table. -/
theorem TblOk.store {base : Addr} {P : Point c.C} {m m' : Mem} {e : Nat} (h : TblOk c base P m e)
    (hc : CfgOk c) (he : e < 2 ^ c.winW) (O : Outside base (tblAt c e 0) (24 * c.n) m m') {x y z : Nat}
    (hx : wordsVal m' base (tblAt c e 0) c.n = x) (hy : wordsVal m' base (tblAt c e 1) c.n = y)
    (hz : wordsVal m' base (tblAt c e 2) c.n = z) (lx : x < c.C.p) (ly : y < c.C.p) (lz : z < c.C.p)
    (hr : Rep c.C (toM c.C.p (2 ^ (64 * c.n)) x) (toM c.C.p (2 ^ (64 * c.n)) y)
      (toM c.C.p (2 ^ (64 * c.n)) z) (mul e P)) : TblOk c base P m' (e + 1) := by
  have hle := tblAt_le hc he
  intro e' he'
  rcases Nat.lt_succ_iff_lt_or_eq.mp he' with h' | rfl
  · exact h.unch O.unch (by dsimp only [tblAt] at hle; omega_using [hle]) (fun w hw => by
      rw [List.mem_singleton.mp hw]; exact Or.inr (by dsimp only [tblAt]; omega_using [])) e' h'
  · refine ⟨fun j hj => ?_, by rw [hx, hy, hz]; exact hr⟩
    obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega_using [hj]
    · rw [hx]; exact lx
    · rw [hy]; exact ly
    · rw [hz]; exact lz

/-- Everything the windows write: the slots, the field arithmetic's own
working space, and the table. -/
abbrev winTW (c : Cfg) : List (Nat × Nat) := pW c winWr ++ [(c.winTbl, 4 * (6 * c.n) * 2 ^ c.winW)]

theorem unch_winTW {base : Addr} {m m' : Mem} (h : Unch base (pW c winWr) m m') : Unch base (winTW c) m m' :=
  h.mono fun _ hw => List.mem_append_left _ hw

/-- A store to an entry is within what the windows write. -/
theorem unch_winTW_entry {base : Addr} {m m' : Mem} {e : Nat} (he : e < 2 ^ c.winW)
    (O : Outside base (tblAt c e 0) (24 * c.n) m m') : Unch base (winTW c) m m' := by
  have hmul := Nat.mul_le_mul_left (4 * (6 * c.n)) (Nat.succ_le_of_lt he)
  rw [Nat.mul_succ] at hmul
  refine O.unch.cover fun w hw => ?_
  rw [List.mem_singleton.mp hw]
  exact ⟨_, List.mem_append_right _ List.mem_cons_self, by dsimp only [tblAt]; omega_using [],
    by dsimp only [tblAt]; omega_using [hmul]⟩

theorem unch_winTW_trans {base : Addr} {m₁ m₂ m₃ : Mem} (h₁ : Unch base (winTW c) m₁ m₂)
    (h₂ : Unch base (winTW c) m₂ m₃) : Unch base (winTW c) m₁ m₃ :=
  (h₁.trans h₂).mono fun _ hw => (List.mem_append.mp hw).elim id id

theorem winW_winTW (h7 : c.n < 10) : WinW c (winTW c) :=
  (winW_winWr h7).append (winW_tbl (Nat.le_refl _))

/-- The build's invariant at `r11 = e`: the entries up to `e` are there, `D`
holds `[e]P`, and the point is as it was. -/
structure BuildInv (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s₀ s : State) (e : Nat) : Prop where
  ctx : WinCtx c base k s
  r11 : s.gpr .r11 = BitVec.ofNat 32 e
  keep : Rest powClob s₀ s
  unch : Unch base (winTW c) s₀.mem s.mem
  tbl : TblOk c base P s.mem (e + 1)
  q : ∀ i ∈ [RX, RY], sv c base s i = sv c base s₀ i
  lt : ∀ i ∈ [DX, DY, DZ], sv c base s i < c.C.p
  rep : Rep c.C (fv c base s DX) (fv c base s DY) (fv c base s DZ) (mul e P)

/-- Entry `e + 1`. -/
theorem winBuildStep_ok (hc : CfgOk c) (hC : Law c.C) {base : Addr} {P : Point c.C}
    (hP : onCurve c.C P = true) {k : Nat} {s₀ s : State} (hqx : sv c base s₀ RX < c.C.p)
    (hqy : sv c base s₀ RY < c.C.p) (hG : Rep c.C (fv c base s₀ RX) (fv c base s₀ RY) 1 P) {e : Nat}
    (he : e < 2 ^ c.winW - 1) (I : BuildInv c base P k s₀ s e) :
    WP isa c.winBuildStep s fun s' =>
      BuildInv c base P k s₀ s' (e + 1) ∧ s'.z = decide (e + 1 = 2 ^ c.winW - 1) := by
  have h7 := hc.n10
  have hn := I.ctx.scr.nowrap
  have hfit := winTbl_fit hc.n10
  have hge := winTbl_ge c
  have hsz : size = 4096 := rfl
  have he1 : e + 1 < 2 ^ c.winW := by omega_using [he]
  have h16 : 2 ^ c.winW ≤ 16 := by rcases pow_winW c with h | h <;> rw [h] <;> decide
  have h24 : 4 * (6 * c.n) = 24 * c.n := by omega_using []
  have below : ∀ {l : List Nat}, (∀ i ∈ l, i < 45) → ∀ {cnt : Nat}, ∀ w ∈ pW c l,
      w.1 + w.2 ≤ c.winTbl ∨ c.winTbl + 4 * (6 * c.n) * cnt ≤ w.1 :=
    fun hl _ w hw => Or.inl (pW_below_tbl h7 hl w hw)
  obtain ltQ : ∀ i ∈ [RX, RY, ONEP], sv c base s i < c.C.p := fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · rw [I.q RX (by decide)]; exact hqx
    · rw [I.q RY (by decide)]; exact hqy
    · exact I.ctx.lt hc _ (by decide)
  obtain repQ : Rep c.C (fv c base s RX) (fv c base s RY) (fv c base s ONEP) P := by
    rw [I.ctx.fv_onep hc]
    show Rep _ (toM _ _ (sv c base s RX)) (toM _ _ (sv c base s RY)) _ _
    rw [I.q RX (by decide), I.q RY (by decide)]; exact hG
  obtain ⟨N, hN, eN, hadd⟩ := winAddM_ok (c := c) hC
  rw [Cfg.winBuildStep, eN]
  -- `T = D + Q`.
  refine WP.seq (WP.mono (ptOp_ok hc hN (p₁ := DX) (p₂ := DY) (p₃ := DZ) (q₁ := RX) (q₂ := RY)
    (q₃ := ONEP) (o₁ := TX) (o₂ := TY) (o₃ := TZ) (by decide) (by decide) (by decide) I.ctx.scr I.ctx.far
    I.ctx.mp (I.ctx.lt8 hc I.lt ltQ)) fun s₁ ⟨K₁, U₁, L₁, V₁⟩ => ?_)
  obtain ctx₁ := I.ctx.next hc K₁ (by decide) U₁ (winW_pW h7 (by decide))
  obtain repT₁ : Rep c.C (fv c base s₁ TX) (fv c base s₁ TY) (fv c base s₁ TZ) (mul (e + 1) P) := by
    rw [← mul_succ_pt hC hP e]
    have := hadd (fun y => tmv c.C c.n base s (rcbσ c.rcbSlots (c.pt DX DY DZ) (c.pt RX RY ONEP)
      (c.pt TX TY TZ) y)) (hC.onCurve_mul hP _) hP (I.ctx.fv_ap hc) (I.ctx.fv_b3p hc)
      (fun _ => I.ctx.fv_onep hc) I.rep repQ
    simp only [Prod.mk.injEq] at V₁
    rw [V₁.1, V₁.2.1, V₁.2.2]; exact this
  obtain g₁ : s₁.gpr .r11 = BitVec.ofNat 32 e := by rw [K₁.gpr _ r11_not_clob, I.r11]
  -- The entry, stored.
  simp only [List.append_assoc]
  refine wp_entryPtr ((by decide : ∀ n < 10, encodable (BitVec.ofNat 32 (24 * n)) = true) _ h7)
    (by omega_using [hfit, h7]) g₁ fun s₂ k₂ m₂ p₂ => ?_
  obtain ctx₂ := ctx₁.same hc k₂ (by decide) m₂
  refine VG.Proof.X25519.Arm.WP.append (storeEntry_ok hc ctx₂.scr ctx₂.far (d := 0) (e := e + 1) p₂
    (by dsimp only [tblAt]; rw [h24, Nat.mul_succ]; omega_using []) he1 (by omega_using [h7]) (by decide))
    fun s₃ ⟨sx, sy, sz, k₃, O₃⟩ => ?_
  obtain e₂ : ∀ i, sv c base s₂ i = sv c base s₁ i := fun i => by show wordsVal s₂.mem _ _ _ = _; rw [m₂]
  rw [e₂] at sx sy sz
  obtain ctx₃ := ctx₂.next hc k₃ (by decide) O₃.unch
    (winW_tbl (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))
  obtain U₁' : Unch base (pW c [T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP]) s.mem s₂.mem := by rw [m₂]; exact U₁
  obtain tbl₃ : TblOk c base P s₃.mem (e + 1 + 1) :=
    (I.tbl.unch U₁' (by have := Nat.mul_le_mul_left (4 * (6 * c.n)) (Nat.le_of_lt he1); omega_using [hfit, this])
      (below (by decide))).store hc he1 O₃ sx sy sz (L₁ _ (by decide)) (L₁ _ (by decide)) (L₁ _ (by decide)) repT₁
  -- `D = T`.
  refine VG.Proof.X25519.Arm.WP.append (copySlots_ok hc ctx₃.scr (o₁ := DX) (o₂ := DY) (o₃ := DZ)
    (a₁ := TX) (a₂ := TY) (a₃ := TZ) (by decide) (by decide) (by decide))
    fun s₄ ⟨ex₄, ey₄, ez₄, k₄, U₄⟩ => ?_
  obtain ctx₄ := ctx₃.next hc k₄ (by decide) U₄ (winW_slW h7 (by decide))
  obtain t₃ : ∀ i ∈ [TX, TY, TZ], sv c base s₃ i = sv c base s₁ i := fun i hi => by
    have h45 : i < 45 := (by decide : ∀ i ∈ [TX, TY, TZ], i < 45) i hi
    have hle := sl_le c h7 h45
    have : sv c base s₃ i = sv c base s₂ i := O₃.wordsVal
      (Or.inl (Nat.le_trans hle (Nat.le_trans hge
        (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))))
      (by omega_using [hle, hsz])
    rw [this, e₂]
  rw [t₃ TX (by decide)] at ex₄
  rw [t₃ TY (by decide)] at ey₄
  rw [t₃ TZ (by decide)] at ez₄
  -- `r11 += 1`.
  refine wp_dp (op2_imm (by decide)) fun s₅ u₅ => wp_cmp (op2_imm
    ((by decide : ∀ x < 17, encodable (BitVec.ofNat 32 (x - 1)) = true) _ (by omega_using [h16])))
    fun s₆ f₆ z₆ => WP.block_nil ?_
  obtain g₅ : s₅.gpr .r11 = BitVec.ofNat 32 (e + 1) := by
    rw [u₅.gpr, dpVal, k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), g₁]
    exact (BitVec.ofNat_add _ _).symm
  obtain k₅₆ : Rest [.r11] s₄ s₆ := (u₅.rest (by simp)).trans (f₆.rest _)
  obtain m₆ : s₆.mem = s₄.mem := by rw [f₆.mem, u₅.mem]
  obtain U₃₄ : Unch base (winTW c) s.mem s₄.mem :=
    unch_winTW_trans (unch_winTW (unch_winWr_pW (by decide) U₁'))
      (unch_winTW_trans (unch_winTW_entry he1 O₃) (unch_winTW (unch_winWr_slW (by decide) U₄)))
  obtain q₄ : ∀ i ∈ [RX, RY], sv c base s₄ i = sv c base s i := fun i hi => by
    have h45 : i < 45 := (by decide : ∀ i ∈ [RX, RY], i < 45) i hi
    have hle := sl_le c h7 h45
    have a₄ : sv c base s₄ i = sv c base s₃ i :=
      sv_unch U₄ h7 hn h45 (apart_slW ((by decide : ∀ i ∈ [RX, RY], i ∉ [DX, DY, DZ]) i hi))
    have a₃ : sv c base s₃ i = sv c base s₂ i := O₃.wordsVal
      (Or.inl (Nat.le_trans hle (Nat.le_trans hge
        (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))))
      (by omega_using [hle, hsz])
    have a₂ : sv c base s₂ i = sv c base s i := sv_pW U₁' h7 hn h45
      ((by decide : ∀ i ∈ [RX, RY], i ∉ [T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP]) i hi)
    rw [a₄, a₃, a₂]
  refine ⟨⟨ctx₄.same hc k₅₆ (by decide) m₆, by rw [f₆.gpr, g₅], ?_, ?_, ?_, fun i hi => ?_, fun i hi => ?_, ?_⟩, ?_⟩
  · exact (((((I.keep.trans (K₁.mono (by decide))).trans (k₂.mono (by decide))).trans
      (k₃.mono (by decide))).trans (k₄.mono (by decide))).trans (k₅₆.mono (by decide)))
  · rw [m₆]; exact unch_winTW_trans I.unch U₃₄
  · rw [m₆]
    exact tbl₃.unch (unch_winWr_slW (by decide) U₄)
      (by have := Nat.mul_le_mul_left (4 * (6 * c.n)) (show e + 1 + 1 ≤ 2 ^ c.winW from he1); omega_using [hfit, this])
      (below (by decide))
  · show wordsVal s₆.mem _ _ _ = _
    rw [m₆]; exact (q₄ i hi).trans (I.q i hi)
  · show wordsVal s₆.mem _ _ _ < _
    rw [m₆]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact lt_of_eq_of_lt ex₄ (L₁ _ (by decide))
    · exact lt_of_eq_of_lt ey₄ (L₁ _ (by decide))
    · exact lt_of_eq_of_lt ez₄ (L₁ _ (by decide))
  · show Rep _ (toM _ _ (wordsVal s₆.mem _ _ _)) (toM _ _ (wordsVal s₆.mem _ _ _))
      (toM _ _ (wordsVal s₆.mem _ _ _)) _
    rw [m₆]
    show Rep _ (toM _ _ (sv c base s₄ DX)) (toM _ _ (sv c base s₄ DY)) (toM _ _ (sv c base s₄ DZ)) _
    rw [ex₄, ey₄, ez₄]; exact repT₁
  · rw [z₆, g₅]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    change BitVec.ofNat 32 (e + 1) - BitVec.ofNat 32 (2 ^ c.winW - 1) = 0#32 ↔ e + 1 = 2 ^ c.winW - 1
    rw [TComb.sub_zero_iff, TComb.ofNat32_eq (by omega_using [he1, h16]) (by omega_using [h16])]

/-- `winBuild`: the table holds `[e]P` for every `e < 2^w`, for the affine
point `P` in `R`'s first two slots. -/
theorem winBuild_ok (hc : CfgOk c) (hC : Law c.C) {base : Addr} {P : Point c.C} (hP : onCurve c.C P = true)
    {k : Nat} {s : State} (ctx : WinCtx c base k s) (hqx : sv c base s RX < c.C.p)
    (hqy : sv c base s RY < c.C.p) (hG : Rep c.C (fv c base s RX) (fv c base s RY) 1 P) :
    WP isa c.winBuild s fun s' => WinCtx c base k s' ∧ Rest powClob s s' ∧
      Unch base (winTW c) s.mem s'.mem ∧ TblOk c base P s'.mem (2 ^ c.winW) := by
  have h7 := hc.n10
  have hn := ctx.scr.nowrap
  have hfit := winTbl_fit hc.n10
  have hge := winTbl_ge c
  have hsz : size = 4096 := rfl
  have h8 : 8 ≤ 2 ^ c.winW := by rcases pow_winW c with h | h <;> rw [h] <;> decide
  have h24 : 4 * (6 * c.n) = 24 * c.n := by omega_using []
  rw [Cfg.winBuild]
  refine WP.seq ?_
  simp only [List.append_assoc]
  refine wp_farPtr (by omega_using [hfit]) (by decide) fun s₁ k₁ m₁ p₁ => ?_
  obtain ctx₁ := ctx.same hc k₁ (by decide) m₁
  obtain e₁ : ∀ i, sv c base s₁ i = sv c base s i := fun i => by show wordsVal s₁.mem _ _ _ = _; rw [m₁]
  -- `O`, entry 0.
  refine VG.Proof.X25519.Arm.WP.append (storeEntry_ok hc ctx₁.scr ctx₁.far (d := 0) (e := 0) p₁
    (by dsimp only [tblAt]; omega_using []) (by omega_using [h8]) (by omega_using [h7]) (by decide))
    fun s₂ ⟨ox, oy, oz, k₂, O₂⟩ => ?_
  rw [e₁] at ox oy oz
  obtain ctx₂ := ctx₁.next hc k₂ (by decide) O₂.unch (winW_tbl (by dsimp only [tblAt]; omega_using []))
  obtain far₂ : ∀ {i}, i < 45 → ∀ {e : Nat} {m m' : Mem}, Outside base (tblAt c e 0) (24 * c.n) m m' →
      wordsVal m' base (c.sl i) c.n = wordsVal m base (c.sl i) c.n := fun {i} hi {e} {m} {m'} O =>
    O.wordsVal (Or.inl (Nat.le_trans (sl_le c h7 hi) (Nat.le_trans hge
      (by dsimp only [tblAt]; omega_using []))))
      (by have := sl_le c h7 hi; omega_using [this, hsz])
  obtain tbl₂ : TblOk c base P s₂.mem (0 + 1) :=
    TblOk.store (m := s₁.mem) (fun _ h => absurd h (Nat.not_lt_zero _)) hc (by omega_using [h8]) O₂ ox oy oz
      (ctx.lt hc _ (by decide)) (ctx.lt hc _ (by decide)) (ctx.lt hc _ (by decide)) (by
        rw [mul_zero_pt]
        have h0 : toM c.C.p (2 ^ (64 * c.n)) (sv c base s ZERO) = 0 := ctx.fv_zero
        have h1 : toM c.C.p (2 ^ (64 * c.n)) (sv c base s ONEP) = 1 := ctx.fv_onep hc
        rw [h0, h1]; exact rep_infinity' hC)
  -- `Q`, entry 1.
  obtain p₂ : s₂.gpr .r5 = s₂.gpr .r12 + BitVec.ofNat 32 c.winTbl := by
    rw [k₂.gpr _ (by decide), k₂.gpr _ (by decide), p₁]
  refine VG.Proof.X25519.Arm.WP.append (storeEntry_ok hc ctx₂.scr ctx₂.far (d := 24 * c.n) (e := 1) p₂
    (by dsimp only [tblAt]; omega_using []) (by omega_using [h8]) (by omega_using [h7]) (by decide))
    fun s₃ ⟨qx, qy, qz, k₃, O₃⟩ => ?_
  obtain e₂ : ∀ {i}, i < 45 → sv c base s₂ i = sv c base s i := fun hi => (far₂ hi O₂).trans (e₁ _)
  rw [e₂ (i := RX) (by decide)] at qx
  rw [e₂ (i := RY) (by decide)] at qy
  rw [e₂ (i := ONEP) (by decide)] at qz
  obtain ctx₃ := ctx₂.next hc k₃ (by decide) O₃.unch (winW_tbl (by dsimp only [tblAt]; omega_using []))
  obtain repQ : Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX)) (toM c.C.p (2 ^ (64 * c.n)) (sv c base s RY))
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ONEP)) P := by
    have h1 : toM c.C.p (2 ^ (64 * c.n)) (sv c base s ONEP) = 1 := ctx.fv_onep hc
    rw [h1]; exact hG
  obtain tbl₃ : TblOk c base P s₃.mem (1 + 1) :=
    tbl₂.store hc (by omega_using [h8]) O₃ qx qy qz hqx hqy (ctx.lt hc _ (by decide)) (by
      rw [mul_one_pt]; exact repQ)
  obtain e₃ : ∀ {i}, i < 45 → sv c base s₃ i = sv c base s i := fun hi => (far₂ hi O₃).trans (e₂ hi)
  -- `D = Q`.
  refine VG.Proof.X25519.Arm.WP.append (copySlots_ok hc ctx₃.scr (o₁ := DX) (o₂ := DY) (o₃ := DZ)
    (a₁ := RX) (a₂ := RY) (a₃ := ONEP) (by decide) (by decide) (by decide))
    fun s₄ ⟨ex₄, ey₄, ez₄, k₄, U₄⟩ => ?_
  rw [e₃ (i := RX) (by decide)] at ex₄
  rw [e₃ (i := RY) (by decide)] at ey₄
  rw [e₃ (i := ONEP) (by decide)] at ez₄
  obtain ctx₄ := ctx₃.next hc k₄ (by decide) U₄ (winW_slW h7 (by decide))
  refine wp_mov (op2_imm (by decide)) fun s₅ u₅ => WP.block_nil ?_
  obtain K₅ : Rest powClob s s₅ := ((((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans
    (k₃.mono (by decide))).trans (k₄.mono (by decide))).trans (u₅.rest (by decide))
  obtain U₅ : Unch base (winTW c) s.mem s₅.mem := by
    rw [u₅.mem, ← m₁]
    exact unch_winTW_trans (unch_winTW_entry (by omega_using [h8]) O₂)
      (unch_winTW_trans (unch_winTW_entry (by omega_using [h8]) O₃)
        (unch_winTW (unch_winWr_slW (by decide) U₄)))
  obtain q₄ : ∀ i ∈ [RX, RY], sv c base s₄ i = sv c base s i := fun i hi =>
    (sv_unch U₄ h7 hn ((by decide : ∀ i ∈ [RX, RY], i < 45) i hi)
      (apart_slW ((by decide : ∀ i ∈ [RX, RY], i ∉ [DX, DY, DZ]) i hi))).trans
      (e₃ ((by decide : ∀ i ∈ [RX, RY], i < 45) i hi))
  -- The loop.
  refine upLoop_ok (Inv := fun e t => BuildInv c base P k s t e) (n := 2 ^ c.winW - 1) (i := 1)
    (fun e t _ he I => winBuildStep_ok hc hC hP hqx hqy hG he I)
    (fun t I => ⟨I.ctx, I.keep, I.unch, by have := I.tbl; rwa [Nat.sub_add_cancel (by omega_using [h8])] at this⟩)
    (by omega_using [h8]) ?_
  refine ⟨ctx₄.same hc (u₅.rest (ws := [.r11]) (by simp)) (by decide) u₅.mem, u₅.gpr, K₅, U₅, ?_,
    fun i hi => ?_, fun i hi => ?_, ?_⟩
  · rw [u₅.mem]
    exact tbl₃.unch U₄ (by
        have := Nat.mul_le_mul_left (4 * (6 * c.n)) (show 1 + 1 ≤ 2 ^ c.winW by omega_using [h8])
        omega_using [hfit, this]) (fun w hw => Or.inl (by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact Nat.le_trans (sl_le c h7 ((by decide : ∀ i ∈ [DX, DY, DZ], i < 45) i hi)) hge))
  · show wordsVal s₅.mem _ _ _ = _
    rw [u₅.mem]; exact q₄ i hi
  · show wordsVal s₅.mem _ _ _ < _
    rw [u₅.mem]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact lt_of_eq_of_lt ex₄ hqx
    · exact lt_of_eq_of_lt ey₄ hqy
    · exact lt_of_eq_of_lt ez₄ (ctx.lt hc _ (by decide))
  · show Rep _ (toM _ _ (wordsVal s₅.mem _ _ _)) (toM _ _ (wordsVal s₅.mem _ _ _))
      (toM _ _ (wordsVal s₅.mem _ _ _)) _
    rw [u₅.mem]
    show Rep _ (toM _ _ (sv c base s₄ DX)) (toM _ _ (sv c base s₄ DY)) (toM _ _ (sv c base s₄ DZ)) _
    rw [ex₄, ey₄, ez₄, mul_one_pt]; exact repQ

/-! ## The multiplication -/

/-- What `mulBody` writes: what the windows write, and the table of the
bits of `k`. -/
abbrev mulBW (c : Cfg) : List (Nat × Nat) := winTW c ++ [(bitsAt c.n 0, 64 * c.n)]

/-- `mulBody`: `R` holds, below `p`, a representative of `[k]P`, for the
affine point `P` of the curve in `R`'s first two slots and the number
`k < 2^(8 len)` at `K`'s slot; only `powClob` and `mulBW` change. -/
theorem mulBody_ok (hc : CfgOk c) (hC : Law c.C) {base : Addr} {s : State} (hs : Scr s base size)
    (hf : Far s base 8192) (hmp : sv c base s MP = c.C.p) (hap : sv c base s AP = c.mont c.C.a)
    (hb3 : sv c base s B3P = c.mont (3 * c.C.b)) (hzero : sv c base s ZERO = 0)
    (hone : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) (hqx : sv c base s RX < c.C.p)
    (hqy : sv c base s RY < c.C.p) {P : Point c.C} (hP : onCurve c.C P = true)
    (hG : Rep c.C (fv c base s RX) (fv c base s RY) 1 P) (hk : sv c base s K < 2 ^ (8 * c.C.len)) :
    WP isa c.mulBody s fun s' => Rest powClob s s' ∧ Unch base (mulBW c) s.mem s'.mem ∧
      sv c base s' MP = c.C.p ∧ (∀ i ∈ [RX, RY, RZ], sv c base s' i < c.C.p) ∧
      Rep c.C (fv c base s' RX) (fv c base s' RY) (fv c base s' RZ) (mul (sv c base s K) P) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hfit := winTbl_fit hc.n10
  obtain ⟨hJ1, hJ, -, hcover⟩ := winJ_bounds hc
  have hsz : size = 4096 := rfl
  rw [Cfg.mulBody]
  -- The table of `k`'s bits.
  refine WP.seq (WP.mono (tbl_bits_ok hc hs hf (i := K) (j := 0) (by decide) (by decide))
    fun s₁ ⟨T₁, K₁, O₁⟩ => ?_)
  obtain e₁ : ∀ {i}, i < 45 → sv c base s₁ i = sv c base s i := fun hi =>
    O₁.wordsVal (Or.inl (sl_below_bits c h7 hi 0 0)) (by have := sl_le c h7 hi; omega_using [this, hsz, hn])
  obtain ctx₁ : WinCtx c base (sv c base s K) s₁ :=
    ⟨⟨hs.of_rest K₁ (by decide), hf.of_rest K₁, (e₁ (by decide)).trans hmp, (e₁ (by decide)).trans hap,
      (e₁ (by decide)).trans hb3, (e₁ (by decide)).trans hzero, (e₁ (by decide)).trans hone⟩,
      fun t ht => T₁ t (Nat.lt_of_lt_of_le ht (scalarBits_le hc))⟩
  -- The table of the point's multiples.
  refine WP.seq (WP.mono (winBuild_ok hc hC hP ctx₁ (by rw [e₁ (by decide)]; exact hqx)
    (by rw [e₁ (by decide)]; exact hqy) (by
      show Rep _ (toM _ _ (sv c base s₁ RX)) (toM _ _ (sv c base s₁ RY)) _ _
      rw [e₁ (by decide), e₁ (by decide)]; exact hG)) fun s₂ ⟨ctx₂, K₂, U₂, tbl₂⟩ => ?_)
  -- `R = O`.
  refine WP.seq ?_
  refine VG.Proof.X25519.Arm.WP.append (copySlots_ok hc ctx₂.scr (o₁ := RX) (o₂ := RY) (o₃ := RZ)
    (a₁ := ZERO) (a₂ := ONEP) (a₃ := ZERO) (by decide) (by decide) (by decide))
    fun s₃ ⟨rx, ry, rz, k₃, U₃⟩ => ?_
  refine wp_mov (op2_imm ((by decide +kernel : ∀ x < 256, encodable (BitVec.ofNat 32 x) = true) _ hJ))
    fun s₄ u₄ => WP.block_nil ?_
  obtain k₃₄ : Rest [.r4, .r11] s₂ s₄ := (k₃.mono (by decide)).trans (u₄.rest (by decide))
  obtain U₃₄ : Unch base (slW c [RX, RY, RZ]) s₂.mem s₄.mem := by rw [u₄.mem]; exact U₃
  obtain ctx₄ := ctx₂.next hc k₃₄ (by decide) U₃₄ (winW_slW h7 (by decide))
  obtain e₄ : ∀ i, sv c base s₄ i = sv c base s₃ i := fun i => by show wordsVal s₄.mem _ _ _ = _; rw [u₄.mem]
  -- The windows.
  refine countLoop_ok (Inv := fun j t => WinInv c base P (sv c base s K) s₄ t j) (n := c.winJ)
    (fun j t h1 h2 I => winStep_ok hc hC hP hk h1 h2 I) (fun t I => ⟨?_, ?_, I.ctx.mp, I.lt, ?_⟩) hJ1 ?_
  · exact ⟨ctx₄, u₄.gpr, Rest.refl _ _, Unch.refl _ _ _,
      tbl₂.unch U₃₄ hfit (fun w hw => Or.inl (by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
        exact Nat.le_trans (sl_le c h7 ((by decide : ∀ i ∈ [RX, RY, RZ], i < 45) i hi)) (winTbl_ge c))),
      fun i hi => by
        rw [e₄]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl
        · rw [rx]; exact ctx₂.lt hc _ (by decide)
        · rw [ry]; exact ctx₂.lt hc _ (by decide)
        · rw [rz]; exact ctx₂.lt hc _ (by decide), by
      show Rep _ (toM _ _ (sv c base s₄ RX)) (toM _ _ (sv c base s₄ RY)) (toM _ _ (sv c base s₄ RZ)) _
      have h0 : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ ZERO) = 0 := ctx₂.fv_zero
      have h1 : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ ONEP) = 1 := ctx₂.fv_onep hc
      rw [e₄, e₄, e₄, rx, ry, rz, h0, h1,
        Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by decide) hcover)), mul_zero_pt]
      exact rep_infinity' hC⟩
  · exact (((K₁.mono (by decide)).trans K₂).trans (k₃₄.mono (by decide))).trans I.keep
  · have U₁ : Unch base (mulBW c) s.mem s₁.mem := O₁.unch.mono fun w hw => by
      rw [List.mem_singleton.mp hw]; exact List.mem_append_right _ List.mem_cons_self
    have U₂' : Unch base (mulBW c) s₁.mem s₂.mem := U₂.mono fun _ hw => List.mem_append_left _ hw
    have U₄ : Unch base (mulBW c) s₂.mem t.mem :=
      (unch_winTW (unch_winWr_trans (unch_winWr_slW (by decide) U₃₄) I.unch)).mono
        fun _ hw => List.mem_append_left _ hw
    exact ((U₁.trans U₂').trans U₄).mono fun _ hw =>
      (List.mem_append.mp hw).elim (fun h => (List.mem_append.mp h).elim id id) id
  · have := I.rep
    rwa [Nat.mul_zero, Nat.pow_zero, Nat.div_one] at this

end VG.Proof.Ecdsa.Arm
