module

public import VerifiedGarbage.Impl.Ecdsa.X86.Window
public import VerifiedGarbage.Proof.Ecdsa.X86.Stages
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.JacMul
public import VerifiedGarbage.Proof.Weierstrass.CombW
public import VerifiedGarbage.Proof.Weierstrass.CombDigitW
public import VerifiedGarbage.Proof.Weierstrass.X86.TCombOne
import VerifiedGarbage.Proof.Ecdsa.X86.Lays
import VerifiedGarbage.Proof.Ecdsa.X86.Flags
import VerifiedGarbage.Proof.Weierstrass.X86.TCombRcb
import VerifiedGarbage.Proof.Weierstrass.X86.NafAdjust
import VerifiedGarbage.Proof.Weierstrass.X86.NafTableIO
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Weierstrass.JacDbl0
import VerifiedGarbage.Proof.Weierstrass.JacDblA
import VerifiedGarbage.Proof.Weierstrass.JacDblAF
import VerifiedGarbage.Proof.Weierstrass.Rcb0
import VerifiedGarbage.Proof.Weierstrass.CombDigitTopW
import VerifiedGarbage.Proof.Weierstrass.Comb
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# `[k]P` by windows on x86 (32-bit): correctness

`Cfg.winMul px py` (`Impl/Ecdsa/X86/Window.lean`) leaves in `R` a
representative of `[k]P`, for the affine point `P` of the curve at the slots
`px`, `py` and the number `k < 2^(8 len)` whose bits are table 0
(`winMul_ok`), for any curve the code supports (`CfgOk`) whose group law the
proofs support (`Law`), as on 32-bit ARM (`Proof/Ecdsa/Arm/Window.lean`):

* the points: `w` doublings of `[m]P` are `[2^w m]P` (`dblPt_mul`), and a
  window takes `[k / 2^(w (j + 1))]P` to `[k / 2^(w j)]P` (`win_pt`);
* a field program of numbered operations on the slots of points (`ptOp_ok`,
  from `fprog_ok`), which the complete addition, the Jacobian doublings
  (`WinDblOk`: for the curve's `a`, `winDbl_ok`) and the changes of
  coordinates all are;
* `winQuad_ok`: `R = 2^w R`, the point at infinity as `(0 : 1 : 0)`;
* `winDigit_ok`: the window; `winSel_ok`: its entry of the table, into `T`,
  by the comb's scans (`selPassAt_ok`);
* `winBuild_ok`: the table holds `[e]P` for every `e < 2^w` (`TblOk`).

Everything the code keeps (the constants, the table of the scalar's bits) is
apart from what it writes (`WinW`, `WinCtx.next`).
-/

-- separate module: the windows' proofs cost more than their imports, and ECDH's and verification's
-- proofs both use them

@[expose] public section

namespace VG.Proof.Ecdsa.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

/-! ## The points -/

section
variable {C : Curve}

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

/-- A numbered slot a field program may name: not the modulus's, nor the
temporary one. -/
abbrev SlotOk (i : Nat) : Prop := i < 45 ∧ i ≠ MP ∧ i ≠ TMP

/-- A slot of a field program on the numbered slots `ids`. -/
abbrev winSl (c : Cfg) (ids : List Nat) (x : Nat) : Prop := x ∈ ids.map c.sl

theorem winLay (hc : CfgOk c) {ids : List Nat} (h : ∀ i ∈ ids, SlotOk i) : Lay c.MP' size (winSl c ids) :=
  lay_map hc rfl rfl rfl h

theorem winWk (hc : CfgOk c) {ids : List Nat} (h : ∀ i ∈ ids, SlotOk i) :
    WkOk c.SP c.MP' c.C.p size c.wk (winSl c ids) :=
  wkOk_map hc hc.fp rfl (jm := MP) (by decide) rfl rfl fun i hi => (h i hi).1

/-- What the slot `i` stands for. -/
abbrev fv (c : Cfg) (base : Addr) (s : State) (i : Nat) : Fe c.C := tmv c.C c.n base s (c.sl i)

/-- The ranges of the numbered slots `l`, of the field arithmetic's own
working space and of memory past the working space: what a field program
writing `l` may change. -/
abbrev pW (c : Cfg) (l : List Nat) : List (Nat × Nat) := slW c l ++ wkW c

/-- Where piece `j` of 8 bytes of entry `e` of the table is: coordinate `i`
is at `tblAt c e (c.n * i)`. -/
abbrev tblAt (c : Cfg) (e j : Nat) : Nat := c.winTbl + 16 * c.winPc * e + 8 * j

/-! ### What the windows write, and what they keep -/

/-- A range the windows' code writes: the temporary slot, within the slots
from 12 and the field arithmetic's own working space, or from the table
on. -/
def WinW (c : Cfg) (W : List (Nat × Nat)) : Prop :=
  ∀ w ∈ W, (w.1 = c.sl TMP ∧ w.2 = 8 * c.n) ∨ (c.sl 12 ≤ w.1 ∧ w.1 + w.2 ≤ 4096) ∨ c.winTbl ≤ w.1

theorem WinW.append {W W' : List (Nat × Nat)} (h : WinW c W) (h' : WinW c W') : WinW c (W ++ W') :=
  fun w hw => (List.mem_append.mp hw).elim (h w) (h' w)

theorem winTbl_eq (c : Cfg) : c.winTbl = 4096 + (64 * c.n + 4) * 3 := rfl

theorem winW_slW (h7 : c.n < 10) {l : List Nat} (hl : ∀ i ∈ l, i = TMP ∨ (12 ≤ i ∧ i < 45)) :
    WinW c (slW c l) := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  rcases hl i hi with h | ⟨h, h'⟩
  · exact Or.inl ⟨by rw [h], rfl⟩
  · refine Or.inr (Or.inl ⟨?_, ?_⟩)
    · rcases Nat.eq_or_lt_of_le h with h | h
      · rw [h]
      · exact Nat.le_trans (Nat.le_add_right _ _) (sl_lt c h)
    · have := sl_below_wk c h'
      have := wk_eq c
      dsimp only
      omega_arith

theorem winW_wk (h7 : c.n < 10) : WinW c (wkW c) := by
  intro w hw
  have h1 := sl_below_wk c (i := 12) (by decide)
  have h2 := wk_own c
  have h3 := winTbl_eq c
  simp only [wkW, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact Or.inr (Or.inl ⟨by dsimp only; omega_arith, by dsimp only; omega_arith⟩)
  · exact Or.inr (Or.inr (by dsimp only; omega_arith))

theorem winW_pW (h7 : c.n < 10) {l : List Nat} (hl : ∀ i ∈ l, i = TMP ∨ (12 ≤ i ∧ i < 45)) :
    WinW c (pW c l) := (winW_slW h7 hl).append (winW_wk h7)

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
  · have := sl_below_wk c (i := i) (by omega_using [hi])
    have := wk_eq c
    have := winTbl_eq c
    exact Or.inl (by omega_arith)

/-- A byte of a table of bits is apart from what the windows write. -/
theorem WinW.apart_bits {W : List (Nat × Nat)} (hW : WinW c W) (h7 : c.n < 10) {j t : Nat} (hj : j < 3)
    (ht : t < 64 * c.n) : ∀ w ∈ W, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  intro w hw
  rw [bitsAt_eq]
  obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega_using [hj]
  all_goals
    rcases hW w hw with ⟨h1, h2⟩ | ⟨-, h⟩ | h
    · rw [h1, h2]
      have := sl_below_wk c (i := TMP) (by decide)
      have := wk_eq c
      exact Or.inr (by omega_arith)
    · exact Or.inr (by omega_arith)
    · rw [winTbl_eq] at h
      exact Or.inl (by omega_arith)

/-- What the windows write misses the constants and the saved registers. -/
theorem WinW.fixedOk {W : List (Nat × Nat)} (hW : WinW c W) (h7 : c.n < 10) : FixedOk c W := by
  intro w hw
  rcases hW w hw with h | ⟨h, -⟩ | h
  · exact Or.inl h
  · exact Or.inr h
  · have := sl_below_wk c (i := 12) (by decide)
    have := wk_eq c
    have := winTbl_eq c
    exact Or.inr (by omega_arith)

/-- What the windows' code keeps throughout: the working space, the prime,
the constants of the formulas, and the table of the bits of `k`. -/
structure WinCtx (c : Cfg) (base : Addr) (k : Nat) (s : State) : Prop where
  scr : Scr s base size
  mp : sv c base s MP = c.C.p
  ap : sv c base s AP = c.mont c.C.a
  b3p : sv c base s B3P = c.mont (3 * c.C.b)
  zero : sv c base s ZERO = 0
  onep : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p
  bits : ∀ t < 8 * c.C.len, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0

/-- Code that keeps `edi` and `esp` and writes only what the windows write
keeps it. -/
theorem WinCtx.next {base : Addr} {k : Nat} {s s' : State} (h : WinCtx c base k s) (hc : CfgOk c)
    {rs : List Reg} (hr : Keeps rs s s') (hdi : .edi ∉ rs) (hsp : .esp ∉ rs) {W : List (Nat × Nat)}
    (hu : Unch base W s.mem s'.mem) (hW : WinW c W) : WinCtx c base k s' := by
  have h7 := hc.n10
  have hn := h.scr.nowrap
  have e : ∀ i, i < 12 → i ≠ TMP → sv c base s' i = sv c base s i := fun i hi hit =>
    sv_unch hu h7 hn (by omega_using [hi]) (hW.apart_const h7 hi hit)
  refine ⟨h.scr.of_keeps hr hdi hsp, (e MP (by decide) (by decide)).trans h.mp,
    (e AP (by decide) (by decide)).trans h.ap, (e B3P (by decide) (by decide)).trans h.b3p,
    (e ZERO (by decide) (by decide)).trans h.zero, (e ONEP (by decide) (by decide)).trans h.onep,
    fun t ht => ?_⟩
  have ht' : t < 64 * c.n := Nat.lt_of_lt_of_le ht (by have := hc.len_hi; omega_using [this])
  rw [tbl_unch hu h7 (j := 0) (by decide) ht' (hW.apart_bits h7 (by decide) ht'), h.bits t ht]

/-- Code that keeps `edi`, `esp` and the memory keeps what the windows keep. -/
theorem WinCtx.same {base : Addr} {k : Nat} {s s' : State} (h : WinCtx c base k s) (hc : CfgOk c)
    {rs : List Reg} (hr : Keeps rs s s') (hdi : .edi ∉ rs) (hsp : .esp ∉ rs) (hm : s'.mem = s.mem) :
    WinCtx c base k s' :=
  h.next hc hr hdi hsp (W := []) (by rw [hm]; exact Unch.refl _ _ _) (fun _ h => nomatch h)

theorem WinCtx.p_pos {base : Addr} {k : Nat} {s : State} (_ : WinCtx c base k s) (hc : CfgOk c) :
    0 < c.C.p := by
  have := hc.p_ge; omega_using [this]

/-- The constants are below `p`. -/
theorem WinCtx.lt {base : Addr} {k : Nat} {s : State} (h : WinCtx c base k s) (hc : CfgOk c) :
    ∀ i ∈ [AP, B3P, ZERO, ONEP], sv c base s i < c.C.p := by
  have hp := h.p_pos hc
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · rw [h.ap]; exact Nat.mod_lt _ hp
  · rw [h.b3p]; exact Nat.mod_lt _ hp
  · rw [h.zero]; exact hp
  · rw [h.onep]; exact Nat.mod_lt _ hp

theorem WinCtx.fv_ap {base : Addr} {k : Nat} {s : State} (h : WinCtx c base k s) (hc : CfgOk c) :
    fv c base s AP = Fin.ofNat c.C.p c.C.a := by
  show toM _ _ (sv c base s AP) = _; rw [h.ap]; exact toM_cmont hc _

theorem WinCtx.fv_b3p {base : Addr} {k : Nat} {s : State} (h : WinCtx c base k s) (hc : CfgOk c) :
    fv c base s B3P = Fin.ofNat c.C.p (3 * c.C.b) := by
  show toM _ _ (sv c base s B3P) = _; rw [h.b3p]; exact toM_cmont hc _

theorem WinCtx.fv_zero {base : Addr} {k : Nat} {s : State} (h : WinCtx c base k s) : fv c base s ZERO = 0 := by
  show toM _ _ (sv c base s ZERO) = _; rw [h.zero]; exact toM_zero _ _

theorem WinCtx.fv_onep {base : Addr} {k : Nat} {s : State} (h : WinCtx c base k s) (hc : CfgOk c) :
    fv c base s ONEP = 1 := by
  show toM _ _ (sv c base s ONEP) = _; rw [h.onep]; exact toM_one (unitMod_pow_two hc.p_odd _)

/-- A numbered slot a field program does not write keeps its number. -/
theorem sv_pW {base : Addr} {l : List Nat} {m m' : Mem} (hu : Unch base (pW c l) m m') (h7 : c.n < 10)
    (hn : base.toNat + size ≤ 2 ^ 32) {i : Nat} (hi : i < 45) (hl : i ∉ l) :
    wordsVal m' base (c.sl i) c.n = wordsVal m base (c.sl i) c.n :=
  sv_unch hu h7 hn hi (apart_append (apart_slW hl) (apart_wk hi))

/-! ## Field programs on the slots of points -/

/-- A field program of the numbered operations `N` (`ofN`) on the slots of
the points `p`, `q` and `o`, `o`'s apart from the others' and the
temporaries': `o` holds, below `p`, what `N` computes of what `a`, `3b`, `p`
and `q` hold; only the temporaries, `o`, the temporary slot and the field
arithmetic's own working space change. -/
theorem ptOp_ok (hc : CfgOk c) {N : List FOp} (hN : NumOk N) {p₁ p₂ p₃ q₁ q₂ q₃ o₁ o₂ o₃ : Nat}
    (hnd : [T0, T1, T2, T3, T4, T5, o₁, o₂, o₃].Nodup)
    (hap : ∀ i ∈ [AP, B3P, p₁, p₂, p₃, q₁, q₂, q₃], i ∉ [T0, T1, T2, T3, T4, T5, o₁, o₂, o₃])
    (hin : ∀ i ∈ [p₁, p₂, p₃, q₁, q₂, q₃, o₁, o₂, o₃], SlotOk i)
    {s : State} {base : Addr} (hs : Scr s base size) (hM : sv c base s MP = c.C.p)
    (hlt : ∀ i ∈ [AP, B3P, p₁, p₂, p₃, q₁, q₂, q₃], sv c base s i < c.C.p) :
    WP isa (fprog c.SP (ofN N c.rcbSlots (c.pt p₁ p₂ p₃) (c.pt q₁ q₂ q₃) (c.pt o₁ o₂ o₃))) s fun s' =>
      Keeps clob s s' ∧
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
  obtain hids : ∀ i ∈ [T0, T1, T2, T3, T4, T5, o₁, o₂, o₃] ++ [AP, B3P, p₁, p₂, p₃, q₁, q₂, q₃], SlotOk i := by
    intro i hi
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hi hin
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | h | h | h | rfl | rfl | h | h | h | h | h | h
    all_goals first | decide | exact hin i (by simp only [h, true_or, or_true])
  obtain hSl : ∀ x ∈ rcbW c.rcbSlots (c.pt o₁ o₂ o₃) ++ rcbR c.rcbSlots (c.pt p₁ p₂ p₃) (c.pt q₁ q₂ q₃),
      winSl c ([T0, T1, T2, T3, T4, T5, o₁, o₂, o₃] ++ [AP, B3P, p₁, p₂, p₃, q₁, q₂, q₃]) x := fun x hx => hx
  obtain I : Inv c.MP' base size c.C.p
      (winSl c ([T0, T1, T2, T3, T4, T5, o₁, o₂, o₃] ++ [AP, B3P, p₁, p₂, p₃, q₁, q₂, q₃]))
      (rcbR c.rcbSlots (c.pt p₁ p₂ p₃) (c.pt q₁ q₂ q₃))
      (tmv c.C c.n base s) s :=
    ⟨hs, modP_of hc hM, fun x hx => hSl x (List.mem_append_right _ hx), fun x hx => by
      have hx' : x ∈ [AP, B3P, p₁, p₂, p₃, q₁, q₂, q₃].map c.sl := hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
      exact hlt i hi, fun _ _ => rfl⟩
  refine WP.mono (fprog_ok (winLay hc hids) (winWk hc hids) (unitMod_pow_two hc.p_odd (64 * c.n)) _ I
    (fun op hop x hx => hSl x (ofN_slots op hop x hx)) (ofN_readsOk hN _ _ _ _)) fun s' ⟨hk, I'⟩ => ?_
  obtain hval : ∀ x ∈ [(c.pt o₁ o₂ o₃).x, (c.pt o₁ o₂ o₃).y, (c.pt o₁ o₂ o₃).z],
      x ∈ validAfter (ofN N c.rcbSlots (c.pt p₁ p₂ p₃) (c.pt q₁ q₂ q₃) (c.pt o₁ o₂ o₃))
        (rcbR c.rcbSlots (c.pt p₁ p₂ p₃) (c.pt q₁ q₂ q₃)) := fun x hx => by
    rw [mem_validAfter]; exact Or.inr (ofN_out_mem hN hx)
  refine ⟨hk.keeps, ?_, fun i hi => ?_, ?_⟩
  · obtain hk' : ProgKeep c.MP' base c.wk (rcbW c.rcbSlots (c.pt o₁ o₂ o₃)) s s' := hk.mono fun w hw => by
      obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
      exact ofN_out hN op hop
    refine hk'.unch.mono fun w hw => ?_
    · have hw' : w ∈ ([T0, T1, T2, T3, T4, T5, o₁, o₂, o₃].map c.sl).map (·, 8 * c.n) ++
          [(c.sl TMP, 8 * c.n), (c.wk, 64 * c.n), Mont.outW] := hw
      simp only [pW, slW, wkW, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hw' ⊢
      rcases hw' with h | h | h | h | h | h | h | h | h | h | h | h <;> simp only [h, true_or, or_true]
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
theorem WinCtx.lt8 {base : Addr} {k : Nat} {s : State} (h : WinCtx c base k s) (hc : CfgOk c)
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

theorem WinCtx.lt_zero {base : Addr} {k : Nat} {s : State} (h : WinCtx c base k s) (hc : CfgOk c) :
    ∀ i ∈ [ZERO, ZERO, ZERO], sv c base s i < c.C.p := fun i hi => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hi
  rw [hi]; exact h.lt hc _ (by decide)

theorem edi_clob : Reg.edi ∉ clob := by decide
theorem esp_clob : Reg.esp ∉ clob := by decide
theorem esi_clob : Reg.esi ∉ clob := by decide

/-- `k` doublings from the Jacobian point in `D` (`b`) or `T`, and back to
projective coordinates: `R` holds `(XZ : Y : Z³)` for a Jacobian triple of
`2^k Q`. -/
theorem winDbls_ok (hc : CfgOk c) (hC : Law c.C) {base : Addr} {kk : Nat} :
    ∀ (k : Nat) (b : Bool) {s : State} {Q : Point c.C}, WinCtx c base kk s → onCurve c.C Q = true →
    (∀ i ∈ [(wpt b).1, (wpt b).2.1, (wpt b).2.2], sv c base s i < c.C.p) →
    InvJ c.C (fv c base s (wpt b).1) (fv c base s (wpt b).2.1) (fv c base s (wpt b).2.2) Q →
    WP isa (c.winDbls k (c.pt (wpt b).1 (wpt b).2.1 (wpt b).2.2)
        (c.pt (wpt !b).1 (wpt !b).2.1 (wpt !b).2.2)) s fun s' =>
      Keeps clob s s' ∧ Unch base (pW c winWr) s.mem s'.mem ∧
      (∀ i ∈ [RX, RY, RZ], sv c base s' i < c.C.p) ∧
      ∃ X Y Z : Fe c.C, InvJ c.C X Y Z (dblPt Q k) ∧ fv c base s' RX = X * Z ∧ fv c base s' RY = Y ∧
        fv c base s' RZ = Z * Z * Z
  | 0, b, s, Q, ctx, _, hlt, hJ => by
    rw [Cfg.winDbls, Cfg.zeroPt, fromJ_eq]
    refine WP.mono (ptOp_ok hc fromJN_ok (q₁ := ZERO) (q₂ := ZERO) (q₃ := ZERO) (o₁ := RX) (o₂ := RY)
      (o₃ := RZ) (by decide) (by cases b <;> decide) (by cases b <;> decide) ctx.scr ctx.mp
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
      (by cases b <;> decide) ctx.scr ctx.mp (ctx.lt8 hc hlt hlt)) fun s₁ ⟨K₁, U₁, L₁, V₁⟩ => ?_)
    obtain ctx₁ := ctx.next hc K₁ edi_clob esp_clob U₁ (winW_pW hc.n10 (by cases b <;> decide))
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
theorem winQuadN_ok (hc : CfgOk c) (hC : Law c.C) (w : Nat) {base : Addr} {kk : Nat} {s : State}
    (ctx : WinCtx c base kk s) {Q : Point c.C} (hQ : onCurve c.C Q = true)
    (hlt : ∀ i ∈ [RX, RY, RZ], sv c base s i < c.C.p)
    (hR : Rep c.C (fv c base s RX) (fv c base s RY) (fv c base s RZ) Q) :
    WP isa (c.winQuadN w) s fun s' => Keeps clob s s' ∧ Unch base (pW c winWr) s.mem s'.mem ∧
      (∀ i ∈ [RX, RY, RZ], sv c base s' i < c.C.p) ∧
      Rep c.C (fv c base s' RX) (fv c base s' RY) (fv c base s' RZ) (dblPt Q w) := by
  have h7 := hc.n10
  have hn0 := hc.n0
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  rw [Cfg.winQuadN, Cfg.zeroPt, toJ_eq]
  -- To Jacobian coordinates, in `D`.
  refine WP.seq (WP.mono (ptOp_ok hc toJN_ok (p₁ := RX) (p₂ := RY) (p₃ := RZ) (q₁ := ZERO) (q₂ := ZERO)
    (q₃ := ZERO) (o₁ := DX) (o₂ := DY) (o₃ := DZ) (by decide) (by decide) (by decide) ctx.scr
    ctx.mp (ctx.lt8 hc hlt (ctx.lt_zero hc))) fun s₁ ⟨K₁, U₁, L₁, V₁⟩ => ?_)
  obtain ctx₁ := ctx.next hc K₁ edi_clob esp_clob U₁ (winW_pW h7 (by decide))
  obtain J₁ : InvJ c.C (fv c base s₁ DX) (fv c base s₁ DY) (fv c base s₁ DZ) Q :=
    InvJ.of_toJ hC hR ctx.fv_zero (V₁.trans (toJN_run _))
  -- The doublings, and back.
  refine WP.seq (WP.mono (winDbls_ok hc hC w true ctx₁ hQ L₁ J₁)
    fun s₂ ⟨K₂, U₂, L₂, X, Y, Z, J₂, rx₂, ry₂, rz₂⟩ => ?_)
  obtain ctx₂ := ctx₁.next hc K₂ edi_clob esp_clob U₂ (winW_winWr h7)
  have hs₂ := ctx₂.scr
  have hn := hs₂.nowrap
  -- `Y = 1` where `Z = 0`.
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (nonzero_ok c hs₂ hn0 (sl_le c h7 (i := RZ) (by decide)))
    fun s₃ ⟨g₃, k₃, m₃⟩ => ?_)
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₄ u₄ => ?_
  obtain k₄ : Keeps [.ecx, .edx] s₂ s₄ := k₃.widen u₄.keeps
  obtain m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, m₃]
  have hRY := sl_le c h7 (i := RY) (by decide)
  have hONE := sl_le c h7 (i := ONEP) (by decide)
  have h15 := sl_lt c (i := ONEP) (j := RY) (by decide)
  refine WP.mono (sel_ok (decide (sv c base s₂ RZ ≠ 0)) (2 * c.n) (hs₂.of_keeps k₄ (by decide))
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
  obtain K₅ : Keeps clob s₂ s₅ := (k₄.mono (by decide)).trans (k₅.mono (by decide))
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

/-- `winQuad`: `R = 2^winW R`. -/
theorem winQuad_ok (hc : CfgOk c) (hC : Law c.C) {base : Addr} {kk : Nat} {s : State}
    (ctx : WinCtx c base kk s) {Q : Point c.C} (hQ : onCurve c.C Q = true)
    (hlt : ∀ i ∈ [RX, RY, RZ], sv c base s i < c.C.p)
    (hR : Rep c.C (fv c base s RX) (fv c base s RY) (fv c base s RZ) Q) :
    WP isa c.winQuad s fun s' => Keeps clob s s' ∧ Unch base (pW c winWr) s.mem s'.mem ∧
      (∀ i ∈ [RX, RY, RZ], sv c base s' i < c.C.p) ∧
      Rep c.C (fv c base s' RX) (fv c base s' RY) (fv c base s' RZ) (dblPt Q c.winW) :=
  winQuadN_ok hc hC c.winW ctx hQ hlt hR

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

theorem winPc_le (h7 : c.n < 10) : 24 * c.n ≤ 16 * c.winPc ∧ 16 * c.winPc ≤ 24 * c.n + 8 ∧ c.winPc ≤ 14 := by
  unfold Cfg.winPc; omega_using [h7]

/-- The table is past the tables of bits, within the working space. -/
theorem winTbl_fit (h7 : c.n < 10) : c.winTbl + 16 * c.winPc * 2 ^ c.winW ≤ 8192 := by
  have hp := winPc_le h7
  rw [winTbl_eq]
  unfold Cfg.winW
  split
  · rename_i h6
    have : 16 * c.winPc * 2 ^ 4 = 16 * (16 * c.winPc) := by omega_arith
    omega_using [this, hp, h6]
  · have : 16 * c.winPc * 2 ^ 3 = 8 * (16 * c.winPc) := by omega_arith
    omega_using [this, hp, h7]

theorem winTbl_ge (c : Cfg) : 4096 ≤ c.winTbl := by
  rw [winTbl_eq]; exact Nat.le_add_right _ _

theorem pow_winW (c : Cfg) : 2 ^ c.winW = 16 ∨ 2 ^ c.winW = 8 := by
  rcases winW_cases c with h | h <;> rw [h]
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem pow_winW_le (c : Cfg) : 2 ^ c.winW ≤ 16 ∧ 8 ≤ 2 ^ c.winW := by
  rcases pow_winW c with h | h <;> omega_using [h]

/-- What a field program writes inside the working space is below the table,
and the rest is past the working space. -/
theorem pW_tbl (h7 : c.n < 10) {l : List Nat} (hl : ∀ i ∈ l, i < 45) {cnt : Nat}
    (hfit : c.winTbl + 16 * c.winPc * cnt ≤ 8192) :
    ∀ w ∈ pW c l, w.1 + w.2 ≤ c.winTbl ∨ c.winTbl + 16 * c.winPc * cnt ≤ w.1 := by
  intro w hw
  have hge := winTbl_ge c
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have := sl_below_wk c (hl i hi)
    have := wk_eq c
    exact Or.inl (by dsimp only; omega_arith)
  · have := wk_own c
    simp only [wkW, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact Or.inl (by dsimp only; omega_arith)
    · exact Or.inr hfit

/-! ## The table -/

/-- The first `cnt` entries of the table are, below `p`, representatives of
`[e]P`. -/
def TblOk (c : Cfg) (base : Addr) (P : Point c.C) (m : Mem) (cnt : Nat) : Prop :=
  ∀ e < cnt, (∀ j < 3, wordsVal m base (tblAt c e (c.n * j)) c.n < c.C.p) ∧
    Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (wordsVal m base (tblAt c e (c.n * 0)) c.n))
      (toM c.C.p (2 ^ (64 * c.n)) (wordsVal m base (tblAt c e (c.n * 1)) c.n))
      (toM c.C.p (2 ^ (64 * c.n)) (wordsVal m base (tblAt c e (c.n * 2)) c.n)) (mul e P)

/-- A coordinate of an entry apart from what changed. -/
theorem winTbl_unch {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (hu : Unch base W m m') {cnt e j : Nat}
    (h7 : c.n < 10) (he : e < cnt) (hj : j < 3) (hfit : c.winTbl + 16 * c.winPc * cnt ≤ 8192)
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ c.winTbl ∨ c.winTbl + 16 * c.winPc * cnt ≤ w.1) :
    wordsVal m' base (tblAt c e (c.n * j)) c.n = wordsVal m base (tblAt c e (c.n * j)) c.n := by
  have hp := winPc_le h7
  have hmul := Nat.mul_le_mul_left (16 * c.winPc) (Nat.succ_le_of_lt he)
  rw [Nat.mul_succ] at hmul
  have hj2 : c.n * j ≤ c.n * 2 := Nat.mul_le_mul_left _ (by omega_using [hj])
  refine hu.wordsVal (fun w hw => ?_) (by dsimp only [tblAt]; omega_using [hmul, hfit, hj2, hp])
  rcases hW w hw with h | h
  · exact Or.inr (by dsimp only [tblAt]; omega_using [h])
  · exact Or.inl (by dsimp only [tblAt]; omega_using [h, hmul, hj2, hp])

theorem TblOk.unch {base : Addr} {P : Point c.C} {W : List (Nat × Nat)} {m m' : Mem} {cnt : Nat}
    (h : TblOk c base P m cnt) (h7 : c.n < 10) (hu : Unch base W m m')
    (hfit : c.winTbl + 16 * c.winPc * cnt ≤ 8192)
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ c.winTbl ∨ c.winTbl + 16 * c.winPc * cnt ≤ w.1) :
    TblOk c base P m' cnt := by
  intro e he
  obtain ⟨hl, hr⟩ := h e he
  refine ⟨fun j hj => by rw [winTbl_unch hu h7 he hj hfit hW]; exact hl j hj, ?_⟩
  rw [winTbl_unch hu h7 he (by decide) hfit hW, winTbl_unch hu h7 he (by decide) hfit hW,
    winTbl_unch hu h7 he (by decide) hfit hW]
  exact hr

/-! ## The window -/

/-- `eax` is the `cnt` low bits of window `j` of the number whose bits are
the bytes at `bits`, for `j` in `esi`. -/
theorem winBits_ok {s : State} {base : Addr} (hs : Scr s base size) {w bits k j cnt N : Nat}
    (hw : w < 9) (hc : cnt ≤ w) (hj : w * j + cnt ≤ N) (hj32 : j < 2 ^ 32) (hN : bits + N ≤ size)
    (hx : s.gpr .esi = BitVec.ofNat 32 j)
    (hbits : ∀ t < N, s.mem (off base (bits + t)) = if k.testBit t then 1 else 0)
    (hwin : hornerVal (fun i => (k.testBit (w * j + i)).toNat) 0 cnt = combWin w k j) :
    WP isa (.block (winIndex w ++ hornerBits bits cnt)) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (combWin w k j) ∧ CKeeps [.eax, .ecx, .edx] s t := by
  have hn := hs.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (winIndex_ok s (by omega_arith) hj32 hx) fun a ⟨a1, ka⟩ => ?_
  have hv : ∀ i, (fun t => (k.testBit (w * j + (t - bits))).toNat) i ≤ 1 := fun _ => Bool.toNat_le _
  refine WP.mono (hornerBits_ok hv cnt bits (s := a) (by omega_arith) fun i hi => ?_)
    fun b ⟨b2, kb⟩ => ?_
  · have he : a.ea (winByte (bits + i)) = off base (bits + (w * j + i)) := by
      rw [ea_winByte (hs.of_keeps ka.keeps (by decide)) (by rw [ka.1 .edi (by decide)]; exact a1) (by omega_arith)]
      exact congrArg (off base) (by omega_arith)
    refine ⟨by rw [he]; exact ⟨_, List.mem_append_right _ (ka.2.2.2 ▸ hs.wr), Scr.contains hs.nowrap (by omega_arith)⟩, ?_⟩
    rw [he, ka.2.1, hbits _ (by omega_arith), show bits + i - bits = i by omega_arith]
    cases k.testBit (w * j + i) <;> rfl
  · have hw' : hornerVal (fun t => (k.testBit (w * j + (t - bits))).toNat) bits cnt = combWin w k j := by
      rw [← hwin]
      exact hornerVal_congr fun i _ => by
        simp only [show bits + i - bits = i by omega_arith, Nat.zero_add]
    exact ⟨by rw [b2, hw'], (ka.mono (by decide)).trans (kb.mono (by decide))⟩

theorem winScan_J (c : Cfg) : c.winScan.J = c.winJ := rfl

theorem winScan_H (c : Cfg) : c.winScan.H = 2 ^ c.winW := by
  show 2 ^ (c.winW + 1 - 1) = _
  rw [Nat.add_sub_cancel]

/-- `winDigit`: `ebx` is window `j` of `k`, plus one, for `j` in `esi`. -/
theorem winDigit_ok (hc : CfgOk c) {base : Addr} {k : Nat} {s : State} (ctx : WinCtx c base k s)
    (hk : k < 2 ^ (8 * c.C.len)) {j : Nat} (hj : j < c.winJ) (gj : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa c.winDigit s fun t =>
      t.gpr .ebx = BitVec.ofNat 32 (combWin c.winW k j + 1) ∧ CKeeps [.eax, .ebx, .ecx, .edx] s t := by
  obtain ⟨hJ1, hJ, hstart, hcover⟩ := winJ_bounds hc
  have h7 := hc.n10
  have hlen := hc.len_hi
  have hw : c.winW < 9 := by rcases winW_cases c with h | h <;> rw [h] <;> decide
  have bounds := windowBits_bounds (w := c.winW) (J := c.winJ) (bits := 8 * c.C.len) hj hstart hcover
  dsimp only at bounds
  have hbit0 := bitsAt_le c h7 (j := 0) (by decide)
  have fin : ∀ t, (t.gpr .eax = BitVec.ofNat 32 (combWin c.winW k j) ∧ CKeeps [.eax, .ecx, .edx] s t) →
      WP isa (.block [.mov .ebx (.reg .eax), .alu .add .ebx (.imm 1)]) t fun u =>
        u.gpr .ebx = BitVec.ofNat 32 (combWin c.winW k j + 1) ∧ CKeeps [.eax, .ebx, .ecx, .edx] s u :=
    fun t ⟨v, kt⟩ => by
      refine wp_mov fun t₁ u₁ => wp_addS rfl fun t₂ u₂ _ => WP.block_nil ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
      · rw [u₂.gpr, u₁.gpr, v, BitVec.ofNat_add]; rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [u₂.other _ hr.2.1, u₁.other _ hr.2.1, kt.1 _ (by simp [hr.1, hr.2.2.1, hr.2.2.2])]
      · rw [u₂.mem, u₁.mem, kt.2.1]
      · rw [u₂.rd, u₁.rd, kt.2.2.1]
      · rw [u₂.wr, u₁.wr, kt.2.2.2]
  unfold Cfg.winDigit
  refine WP.seq (WP.mono (topTest_ok c.winScan s (j := j) hj (by rw [winScan_J]; omega_using [hJ]) gj)
    fun s₁ ⟨z₁, k₁⟩ => ?_)
  rw [winScan_J] at z₁
  have hs₁ : Scr s₁ base size := ctx.scr.of_keeps k₁.keeps (by decide)
  have hx₁ : s₁.gpr .esi = BitVec.ofNat 32 j := by rw [k₁.1 _ List.not_mem_nil, gj]
  have hb₁ : ∀ t < 8 * c.C.len, s₁.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by rw [k₁.2.1]; exact ctx.bits t ht
  have hcl : ∀ r ∈ ([] : List Reg), r ∈ [Reg.eax, .ecx, .edx] := fun _ h => nomatch h
  refine WP.seq ?_
  refine WP.ite (decide (j = c.winJ - 1)) z₁ (fun h => ?_) (fun h => ?_)
  · have hjt : j = c.winJ - 1 := of_decide_eq_true h
    rw [ite_eq_left hjt] at bounds
    refine WP.mono (winBits_ok hs₁ (k := k) (j := j) (cnt := c.winTop) (N := 8 * c.C.len) hw bounds.1
      bounds.2.1 (by omega_using [hj, hJ]) (by omega_using [hbit0, hlen]) hx₁ hb₁
      (window_without_padding bounds.1 bounds.2.2 hk)) fun t ⟨a, kt⟩ => fin t ⟨a, (k₁.mono hcl).trans kt⟩
  · have hjt : j ≠ c.winJ - 1 := of_decide_eq_false h
    rw [ite_eq_right hjt] at bounds
    refine WP.mono (winBits_ok hs₁ (k := k) (j := j) (cnt := c.winW) (N := 8 * c.C.len) hw bounds.1
      bounds.2.1 (by omega_using [hj, hJ]) (by omega_using [hbit0, hlen]) hx₁ hb₁
      (window_without_padding bounds.1 bounds.2.2 hk)) fun t ⟨a, kt⟩ => fin t ⟨a, (k₁.mono hcl).trans kt⟩

/-! ## The scan of the table -/

/-- The pieces of an entry of a table in the working space are the same after
a change of the working space below the table. -/
theorem accVal_inside {mem mem' : Mem} {base : Addr} {o len tbl n a H p : Nat}
    (hO : Outside base o len mem mem') (hp : p < n) (hsep : o + len ≤ tbl) (hfit : tbl + 16 * n * H < 2 ^ 64) :
    accVal mem' (off base tbl) n a H p = accVal mem (off base tbl) n a H p := by
  unfold accVal
  split
  next h =>
    refine Mem.readW_congr fun b hb => ?_
    have h1 := Nat.mul_le_mul_left (16 * n) (show a - 1 + 1 ≤ H by omega_using [h])
    rw [Nat.mul_add, Nat.mul_one] at h1
    rw [off, Offset.add_add, Offset.add_add]
    refine hO _ (Or.inr ?_)
    rw [ofs_off0 base (by omega_using [h1, hp, hb, hfit])]
    omega_using [hsep]
  next => rfl

theorem off_toNat {base : Addr} {d : Nat} (h : base.toNat + d < 2 ^ 64) : (off base d).toNat = base.toNat + d := by
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_using [h]

/-- `winTblPtr`: `edx` is the table's address. -/
theorem winTblPtr_ok {s : State} {base : Addr} (hs : Scr s base size) (ht : c.winTbl < size) :
    WP isa (.block c.winTblPtr) s fun t =>
      (t.gpr .edx).setWidth 64 = off base c.winTbl ∧ CKeeps [.edx] s t := by
  refine wp_mov fun s₁ u₁ => wp_addS rfl fun s₂ u₂ _ => WP.block_nil ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [u₂.gpr, u₁.gpr]
    exact hs.ea ht
  · simp only [List.mem_singleton] at hr
    rw [u₂.other _ hr, u₁.other _ hr]
  · rw [u₂.mem, u₁.mem]
  · rw [u₂.rd, u₁.rd]
  · rw [u₂.wr, u₁.wr]

theorem sl_T (c : Cfg) (j : Nat) : c.sl (TX + j) = c.sl TX + 8 * (c.n * j) := by
  rw [sl_eq, sl_eq, Nat.mul_add, Nat.add_assoc, Nat.mul_assoc 8 c.n j]

/-- `T`'s pieces are below the field arithmetic's own working space. -/
theorem selE_le (h7 : c.n < 10) : c.sl TX + 16 * c.winPc ≤ 4096 - 64 * c.n := by
  have hp := winPc_le h7
  have h1 := sl_below_wk c (i := T0) (by decide)
  have h2 := wk_eq c
  have h3 := sl_T c 3
  have : c.sl (TX + 3) = c.sl T0 := rfl
  omega_arith

/-- The scans of the table from pass `i`: the pieces of the entry `a` (from
1) into `T`, six to a pass. -/
theorem winPasses_ok {base : Addr} {a : Nat} (ha : a < 2 ^ 31) (h7 : c.n < 10) {s₀ : State}
    (hs₀ : Scr s₀ base size) (g8 : s₀.gpr .ebx = BitVec.ofNat 32 a)
    (gx : (s₀.gpr .edx).setWidth 64 = off base c.winTbl) :
    ∀ (k i : Nat) {s : State}, 6 * (i + k) < c.winPc + 6 → KeepRegs [.ecx] s₀ s →
      Outside base (c.sl TX) (16 * c.winPc) s₀.mem s.mem →
      (∀ p < min (6 * i) c.winPc, s.mem.readW (off base (c.sl TX + 16 * p)) 128 =
        accVal s₀.mem (off base c.winTbl) c.winPc a (2 ^ c.winW) p) →
      WP isa (.block (c.winPasses k i)) s fun t =>
        KeepRegs [.ecx] s₀ t ∧ Outside base (c.sl TX) (16 * c.winPc) s₀.mem t.mem ∧
        ∀ p < min (6 * (i + k)) c.winPc, t.mem.readW (off base (c.sl TX + 16 * p)) 128 =
          accVal s₀.mem (off base c.winTbl) c.winPc a (2 ^ c.winW) p
  | 0, i, s, _, K, O, hpc => WP.block_nil ⟨K, O, hpc⟩
  | k + 1, i, s, hk, K, O, hpc => by
    have hn := hs₀.nowrap
    have hsz : size = 8192 := rfl
    have hfit := winTbl_fit (c := c) h7
    have hge := winTbl_ge c
    have hE := selE_le (c := c) h7
    have hH : c.winScan.H = 2 ^ c.winW := winScan_H c
    have h16 := (pow_winW_le c).1
    have hs : Scr s base size := hs₀.of_keeps K (by decide)
    have hi : 6 * i < c.winPc := by omega_using [hk]
    rw [Cfg.winPasses, WP.block_append_iff]
    refine WP.mono (selPassAt_ok c.winScan hs (X := off base c.winTbl) (a := a) (c₀ := 6 * i)
      (cnt := min 6 (c.winPc - 6 * i)) (Nat.min_le_left _ _)
      (show 6 * i + min 6 (c.winPc - 6 * i) ≤ c.winPc by omega_using [hi])
      (by rw [hH]; omega_using [h16]) ha (by rw [K.1 _ (by decide), g8]) (by rw [K.1 _ (by decide), gx])
      (fun e he p hp => by
        rw [hH] at he
        have hmul := Nat.mul_le_mul_left (16 * c.winPc) (Nat.succ_le_of_lt he)
        rw [Nat.mul_succ] at hmul
        have hp' : p < c.winPc := hp
        rw [off, Offset.add_add]
        exact hs.read (d := c.winTbl + (16 * c.winPc * e + 16 * p)) (n := 16)
          (by show _ ≤ 8192; omega_using [hmul, hfit, hp']))
      (by rw [hH, off_toNat (by omega_using [hn, hfit, hsz])]; show _ + 16 * c.winPc * _ ≤ _; omega_using [hn, hfit, hsz])
      (show c.sl TX + 16 * c.winPc ≤ 8192 by omega_using [hE]))
      fun s₁ ⟨a₁, O₁, k₁⟩ => ?_
    rw [hH] at a₁
    change ∀ p < min 6 (c.winPc - 6 * i), s₁.mem.readW (off base (c.sl TX + 16 * (6 * i + p))) 128 =
      accVal s.mem (off base c.winTbl) c.winPc a (2 ^ c.winW) (6 * i + p) at a₁
    change Outside base (c.sl TX + 16 * (6 * i)) (16 * min 6 (c.winPc - 6 * i)) s.mem s₁.mem at O₁
    have ih := winPasses_ok ha h7 hs₀ g8 gx k (i + 1) (s := s₁) (by omega_using [hk]) (K.trans k₁)
      (O.trans (O₁.mono (Nat.le_add_right _ _) (by omega_using [hi]))) (fun p hp => by
        by_cases hlt : p < 6 * i
        · rw [O₁.read128 (Or.inl (by omega_using [hlt])) (by omega_using [hn, hE, hp, hsz])]
          exact hpc p (by omega_using [hlt, hp])
        · have := a₁ (p - 6 * i) (by omega_using [hlt, hp])
          rw [show 6 * i + (p - 6 * i) = p by omega_using [hlt]] at this
          rw [this]
          exact accVal_inside O (by omega_using [hp]) (by omega_using [hE, hge]) (by omega_using [hfit]))
    rw [show i + 1 + k = i + (k + 1) by omega_arith] at ih
    exact ih

/-- `winSel`: `T` holds entry `a` of the table, for `a + 1` in `ebx`. -/
theorem winSel_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    {a : Nat} (ha : a < 2 ^ c.winW) (ga : s.gpr .ebx = BitVec.ofNat 32 (a + 1)) :
    WP isa (.block c.winSel) s fun t =>
      (∀ j < 3, sv c base t (TX + j) = wordsVal s.mem base (tblAt c a (c.n * j)) c.n) ∧
      Keeps [.ecx, .edx] s t ∧ Outside base (c.sl TX) (16 * c.winPc) s.mem t.mem := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hfit := winTbl_fit (c := c) h7
  have hp := winPc_le (c := c) h7
  have h16 := (pow_winW_le c).1
  rw [Cfg.winSel, WP.block_append_iff]
  refine WP.mono (winTblPtr_ok hs (by show _ < 8192; rw [winTbl_eq]; omega_using [h7])) fun s₁ ⟨x₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁.keeps (by decide)
  refine WP.mono (winPasses_ok (a := a + 1) (by omega_using [ha, h16]) h7 hs₁
    (by rw [k₁.1 _ (by decide), ga]) x₁ ((c.winPc + 5) / 6) 0 (s := s₁) (by omega_arith) (Keeps.refl _ _)
    (Outside.refl _ _ _ _) (fun p hp => absurd hp (by omega_arith))) fun t ⟨K, O, V⟩ => ?_
  rw [k₁.2.1] at O V
  refine ⟨fun j hj => ?_, (k₁.keeps.mono (by decide)).trans (K.mono (by decide)), O⟩
  have W := accVal_word (fun p hp' => V p (by omega_using [hp']))
  show wordsVal t.mem base (c.sl (TX + j)) c.n = _
  rw [sl_T]
  refine wordsVal_congr₂ _ _ _ fun i hi => ?_
  have hmul : c.n * j ≤ c.n * 2 := Nat.mul_le_mul_left _ (by omega_using [hj])
  have := W (c.n * j + i) (by omega_using [hmul, hi, hp])
  rw [ite_eq_left (show 1 ≤ a + 1 ∧ a + 1 ≤ 2 ^ c.winW from ⟨Nat.le_add_left _ _, ha⟩), Nat.add_sub_cancel] at this
  have e : Mont.word s.mem (off base c.winTbl) (16 * c.winPc * a + 8 * (c.n * j + i)) =
      Mont.word s.mem base (tblAt c a (c.n * j) + 8 * i) := by
    show s.mem.readW (base + BitVec.ofNat 64 c.winTbl + BitVec.ofNat 64 _) 64 =
      s.mem.readW (base + BitVec.ofNat 64 _) 64
    rw [Offset.add_add]
    exact congrArg (fun d => s.mem.readW (base + BitVec.ofNat 64 d) 64) (by dsimp only [tblAt]; omega_arith)
  rw [show c.sl TX + 8 * (c.n * j) + 8 * i = c.sl TX + 8 * (c.n * j + i) by omega_arith, this, e]

/-! ## Copies of points, and the table's entries -/

/-- `o = a`, for points of numbered slots, `o`'s apart from each other and
from `a`'s. -/
theorem copySlots_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size)
    {o₁ o₂ o₃ a₁ a₂ a₃ : Nat} (h45 : ∀ i ∈ [o₁, o₂, o₃, a₁, a₂, a₃], i < 45) (hnd : [o₁, o₂, o₃].Nodup)
    (hoa : ∀ i ∈ [o₁, o₂, o₃], i ∉ [a₁, a₂, a₃]) :
    WP isa (.block (copyPt c.n (c.pt o₁ o₂ o₃) (c.pt a₁ a₂ a₃))) s fun s' =>
      sv c base s' o₁ = sv c base s a₁ ∧ sv c base s' o₂ = sv c base s a₂ ∧
      sv c base s' o₃ = sv c base s a₃ ∧ Keeps [.eax] s s' ∧ Unch base (slW c [o₁, o₂, o₃]) s.mem s'.mem := by
  have h7 := hc.n10
  have hn0 := hc.n0
  have inj : ∀ {i j : Nat}, c.sl i = c.sl j → i = j := fun h => sl_inj c hn0 h
  have hoa0 := hoa
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true, not_false_eq_true] at hnd
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, forall_eq_or_imp, forall_eq] at hoa h45
  obtain ⟨⟨n12, n13⟩, n23⟩ := hnd
  obtain ⟨⟨x1, x2, x3⟩, ⟨y1, y2, y3⟩, ⟨z1, z2, z3⟩⟩ := hoa
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := h45
  refine WP.mono (copyPt_ok hs (n := c.n) (o := c.pt o₁ o₂ o₃) (a := c.pt a₁ a₂ a₃) ?_ ?_ ?_ ?_)
    fun s' ⟨ex, ey, ez, k, U⟩ => ⟨ex, ey, ez, k, U⟩
  · intro d hd
    have hd' : d ∈ [o₁, o₂, o₃, a₁, a₂, a₃].map c.sl := hd
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> exact sl_le c h7 ‹_›
  · intro x hx y hy hxy
    have hx' : x ∈ [o₁, o₂, o₃].map c.sl := hx
    have hy' : y ∈ [o₁, o₂, o₃, a₁, a₂, a₃].map c.sl := hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx'
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy'
    exact sl_apart c fun h => hxy (h ▸ rfl)
  · intro x hx hy
    have hx' : x ∈ [o₁, o₂, o₃].map c.sl := hx
    have hy' : x ∈ [a₁, a₂, a₃].map c.sl := hy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    obtain ⟨j, hj, e⟩ := List.mem_map.mp hy'
    have := inj e
    subst this
    exact hoa0 _ hi hj
  · exact ⟨fun h => n12 (inj h), fun h => n13 (inj h), fun h => n23 (inj h)⟩

/-- An entry is within the table. -/
theorem tblAt_le (hc : CfgOk c) {e : Nat} (he : e < 2 ^ c.winW) : tblAt c e 0 + 16 * c.winPc ≤ 8192 := by
  have hfit := winTbl_fit (c := c) hc.n10
  have hmul := Nat.mul_le_mul_left (16 * c.winPc) (Nat.succ_le_of_lt he)
  rw [Nat.mul_succ] at hmul
  dsimp only [tblAt]; omega_using [hfit, hmul]

/-- `winEntryAddr`: `edx` is the address of entry `e` of the table, for `e`
in `esi`. -/
theorem winEntryAddr_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) {e : Nat}
    (he : e < 2 ^ c.winW) (ge : s.gpr .esi = BitVec.ofNat 32 e) :
    WP isa (.block c.winEntryAddr) s fun t =>
      (t.gpr .edx).setWidth 64 = off base (tblAt c e 0) ∧ CKeeps [.eax, .ecx, .edx] s t := by
  have hle := tblAt_le hc he
  have hp := winPc_le (c := c) hc.n10
  have hn0 := hc.n0
  unfold Cfg.winEntryAddr
  refine wp_mov fun s₁ u₁ => wp_movi fun s₂ u₂ => wp_mul fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_addS rfl fun s₅ u₅ _ => wp_addS rfl fun s₆ u₆ _ => WP.block_nil ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · have hm : s₃.gpr .eax = BitVec.ofNat 32 (16 * c.winPc * e) := by
      rw [u₃.eax, u₂.other _ (by decide), u₁.gpr, ge, u₂.gpr]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mul_comm]
    rw [u₆.gpr, u₅.gpr, u₄.gpr, u₅.other _ (by decide), u₄.other _ (by decide), hm,
      u₃.other _ (by decide) (by decide), u₂.other _ (by decide), u₁.other _ (by decide), Offset.add_add]
    exact hs.ea (d := tblAt c e 0) (by show _ < 8192; omega_using [hle, hp, hn0])
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other _ hr.2.2, u₅.other _ hr.2.2, u₄.other _ hr.2.2, u₃.other _ hr.1 hr.2.2, u₂.other _ hr.2.1,
      u₁.other _ hr.1]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-- `winStore`: entry `e` of the table holds `T`, for `e` in `esi`. -/
theorem winStore_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) {e : Nat}
    (he : e < 2 ^ c.winW) (ge : s.gpr .esi = BitVec.ofNat 32 e) :
    WP isa (.block c.winStore) s fun t =>
      (∀ j < 3, wordsVal t.mem base (tblAt c e (c.n * j)) c.n = sv c base s (TX + j)) ∧
      Keeps [.eax, .ecx, .edx] s t ∧ Outside base (tblAt c e 0) (16 * c.winPc) s.mem t.mem := by
  have h7 := hc.n10
  have hle := tblAt_le hc he
  have hp := winPc_le (c := c) h7
  have hE := selE_le (c := c) h7
  have hge := winTbl_ge c
  have hsz : size = 8192 := rfl
  rw [Cfg.winStore, WP.block_append_iff]
  refine WP.mono (winEntryAddr_ok hc hs he ge) fun s₁ ⟨x₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁.keeps (by decide)
  refine WP.mono (nafCopyPieces_ok (a := c.sl TX) (o := tblAt c e 0) c.winPc s₁ hs₁
    (by omega_using [hE, hsz]) (by omega_using [hle, hsz]) (Or.inr (by dsimp only [tblAt]; omega_using [hE, hge]))
    (fun i hi => hs₁.ea (by omega_using [hE, hsz, hi]))
    (fun i hi => nafTable_ea hs₁ x₁ (by omega_using [hle, hsz, hi]))) fun t ⟨et, ot, gt, rt, wt⟩ => ?_
  rw [k₁.2.1] at et ot
  refine ⟨fun j hj => ?_, ⟨fun r hr => by rw [gt, k₁.1 r hr], rt.trans k₁.2.2.1, wt.trans k₁.2.2.2⟩, ot⟩
  have W := nafCopy_words et
  show _ = wordsVal s.mem base (c.sl (TX + j)) c.n
  rw [sl_T]
  refine wordsVal_congr₂ _ _ _ fun i hi => ?_
  have hmul : c.n * j ≤ c.n * 2 := Nat.mul_le_mul_left _ (by omega_using [hj])
  have := W (c.n * j + i) (by omega_using [hmul, hi, hp])
  rw [show c.sl TX + 8 * (c.n * j) + 8 * i = c.sl TX + 8 * (c.n * j + i) by omega_arith, ← this]
  exact congrArg (fun d => t.mem.readW (base + BitVec.ofNat 64 d) 64) (by dsimp only [tblAt]; omega_arith)

/-- A point stored as entry `e` extends the table. -/
theorem TblOk.store {base : Addr} {P : Point c.C} {m m' : Mem} {e : Nat} (h : TblOk c base P m e)
    (hc : CfgOk c) (he : e < 2 ^ c.winW) (O : Outside base (tblAt c e 0) (16 * c.winPc) m m') {x y z : Nat}
    (hx : wordsVal m' base (tblAt c e (c.n * 0)) c.n = x) (hy : wordsVal m' base (tblAt c e (c.n * 1)) c.n = y)
    (hz : wordsVal m' base (tblAt c e (c.n * 2)) c.n = z) (lx : x < c.C.p) (ly : y < c.C.p) (lz : z < c.C.p)
    (hr : Rep c.C (toM c.C.p (2 ^ (64 * c.n)) x) (toM c.C.p (2 ^ (64 * c.n)) y)
      (toM c.C.p (2 ^ (64 * c.n)) z) (mul e P)) : TblOk c base P m' (e + 1) := by
  have hle := tblAt_le hc he
  intro e' he'
  rcases Nat.lt_succ_iff_lt_or_eq.mp he' with h' | rfl
  · exact h.unch hc.n10 O.unch (by dsimp only [tblAt] at hle; omega_using [hle]) (fun w hw => by
      rw [List.mem_singleton.mp hw]; exact Or.inr (by dsimp only [tblAt]; omega_using [])) e' h'
  · refine ⟨fun j hj => ?_, by rw [hx, hy, hz]; exact hr⟩
    obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega_using [hj]
    · rw [hx]; exact lx
    · rw [hy]; exact ly
    · rw [hz]; exact lz

/-- Everything the windows write: the slots, the field arithmetic's own
working space, and the table. -/
abbrev winTW (c : Cfg) : List (Nat × Nat) := pW c winWr ++ [(c.winTbl, 16 * c.winPc * 2 ^ c.winW)]

theorem unch_winTW {base : Addr} {m m' : Mem} (h : Unch base (pW c winWr) m m') : Unch base (winTW c) m m' :=
  h.mono fun _ hw => List.mem_append_left _ hw

/-- A store to an entry is within what the windows write. -/
theorem unch_winTW_entry {base : Addr} {m m' : Mem} {e : Nat} (he : e < 2 ^ c.winW)
    (O : Outside base (tblAt c e 0) (16 * c.winPc) m m') : Unch base (winTW c) m m' := by
  have hmul := Nat.mul_le_mul_left (16 * c.winPc) (Nat.succ_le_of_lt he)
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

/-- The entry selected to `T`, with the 8 bytes past it for an odd `n`, is
within what the windows write. -/
theorem unch_winWr_sel {base : Addr} {m m' : Mem} (h7 : c.n < 10)
    (O : Outside base (c.sl TX) (16 * c.winPc) m m') : Unch base (pW c winWr) m m' := by
  intro x hx
  have h0 := hx (c.sl TX, 8 * c.n) (slot_pW (by decide))
  have h1 := hx (c.sl TY, 8 * c.n) (slot_pW (by decide))
  have h2 := hx (c.sl TZ, 8 * c.n) (slot_pW (by decide))
  have h3 := hx (c.sl T0, 8 * c.n) (slot_pW (by decide))
  dsimp only at h0 h1 h2 h3
  have hp := winPc_le (c := c) h7
  have eX : c.sl TX = 64 + 8 * c.n * 20 := rfl
  have eY : c.sl TY = 64 + 8 * c.n * 21 := rfl
  have eZ : c.sl TZ = 64 + 8 * c.n * 22 := rfl
  have e0 : c.sl T0 = 64 + 8 * c.n * 23 := rfl
  exact O x (by omega_using [h0, h1, h2, h3, hp, eX, eY, eZ, e0])

theorem winW_sel (h7 : c.n < 10) : WinW c [(c.sl TX, 16 * c.winPc)] := fun w hw => by
  rw [List.mem_singleton.mp hw]
  have hE := selE_le (c := c) h7
  exact Or.inr (Or.inl ⟨Nat.le_trans (Nat.le_add_right _ _) (sl_lt c (i := 12) (j := TX) (by decide)),
    by dsimp only; omega_using [hE]⟩)

/-- A numbered slot the windows do not write is apart from what they write. -/
theorem apart_winTW (h7 : c.n < 10) {i : Nat} (hi : i < 45) (hl : i ∉ winWr) :
    ∀ w ∈ winTW c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  apart_append (apart_append (apart_slW hl) (apart_wk hi)) (fun w hw => by
    rw [List.mem_singleton.mp hw]
    have := sl_below_wk c hi
    have := wk_eq c
    have := winTbl_ge c
    exact Or.inl (by dsimp only; omega_arith))

/-- A numbered slot the windows do not write keeps its number. -/
theorem sv_winTW {base : Addr} {m m' : Mem} (hu : Unch base (winTW c) m m') (h7 : c.n < 10)
    (hn : base.toNat + size ≤ 2 ^ 32) {i : Nat} (hi : i < 45) (hl : i ∉ winWr) :
    wordsVal m' base (c.sl i) c.n = wordsVal m base (c.sl i) c.n :=
  sv_unch hu h7 hn hi (apart_winTW h7 hi hl)

/-! ## A window -/

theorem esi_powClob : ∀ r ∈ clob, r ∈ powClob := fun _ h => List.mem_cons_of_mem _ h

/-- The windows' invariant at `esi = j`: `R` represents `[k / 2^(w j)]P`,
below `p`, and the table holds the multiples of `P`. -/
structure WinInv (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s₀ s : State) (j : Nat) : Prop where
  ctx : WinCtx c base k s
  esi : s.gpr .esi = BitVec.ofNat 32 j
  keep : Keeps powClob s₀ s
  unch : Unch base (pW c winWr) s₀.mem s.mem
  tbl : TblOk c base P s.mem (2 ^ c.winW)
  lt : ∀ i ∈ [RX, RY, RZ], sv c base s i < c.C.p
  rep : Rep c.C (fv c base s RX) (fv c base s RY) (fv c base s RZ) (mul (k / 2 ^ (c.winW * j)) P)

/-- A window. -/
theorem winStep_ok (hc : CfgOk c) (hC : Law c.C) {base : Addr} {P : Point c.C} (hP : onCurve c.C P = true)
    {k : Nat} (hk : k < 2 ^ (8 * c.C.len)) {s₀ s : State} {j : Nat} (hj : 1 ≤ j) (hjn : j ≤ c.winJ)
    (I : WinInv c base P k s₀ s j) :
    WP isa c.winStep s fun s' => WinInv c base P k s₀ s' (j - 1) ∧ s'.zf = some (decide (j - 1 = 0)) := by
  have h7 := hc.n10
  obtain ⟨hJ1, hJ, -, -⟩ := winJ_bounds hc
  have hfit := winTbl_fit (c := c) hc.n10
  have hn := I.ctx.scr.nowrap
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega_using [hj]⟩
  rw [Nat.add_sub_cancel]
  have hQ := hC.onCurve_mul hP (k / 2 ^ (c.winW * (i + 1)))
  have below : ∀ {l : List Nat}, (∀ i ∈ l, i < 45) → ∀ w ∈ pW c l,
      w.1 + w.2 ≤ c.winTbl ∨ c.winTbl + 16 * c.winPc * 2 ^ c.winW ≤ w.1 :=
    fun hl => pW_tbl h7 hl hfit
  rw [Cfg.winStep]
  refine WP.seq (wp_decCounter hj I.esi fun s₁ g₁ k₁ m₁ => WP.block_nil ?_)
  rw [Nat.add_sub_cancel] at g₁
  obtain ctx₁ := I.ctx.same hc k₁ (by decide) (by decide) m₁
  -- `R = 2^w R`.
  refine WP.seq (WP.mono (winQuad_ok hc hC ctx₁ hQ
    (fun i hi => by show wordsVal s₁.mem _ _ _ < _; rw [m₁]; exact I.lt i hi)
    (by show Rep _ (toM _ _ (wordsVal s₁.mem _ _ _)) (toM _ _ (wordsVal s₁.mem _ _ _))
          (toM _ _ (wordsVal s₁.mem _ _ _)) _
        rw [m₁]; exact I.rep)) fun s₂ ⟨K₂, U₂, L₂, R₂⟩ => ?_)
  obtain ctx₂ := ctx₁.next hc K₂ edi_clob esp_clob U₂ (winW_winWr h7)
  obtain g₂ : s₂.gpr .esi = BitVec.ofNat 32 i := by rw [K₂.1 _ esi_clob, g₁]
  obtain U₂' : Unch base (pW c winWr) s.mem s₂.mem := by rw [← m₁]; exact U₂
  obtain tbl₂ : TblOk c base P s₂.mem (2 ^ c.winW) := I.tbl.unch h7 U₂' hfit (below (by decide))
  -- The window, and its entry.
  refine WP.seq (WP.mono (winDigit_ok hc ctx₂ hk (j := i) (by omega_using [hjn]) g₂) fun s₃ ⟨g₃, k₃⟩ => ?_)
  obtain m₃ : s₃.mem = s₂.mem := k₃.2.1
  obtain ctx₃ := ctx₂.same hc k₃.keeps (by decide) (by decide) m₃
  refine WP.seq (WP.mono (winSel_ok hc ctx₃.scr (combWin_lt _ _ _) g₃) fun s₄ ⟨V₄, k₄, O₄⟩ => ?_)
  obtain ctx₄ := ctx₃.next hc k₄ (by decide) (by decide) O₄.unch (winW_sel h7)
  rw [m₃] at V₄ O₄
  obtain U₄' : Unch base (pW c winWr) s₂.mem s₄.mem := unch_winWr_sel h7 O₄
  obtain ex₄ : sv c base s₄ TX = _ := V₄ 0 (by decide)
  obtain ey₄ : sv c base s₄ TY = _ := V₄ 1 (by decide)
  obtain ez₄ : sv c base s₄ TZ = _ := V₄ 2 (by decide)
  obtain ⟨tl, tr⟩ := tbl₂ (combWin c.winW k i) (combWin_lt _ _ _)
  obtain r₄ : ∀ i ∈ [RX, RY, RZ], sv c base s₄ i = sv c base s₂ i := fun i hi =>
    O₄.wordsVal (d := c.sl i) (k := c.n)
      (Or.inl (sl_lt c (i := i) (j := TX) ((by decide : ∀ i ∈ [RX, RY, RZ], i < TX) i hi)))
      (by
        have := sl_le c h7 ((by decide : ∀ i ∈ [RX, RY, RZ], i < 45) i hi)
        have hsz : size = 8192 := rfl
        omega_using [this, hsz])
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
    (q₃ := TZ) (o₁ := DX) (o₂ := DY) (o₃ := DZ) (by decide) (by decide) (by decide) ctx₄.scr
    ctx₄.mp (ctx₄.lt8 hc ltR₄ ltT₄)) fun s₅ ⟨K₅, U₅, L₅, V₅⟩ => ?_)
  obtain ctx₅ := ctx₄.next hc K₅ edi_clob esp_clob U₅ (winW_pW h7 (by decide))
  obtain repD₅ : Rep c.C (fv c base s₅ DX) (fv c base s₅ DY) (fv c base s₅ DZ) (mul (k / 2 ^ (c.winW * i)) P) := by
    rw [← win_pt hC hP c.winW k i]
    have := hadd (fun y => tmv c.C c.n base s₄ (rcbσ c.rcbSlots (c.pt RX RY RZ) (c.pt TX TY TZ)
      (c.pt DX DY DZ) y)) (onCurve_dblPt hC _ hQ) (hC.onCurve_mul hP _) (ctx₄.fv_ap hc) (ctx₄.fv_b3p hc)
      nofun repR₄ repT₄
    simp only [Prod.mk.injEq] at V₅
    rw [V₅.1, V₅.2.1, V₅.2.2]; exact this
  -- `R = D`.
  refine WP.block_append (WP.mono (copySlots_ok hc ctx₅.scr (o₁ := RX) (o₂ := RY) (o₃ := RZ)
    (a₁ := DX) (a₂ := DY) (a₃ := DZ) (by decide) (by decide) (by decide))
    fun s₆ ⟨ex₆, ey₆, ez₆, k₆, U₆⟩ => ?_)
  obtain ctx₆ := ctx₅.next hc k₆ (by decide) (by decide) U₆ (winW_slW h7 (by decide))
  obtain g₆ : s₆.gpr .esi = BitVec.ofNat 32 i := by
    rw [k₆.1 _ (by decide), K₅.1 _ esi_clob, k₄.1 _ (by decide), k₃.1 _ (by decide), g₂]
  refine wp_testCounter (by omega_using [hjn, hJ]) g₆ fun s₇ f₇ z₇ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, z₇⟩
  · exact ctx₆.same hc (f₇.keeps []) (by decide) (by decide) f₇.mem
  · rw [f₇.gpr, g₆]
  · exact ((((((I.keep.trans (k₁.mono (by decide))).trans (K₂.mono esi_powClob)).trans
      (k₃.keeps.mono (by decide))).trans (k₄.mono (by decide))).trans (K₅.mono esi_powClob)).trans
      (k₆.mono (by decide))).trans (f₇.keeps _)
  · rw [f₇.mem]
    exact unch_winWr_trans I.unch (unch_winWr_trans U₂' (unch_winWr_trans U₄'
      (unch_winWr_trans (unch_winWr_pW (by decide) U₅) (unch_winWr_slW (by decide) U₆))))
  · rw [f₇.mem]
    exact (((tbl₂.unch h7 U₄' hfit (below (by decide))).unch h7 U₅ hfit
      (below (by decide))).unch h7 (unch_winWr_slW (by decide) U₆) hfit (below (by decide)))
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

/-! ## The table -/

/-- A loop whose body takes the invariant from `e` to `e + 1` and leaves `ZF`
set iff `e + 1 = n`, run from `i < n`. -/
theorem upLoop_ok {body : Prog isa} {Inv : Nat → State → Prop} {Q : State → Prop} {n i : Nat}
    (hstep : ∀ e s, i ≤ e → e < n → Inv e s →
      WP isa body s fun s' => Inv (e + 1) s' ∧ s'.zf = some (decide (e + 1 = n)))
    (hQ : ∀ s, Inv n s → Q s) (hi : i < n) {s : State} (hs : Inv i s) :
    WP isa (.loop body .ne) s Q := by
  refine WP.loop (M := isa) (fun r s => ∃ e, i ≤ e ∧ e < n ∧ r = n - e ∧ Inv e s)
    (fun r s ⟨e, h1, h2, hr, hI⟩ => ?_) (n - i) s ⟨i, Nat.le_refl _, hi, rfl, hs⟩
  refine WP.mono (hstep e s h1 h2 hI) fun s' ⟨hI', hz⟩ => ?_
  by_cases he : e + 1 = n
  · exact .inl ⟨by simp only [eval, hz, decide_eq_true he, Option.map_some, Bool.not_true],
      hQ s' (by rw [he] at hI'; exact hI')⟩
  · exact .inr ⟨by simp only [eval, hz, decide_eq_false he, Option.map_some, Bool.not_false],
      n - (e + 1), by omega_using [h2, hr], e + 1, by omega_using [h1], by omega_using [h2, he], rfl, hI'⟩

/-- A slot the point multiplied may be in: a numbered slot the windows do not
write, and not the modulus's. -/
abbrev PtSlot (i : Nat) : Prop := i < 45 ∧ i ≠ MP ∧ i ∉ winWr

theorem PtSlot.ok {i : Nat} (h : PtSlot i) : SlotOk i := ⟨h.1, h.2.1, fun e => h.2.2 (e ▸ by decide)⟩

/-- The build's invariant at `esi = e`: the entries up to `e` are there, and
`D` holds `[e]P`. -/
structure BuildInv (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s₀ s : State) (e : Nat) : Prop where
  ctx : WinCtx c base k s
  esi : s.gpr .esi = BitVec.ofNat 32 e
  keep : Keeps powClob s₀ s
  unch : Unch base (winTW c) s₀.mem s.mem
  tbl : TblOk c base P s.mem (e + 1)
  lt : ∀ i ∈ [DX, DY, DZ], sv c base s i < c.C.p
  rep : Rep c.C (fv c base s DX) (fv c base s DY) (fv c base s DZ) (mul e P)

/-- The comb whose test of the counter is the build's: `esi = 2^winW - 1`. -/
abbrev buildK (c : Cfg) : TCombCfg := { c.winScan with J := 2 ^ c.winW }

/-- Entry `e + 1`. -/
theorem winBuildStep_ok (hc : CfgOk c) (hC : Law c.C) {px py : Nat} (hpx : PtSlot px) (hpy : PtSlot py)
    {base : Addr} {P : Point c.C} (hP : onCurve c.C P = true) {k : Nat} {s₀ s : State}
    (hqx : sv c base s₀ px < c.C.p) (hqy : sv c base s₀ py < c.C.p)
    (hG : Rep c.C (fv c base s₀ px) (fv c base s₀ py) 1 P) {e : Nat}
    (he : e < 2 ^ c.winW - 1) (I : BuildInv c base P k s₀ s e) :
    WP isa (c.winBuildStep px py) s fun s' =>
      BuildInv c base P k s₀ s' (e + 1) ∧ s'.zf = some (decide (e + 1 = 2 ^ c.winW - 1)) := by
  have h7 := hc.n10
  have hn := I.ctx.scr.nowrap
  have hfit := winTbl_fit (c := c) hc.n10
  have hge := winTbl_ge c
  have hsz : size = 8192 := rfl
  have he1 : e + 1 < 2 ^ c.winW := by omega_using [he]
  have h16 := (pow_winW_le c).1
  have hE := selE_le (c := c) h7
  have sub9 : ∀ i ∈ [T0, T1, T2, T3, T4, T5, TX, TY, TZ], i ∈ winWr := by decide
  have fitc : ∀ {cnt : Nat}, cnt ≤ 2 ^ c.winW → c.winTbl + 16 * c.winPc * cnt ≤ 8192 := fun h => by
    have := Nat.mul_le_mul_left (16 * c.winPc) h
    omega_using [hfit, this]
  obtain q : ∀ i, PtSlot i → sv c base s i = sv c base s₀ i := fun i hi => sv_winTW I.unch h7 hn hi.1 hi.2.2
  obtain ltQ : ∀ i ∈ [px, py, ONEP], sv c base s i < c.C.p := fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · rw [q _ hpx]; exact hqx
    · rw [q _ hpy]; exact hqy
    · exact I.ctx.lt hc _ (by decide)
  obtain repQ : Rep c.C (fv c base s px) (fv c base s py) (fv c base s ONEP) P := by
    rw [I.ctx.fv_onep hc]
    show Rep _ (toM _ _ (sv c base s px)) (toM _ _ (sv c base s py)) _ _
    rw [q _ hpx, q _ hpy]; exact hG
  obtain ⟨N, hN, eN, hadd⟩ := winAddM_ok (c := c) hC
  rw [Cfg.winBuildStep, eN]
  -- `T = D + P`.
  refine WP.seq (WP.mono (ptOp_ok hc hN (p₁ := DX) (p₂ := DY) (p₃ := DZ) (q₁ := px) (q₂ := py)
    (q₃ := ONEP) (o₁ := TX) (o₂ := TY) (o₃ := TZ) (by decide)
    (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | decide | exact fun h => hpx.2.2 (sub9 _ h) | exact fun h => hpy.2.2 (sub9 _ h))
    (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | decide | exact hpx.ok | exact hpy.ok)
    I.ctx.scr I.ctx.mp (I.ctx.lt8 hc I.lt ltQ)) fun s₁ ⟨K₁, U₁, L₁, V₁⟩ => ?_)
  obtain ctx₁ := I.ctx.next hc K₁ edi_clob esp_clob U₁ (winW_pW h7 (by decide))
  obtain repT₁ : Rep c.C (fv c base s₁ TX) (fv c base s₁ TY) (fv c base s₁ TZ) (mul (e + 1) P) := by
    rw [← mul_succ_pt hC hP e]
    have := hadd (fun y => tmv c.C c.n base s (rcbσ c.rcbSlots (c.pt DX DY DZ) (c.pt px py ONEP)
      (c.pt TX TY TZ) y)) (hC.onCurve_mul hP _) hP (I.ctx.fv_ap hc) (I.ctx.fv_b3p hc)
      (fun _ => I.ctx.fv_onep hc) I.rep repQ
    simp only [Prod.mk.injEq] at V₁
    rw [V₁.1, V₁.2.1, V₁.2.2]; exact this
  obtain g₁ : s₁.gpr .esi = BitVec.ofNat 32 e := by rw [K₁.1 _ esi_clob, I.esi]
  -- `esi += 1`, and the entry, stored.
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_addS rfl fun s₂ u₂ _ => ?_
  obtain g₂ : s₂.gpr .esi = BitVec.ofNat 32 (e + 1) := by rw [u₂.gpr, g₁, BitVec.ofNat_add]; rfl
  obtain ctx₂ := ctx₁.same hc u₂.keeps (by decide) (by decide) u₂.mem
  refine WP.block_append (WP.mono (winStore_ok hc ctx₂.scr he1 g₂) fun s₃ ⟨V₃, k₃, O₃⟩ => ?_)
  obtain e₂ : ∀ i, sv c base s₂ i = sv c base s₁ i := fun i => by show wordsVal s₂.mem _ _ _ = _; rw [u₂.mem]
  rw [u₂.mem] at O₃
  obtain sx : wordsVal s₃.mem base (tblAt c (e + 1) (c.n * 0)) c.n = sv c base s₁ TX :=
    (V₃ 0 (by decide)).trans (e₂ _)
  obtain sy : wordsVal s₃.mem base (tblAt c (e + 1) (c.n * 1)) c.n = sv c base s₁ TY :=
    (V₃ 1 (by decide)).trans (e₂ _)
  obtain sz : wordsVal s₃.mem base (tblAt c (e + 1) (c.n * 2)) c.n = sv c base s₁ TZ :=
    (V₃ 2 (by decide)).trans (e₂ _)
  obtain ctx₃ := ctx₂.next hc k₃ (by decide) (by decide) (by rw [u₂.mem]; exact O₃.unch)
    (winW_tbl (by dsimp only [tblAt]; omega_using []))
  obtain tbl₃ : TblOk c base P s₃.mem (e + 1 + 1) :=
    (I.tbl.unch h7 U₁ (fitc (Nat.le_of_lt he1)) (pW_tbl h7 (by decide) (fitc (Nat.le_of_lt he1)))).store hc he1
      O₃ sx sy sz (L₁ _ (by decide)) (L₁ _ (by decide)) (L₁ _ (by decide)) repT₁
  -- `D = T`.
  refine WP.block_append (WP.mono (copySlots_ok hc ctx₃.scr (o₁ := DX) (o₂ := DY) (o₃ := DZ)
    (a₁ := TX) (a₂ := TY) (a₃ := TZ) (by decide) (by decide) (by decide))
    fun s₄ ⟨ex₄, ey₄, ez₄, k₄, U₄⟩ => ?_)
  obtain ctx₄ := ctx₃.next hc k₄ (by decide) (by decide) U₄ (winW_slW h7 (by decide))
  obtain t₃ : ∀ i ∈ [TX, TY, TZ], sv c base s₃ i = sv c base s₁ i := fun i hi => by
    have h45 : i < 45 := (by decide : ∀ i ∈ [TX, TY, TZ], i < 45) i hi
    have hle := sl_below_wk c h45
    have hwk := wk_eq c
    exact O₃.wordsVal (Or.inl (by dsimp only [tblAt]; omega_using [hle, hwk, hge])) (by omega_using [hle, hwk])
  rw [t₃ TX (by decide)] at ex₄
  rw [t₃ TY (by decide)] at ey₄
  rw [t₃ TZ (by decide)] at ez₄
  obtain g₄ : s₄.gpr .esi = BitVec.ofNat 32 (e + 1) := by rw [k₄.1 _ (by decide), k₃.1 _ (by decide), g₂]
  refine WP.mono (topTest_ok (buildK c) s₄ (j := e + 1) he1 (by show 2 ^ c.winW < _; omega_using [h16]) g₄)
    fun s₅ ⟨z₅, k₅⟩ => ?_
  obtain m₅ : s₅.mem = s₄.mem := k₅.2.1
  obtain U₃₄ : Unch base (winTW c) s.mem s₄.mem :=
    unch_winTW_trans (unch_winTW (unch_winWr_pW (by decide) U₁))
      (unch_winTW_trans (unch_winTW_entry he1 O₃) (unch_winTW (unch_winWr_slW (by decide) U₄)))
  refine ⟨⟨ctx₄.same hc k₅.keeps (by decide) (by decide) m₅, by rw [k₅.1 _ List.not_mem_nil, g₄], ?_, ?_, ?_,
    fun i hi => ?_, ?_⟩, z₅⟩
  · exact ((((I.keep.trans (K₁.mono esi_powClob)).trans (u₂.keeps.mono (by decide))).trans
      (k₃.mono (by decide))).trans (k₄.mono (by decide))).trans (k₅.keeps.mono (by decide))
  · rw [m₅]; exact unch_winTW_trans I.unch U₃₄
  · rw [m₅]
    exact tbl₃.unch h7 (unch_winWr_slW (by decide) U₄) (fitc he1) (pW_tbl h7 (by decide) (fitc he1))
  · show wordsVal s₅.mem _ _ _ < _
    rw [m₅]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact lt_of_eq_of_lt ex₄ (L₁ _ (by decide))
    · exact lt_of_eq_of_lt ey₄ (L₁ _ (by decide))
    · exact lt_of_eq_of_lt ez₄ (L₁ _ (by decide))
  · show Rep _ (toM _ _ (wordsVal s₅.mem _ _ _)) (toM _ _ (wordsVal s₅.mem _ _ _))
      (toM _ _ (wordsVal s₅.mem _ _ _)) _
    rw [m₅]
    show Rep _ (toM _ _ (sv c base s₄ DX)) (toM _ _ (sv c base s₄ DY)) (toM _ _ (sv c base s₄ DZ)) _
    rw [ex₄, ey₄, ez₄]; exact repT₁

/-- A slot the windows write is not one of the point's, nor one's. -/
theorem pt_not {px py : Nat} (hpx : PtSlot px) (hpy : PtSlot py) : ∀ i ∈ winWr, i ∉ [px, py, ONEP] := by
  intro i hi h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · exact hpx.2.2 hi
  · exact hpy.2.2 hi
  · exact absurd hi (by decide)

/-- `winBuild`: the table holds `[e]P` for every `e < 2^w`, for the affine
point `P` at `px`, `py`. -/
theorem winBuild_ok (hc : CfgOk c) (hC : Law c.C) {px py : Nat} (hpx : PtSlot px) (hpy : PtSlot py)
    {base : Addr} {P : Point c.C} (hP : onCurve c.C P = true)
    {k : Nat} {s : State} (ctx : WinCtx c base k s) (hqx : sv c base s px < c.C.p)
    (hqy : sv c base s py < c.C.p) (hG : Rep c.C (fv c base s px) (fv c base s py) 1 P) :
    WP isa (c.winBuild px py) s fun s' => WinCtx c base k s' ∧ Keeps powClob s s' ∧
      Unch base (winTW c) s.mem s'.mem ∧ TblOk c base P s'.mem (2 ^ c.winW) := by
  have h7 := hc.n10
  have hn := ctx.scr.nowrap
  have hfit := winTbl_fit (c := c) hc.n10
  have h8 := (pow_winW_le c).2
  have h16 := (pow_winW_le c).1
  have fitc : ∀ {cnt : Nat}, cnt ≤ 2 ^ c.winW → c.winTbl + 16 * c.winPc * cnt ≤ 8192 := fun h => by
    have := Nat.mul_le_mul_left (16 * c.winPc) h
    omega_using [hfit, this]
  have subT : ∀ i ∈ [TX, TY, TZ], i ∈ winWr := by decide
  have subD : ∀ i ∈ [DX, DY, DZ], i ∈ winWr := by decide
  obtain svq : ∀ {t : State}, Unch base (winTW c) s.mem t.mem → ∀ {i : Nat}, i < 45 → i ∉ winWr →
      sv c base t i = sv c base s i := fun U _ hi hl => sv_winTW U h7 hn hi hl
  obtain repQ : Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (sv c base s px)) (toM c.C.p (2 ^ (64 * c.n)) (sv c base s py))
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ONEP)) P := by
    have h1 : toM c.C.p (2 ^ (64 * c.n)) (sv c base s ONEP) = 1 := ctx.fv_onep hc
    rw [h1]; exact hG
  rw [Cfg.winBuild]
  refine WP.seq ?_
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- `T = O`, entry 0.
  refine WP.block_append (WP.mono (copySlots_ok hc ctx.scr (o₁ := TX) (o₂ := TY) (o₃ := TZ)
    (a₁ := ZERO) (a₂ := ONEP) (a₃ := ZERO) (by decide) (by decide) (by decide))
    fun s₁ ⟨tx₁, ty₁, tz₁, k₁, U₁⟩ => ?_)
  obtain ctx₁ := ctx.next hc k₁ (by decide) (by decide) U₁ (winW_slW h7 (by decide))
  obtain UU₁ : Unch base (winTW c) s.mem s₁.mem := unch_winTW (unch_winWr_slW subT U₁)
  refine wp_movi fun s₂ u₂ => ?_
  obtain ctx₂ := ctx₁.same hc u₂.keeps (by decide) (by decide) u₂.mem
  refine WP.block_append (WP.mono (winStore_ok hc ctx₂.scr (e := 0) (by omega_using [h8]) u₂.gpr)
    fun s₃ ⟨V₃, k₃, O₃⟩ => ?_)
  rw [u₂.mem] at O₃
  obtain e₂ : ∀ i, sv c base s₂ i = sv c base s₁ i := fun i => by show wordsVal s₂.mem _ _ _ = _; rw [u₂.mem]
  obtain ctx₃ := ctx₂.next hc k₃ (by decide) (by decide) (by rw [u₂.mem]; exact O₃.unch)
    (winW_tbl (by dsimp only [tblAt]; omega_using []))
  obtain UU₃ : Unch base (winTW c) s.mem s₃.mem :=
    unch_winTW_trans UU₁ (unch_winTW_entry (by omega_using [h8]) O₃)
  obtain tbl₃ : TblOk c base P s₃.mem (0 + 1) :=
    TblOk.store (m := s₁.mem) (fun _ h => absurd h (Nat.not_lt_zero _)) hc (by omega_using [h8]) O₃
      ((V₃ 0 (by decide)).trans ((e₂ _).trans tx₁)) ((V₃ 1 (by decide)).trans ((e₂ _).trans ty₁))
      ((V₃ 2 (by decide)).trans ((e₂ _).trans tz₁))
      (ctx.lt hc _ (by decide)) (ctx.lt hc _ (by decide)) (ctx.lt hc _ (by decide)) (by
        rw [mul_zero_pt]
        have h0 : toM c.C.p (2 ^ (64 * c.n)) (sv c base s ZERO) = 0 := ctx.fv_zero
        have h1 : toM c.C.p (2 ^ (64 * c.n)) (sv c base s ONEP) = 1 := ctx.fv_onep hc
        rw [h0, h1]; exact rep_infinity' hC)
  -- `T = P`, `D = P`, entry 1.
  refine WP.block_append (WP.mono (copySlots_ok hc ctx₃.scr (o₁ := TX) (o₂ := TY) (o₃ := TZ)
    (a₁ := px) (a₂ := py) (a₃ := ONEP)
    (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | decide | exact hpx.1 | exact hpy.1)
    (by decide) (fun i hi => pt_not hpx hpy i (subT i hi)))
    fun s₄ ⟨tx₄, ty₄, tz₄, k₄, U₄⟩ => ?_)
  rw [svq UU₃ hpx.1 hpx.2.2] at tx₄
  rw [svq UU₃ hpy.1 hpy.2.2] at ty₄
  rw [svq UU₃ (i := ONEP) (by decide) (by decide)] at tz₄
  obtain ctx₄ := ctx₃.next hc k₄ (by decide) (by decide) U₄ (winW_slW h7 (by decide))
  obtain UU₄ : Unch base (winTW c) s.mem s₄.mem :=
    unch_winTW_trans UU₃ (unch_winTW (unch_winWr_slW subT U₄))
  refine WP.block_append (WP.mono (copySlots_ok hc ctx₄.scr (o₁ := DX) (o₂ := DY) (o₃ := DZ)
    (a₁ := px) (a₂ := py) (a₃ := ONEP)
    (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | decide | exact hpx.1 | exact hpy.1)
    (by decide) (fun i hi => pt_not hpx hpy i (subD i hi)))
    fun s₅ ⟨dx₅, dy₅, dz₅, k₅, U₅⟩ => ?_)
  rw [svq UU₄ hpx.1 hpx.2.2] at dx₅
  rw [svq UU₄ hpy.1 hpy.2.2] at dy₅
  rw [svq UU₄ (i := ONEP) (by decide) (by decide)] at dz₅
  obtain ctx₅ := ctx₄.next hc k₅ (by decide) (by decide) U₅ (winW_slW h7 (by decide))
  obtain UU₅ : Unch base (winTW c) s.mem s₅.mem :=
    unch_winTW_trans UU₄ (unch_winTW (unch_winWr_slW subD U₅))
  obtain t₅ : ∀ i ∈ [TX, TY, TZ], sv c base s₅ i = sv c base s₄ i := fun i hi =>
    sv_unch U₅ h7 hn ((by decide : ∀ i ∈ [TX, TY, TZ], i < 45) i hi)
      (apart_slW ((by decide : ∀ i ∈ [TX, TY, TZ], i ∉ [DX, DY, DZ]) i hi))
  refine wp_movi fun s₆ u₆ => ?_
  obtain ctx₆ := ctx₅.same hc u₆.keeps (by decide) (by decide) u₆.mem
  obtain e₆ : ∀ i, sv c base s₆ i = sv c base s₅ i := fun i => by show wordsVal s₆.mem _ _ _ = _; rw [u₆.mem]
  refine WP.mono (winStore_ok hc ctx₆.scr (e := 1) (by omega_using [h8]) u₆.gpr) fun s₇ ⟨V₇, k₇, O₇⟩ => ?_
  rw [u₆.mem] at O₇
  obtain ctx₇ := ctx₆.next hc k₇ (by decide) (by decide) (by rw [u₆.mem]; exact O₇.unch)
    (winW_tbl (by dsimp only [tblAt]; omega_using []))
  obtain UU₇ : Unch base (winTW c) s.mem s₇.mem :=
    unch_winTW_trans UU₅ (unch_winTW_entry (by omega_using [h8]) O₇)
  obtain tbl₅ : TblOk c base P s₅.mem (0 + 1) :=
    (tbl₃.unch h7 (unch_winWr_slW subT U₄) (fitc (by omega_using [h8]))
      (pW_tbl h7 (by decide) (fitc (by omega_using [h8])))).unch h7 (unch_winWr_slW subD U₅)
      (fitc (by omega_using [h8])) (pW_tbl h7 (by decide) (fitc (by omega_using [h8])))
  obtain tbl₇ : TblOk c base P s₇.mem (1 + 1) :=
    tbl₅.store hc (by omega_using [h8]) O₇
      ((V₇ 0 (by decide)).trans ((e₆ _).trans ((t₅ TX (by decide)).trans tx₄)))
      ((V₇ 1 (by decide)).trans ((e₆ _).trans ((t₅ TY (by decide)).trans ty₄)))
      ((V₇ 2 (by decide)).trans ((e₆ _).trans ((t₅ TZ (by decide)).trans tz₄)))
      hqx hqy (ctx.lt hc _ (by decide)) (by rw [mul_one_pt]; exact repQ)
  obtain d₇ : ∀ i ∈ [DX, DY, DZ], sv c base s₇ i = sv c base s₅ i := fun i hi => by
    have h45 : i < 45 := (by decide : ∀ i ∈ [DX, DY, DZ], i < 45) i hi
    have hle := sl_below_wk c h45
    have hwk := wk_eq c
    have hge := winTbl_ge c
    exact O₇.wordsVal (Or.inl (by dsimp only [tblAt]; omega_using [hle, hwk, hge])) (by omega_using [hle, hwk])
  -- The loop.
  refine upLoop_ok (Inv := fun e t => BuildInv c base P k s t e) (n := 2 ^ c.winW - 1) (i := 1)
    (fun e t _ he I => winBuildStep_ok hc hC hpx hpy hP hqx hqy hG he I)
    (fun t I => ⟨I.ctx, I.keep, I.unch, by have := I.tbl; rwa [Nat.sub_add_cancel (by omega_using [h8])] at this⟩)
    (by omega_using [h8]) ?_
  refine ⟨ctx₇, by rw [k₇.1 _ (by decide), u₆.gpr]; rfl, ?_, UU₇, tbl₇, fun i hi => ?_, ?_⟩
  · exact (((((k₁.mono (by decide)).trans (u₂.keeps.mono (by decide))).trans (k₃.mono (by decide))).trans
      (k₄.mono (by decide))).trans (k₅.mono (by decide))).trans
      ((u₆.keeps.mono (by decide)).trans (k₇.mono (by decide)))
  · rw [d₇ i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact lt_of_eq_of_lt dx₅ hqx
    · exact lt_of_eq_of_lt dy₅ hqy
    · exact lt_of_eq_of_lt dz₅ (ctx.lt hc _ (by decide))
  · show Rep _ (toM _ _ (sv c base s₇ DX)) (toM _ _ (sv c base s₇ DY)) (toM _ _ (sv c base s₇ DZ)) _
    rw [d₇ DX (by decide), d₇ DY (by decide), d₇ DZ (by decide), dx₅, dy₅, dz₅, mul_one_pt]; exact repQ

/-! ## The multiplication -/

/-- `winMul`: `R` holds, below `p`, a representative of `[k]P`, for the
affine point `P` of the curve at `px`, `py` and the number `k < 2^(8 len)`
whose bits are table 0; only `powClob` and what the windows write (`winTW`)
change. -/
theorem winMul_ok (hc : CfgOk c) (hC : Law c.C) {px py : Nat} (hpx : PtSlot px) (hpy : PtSlot py)
    {base : Addr} {s : State} (hs : Scr s base size)
    (hmp : sv c base s MP = c.C.p) (hap : sv c base s AP = c.mont c.C.a)
    (hb3 : sv c base s B3P = c.mont (3 * c.C.b)) (hzero : sv c base s ZERO = 0)
    (hone : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) (hqx : sv c base s px < c.C.p)
    (hqy : sv c base s py < c.C.p) {P : Point c.C} (hP : onCurve c.C P = true)
    (hG : Rep c.C (fv c base s px) (fv c base s py) 1 P) {k : Nat} (hk : k < 2 ^ (8 * c.C.len))
    (hbits : ∀ t < 8 * c.C.len, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0) :
    WP isa (c.winMul px py) s fun s' => Keeps powClob s s' ∧ Unch base (winTW c) s.mem s'.mem ∧
      (∀ i ∈ [RX, RY, RZ], sv c base s' i < c.C.p) ∧
      Rep c.C (fv c base s' RX) (fv c base s' RY) (fv c base s' RZ) (mul k P) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hfit := winTbl_fit (c := c) hc.n10
  obtain ⟨hJ1, hJ, -, hcover⟩ := winJ_bounds hc
  obtain ctx : WinCtx c base k s := ⟨hs, hmp, hap, hb3, hzero, hone, hbits⟩
  rw [Cfg.winMul]
  -- The table of the point's multiples.
  refine WP.seq (WP.mono (winBuild_ok hc hC hpx hpy hP ctx hqx hqy hG) fun s₂ ⟨ctx₂, K₂, U₂, tbl₂⟩ => ?_)
  -- `R = O`.
  refine WP.seq ?_
  refine WP.block_append (WP.mono (copySlots_ok hc ctx₂.scr (o₁ := RX) (o₂ := RY) (o₃ := RZ)
    (a₁ := ZERO) (a₂ := ONEP) (a₃ := ZERO) (by decide) (by decide) (by decide))
    fun s₃ ⟨rx, ry, rz, k₃, U₃⟩ => ?_)
  refine wp_movi fun s₄ u₄ => WP.block_nil ?_
  obtain k₃₄ : Keeps [.eax, .esi] s₂ s₄ := (k₃.mono (by decide)).trans (u₄.keeps.mono (by decide))
  obtain U₃₄ : Unch base (slW c [RX, RY, RZ]) s₂.mem s₄.mem := by rw [u₄.mem]; exact U₃
  obtain ctx₄ := ctx₂.next hc k₃₄ (by decide) (by decide) U₃₄ (winW_slW h7 (by decide))
  obtain e₄ : ∀ i, sv c base s₄ i = sv c base s₃ i := fun i => by show wordsVal s₄.mem _ _ _ = _; rw [u₄.mem]
  -- The windows.
  refine countLoop_ok (Inv := fun j t => WinInv c base P k s₄ t j) (n := c.winJ)
    (fun j t h1 h2 I => winStep_ok hc hC hP hk h1 h2 I) (fun t I => ⟨?_, ?_, I.lt, ?_⟩) hJ1 ?_
  · exact ⟨ctx₄, u₄.gpr, Keeps.refl _ _, Unch.refl _ _ _,
      tbl₂.unch h7 (unch_winWr_slW (by decide) U₃₄) hfit (pW_tbl h7 (by decide) hfit),
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
  · exact (K₂.trans (k₃₄.mono (by decide))).trans I.keep
  · exact unch_winTW_trans U₂ (unch_winTW (unch_winWr_trans (unch_winWr_slW (by decide) U₃₄) I.unch))
  · have := I.rep
    rwa [Nat.mul_zero, Nat.pow_zero, Nat.div_one] at this

/-! ## Signed windows of four bits

`Cfg.swinMul` (`Impl/Ecdsa/X86/Window.lean`), for the curves whose table has
eight entries: Booth's digits `d_j = w_j + b_{4j-1} - 16 b_{4j+3}`. After the
windows from `j` up the accumulator is `[swPre k j]P`, where `swPre k j` is
`k / 16^j`, plus one if the bit below is set (`swin_pt`). -/

/-- The multiple after the windows from `j` up. -/
def swPre (k j : Nat) : Nat := k / 2 ^ (4 * j) + (if 0 < j ∧ k.testBit (4 * j - 1) then 1 else 0)

/-- Window `j`'s digit, plus 16: its window with its top bit flipped, plus 8,
plus the bit below. -/
def swV (k j : Nat) : Nat :=
  (if combWin 4 k j < 8 then combWin 4 k j + 16 else combWin 4 k j) +
    (if 0 < j ∧ k.testBit (4 * j - 1) then 1 else 0)

theorem combWin4_lt (k j : Nat) : combWin 4 k j < 16 := combWin_lt 4 k j

theorem swV_lt (k j : Nat) : swV k j < 32 := by
  have := combWin4_lt k j
  unfold swV
  split <;> split <;> omega_arith

theorem swPre_succ (k j : Nat) :
    swPre k (j + 1) = k / 2 ^ (4 * (j + 1)) + (if 8 ≤ combWin 4 k j then 1 else 0) := by
  have h := testBit_top k 4 j (by decide)
  rw [show 4 * j + (4 - 1) = 4 * (j + 1) - 1 by omega_arith, show (2 : Nat) ^ (4 - 1) = 8 from rfl] at h
  unfold swPre
  rw [h]
  simp only [Nat.zero_lt_succ, true_and, decide_eq_true_eq]

theorem div_win4 (k j : Nat) : k / 2 ^ (4 * j) = 16 * (k / 2 ^ (4 * (j + 1))) + combWin 4 k j := by
  have h := Nat.div_add_mod (k / 2 ^ (4 * j)) (2 ^ 4)
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, show (2 : Nat) ^ 4 = 16 from rfl] at h
  rw [combWin, show 4 * (j + 1) = 4 * j + 4 by omega_arith, show (2 : Nat) ^ 4 = 16 from rfl]
  exact h.symm

/-- A window's step of the multiple: its digit added, or subtracted where
the window's top bit is set. -/
theorem swPre_step (k j : Nat) :
    (16 ≤ swV k j → swPre k j = 16 * swPre k (j + 1) + magH 16 (swV k j) ∧
      (combWin 4 k j < 8 ∨ magH 16 (swV k j) = 0)) ∧
    (swV k j < 16 → ¬combWin 4 k j < 8 ∧ magH 16 (swV k j) ≤ 16 * swPre k (j + 1) ∧
      swPre k j = 16 * swPre k (j + 1) - magH 16 (swV k j)) := by
  have hw := combWin4_lt k j
  have hd := div_win4 k j
  have hm : ∀ x, (if 16 ≤ x then x - 16 else 16 - x) = x - 16 + (16 - x) := fun x => by
    split <;> omega_arith
  rw [swPre_succ]
  unfold swPre swV magH
  rw [hd]
  obtain ⟨w, hwe⟩ : ∃ w, combWin 4 k j = w := ⟨_, rfl⟩
  rw [hwe] at hw ⊢
  obtain ⟨c, hc, hc1⟩ : ∃ c, (if 0 < j ∧ k.testBit (4 * j - 1) = true then 1 else 0) = c ∧ c ≤ 1 :=
    ⟨_, rfl, by split <;> decide⟩
  rw [hc]
  simp only [hm]
  generalize k / 2 ^ (4 * (j + 1)) = q
  by_cases h8 : w < 8
  · have h8' : ¬8 ≤ w := by omega_arith
    simp only [h8, h8', ↓reduceIte]
    exact ⟨fun _ => ⟨by omega_arith, Or.inl trivial⟩, fun h => absurd h (by omega_arith)⟩
  · have h8' : 8 ≤ w := by omega_arith
    simp only [h8, h8', ↓reduceIte]
    exact ⟨fun h => ⟨by omega_arith, Or.inr (by omega_arith)⟩,
      fun h => ⟨fun hf => hf, by omega_arith, by omega_arith⟩⟩

/-- A window: `16 [swPre k (j + 1)]P ± [|d_j|]P = [swPre k j]P`. -/
theorem swin_pt {C : Curve} (hC : Law C) {P : Point C} (hP : onCurve C P = true) (k j : Nat) :
    Spec.Weierstrass.add (dblPt (mul (swPre k (j + 1)) P) 4)
      (if combWin 4 k j < 8 then mul (magH 16 (swV k j)) P else negPt (mul (magH 16 (swV k j)) P)) =
      mul (swPre k j) P := by
  rw [dblPt_mul hC hP, show (2 : Nat) ^ 4 = 16 from rfl]
  by_cases h16 : 16 ≤ swV k j
  · obtain ⟨e, hz⟩ := (swPre_step k j).1 h16
    have hn : negPt (mul 0 P) = mul 0 P := by
      have h0 : mul 0 P = .infinity := by rw [Spec.Weierstrass.mul]; simp
      rw [h0]; rfl
    rcases hz with hw | hm
    · simp only [hw, ↓reduceIte]
      rw [hC.add_mul_mul hP, e]
    · rw [hm] at e ⊢
      rw [hn, ite_self, hC.add_mul_mul hP, e]
  · obtain ⟨hw, hle, e⟩ := (swPre_step k j).2 (by omega_arith)
    simp only [hw, ↓reduceIte]
    rw [hC.add_mul_neg hP hle, e]

/-- A byte of the table of bits at a constant offset from window `esi`'s. -/
theorem winBit_ok {s : State} {base : Addr} (hs : Scr s base size) {k j N D t bits w : Nat}
    (hw : w < 2 ^ 32) (hj : j < 2 ^ 32) (hD : D + w * j = bits + t) (ht : t < N) (hN : bits + N ≤ size)
    (hx : s.gpr .esi = BitVec.ofNat 32 j)
    (hbits : ∀ t < N, s.mem (off base (bits + t)) = if k.testBit t then 1 else 0) :
    WP isa (.block (winIndex w ++ [.movzx8 .ebx (winByte D)])) s fun u =>
      u.gpr .ebx = BitVec.ofNat 32 (k.testBit t).toNat ∧ CKeeps [.eax, .ebx, .ecx, .edx] s u := by
  have hn := hs.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (winIndex_ok s hw hj hx) fun a ⟨a1, ka⟩ => ?_
  have hea : a.ea (winByte D) = off base (bits + t) := by
    rw [ea_winByte (hs.of_keeps ka.keeps (by decide)) (by rw [ka.1 .edi (by decide)]; exact a1)
      (by omega_arith)]
    exact congrArg (off base) hD
  have hr : InRegions (a.rd ++ a.wr) (off base (bits + t)) 1 :=
    ⟨_, List.mem_append_right _ (ka.2.2.2 ▸ hs.wr), Scr.contains hs.nowrap (by omega_arith)⟩
  have hm : a.mem (off base (bits + t)) = if k.testBit t then 1 else 0 := by rw [ka.2.1, hbits _ ht]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load8, hea, hr, hm, ite_true,
    Option.map_some, RegUpd.gpr_setReg, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr' => ?_, ka.2.1, ka.2.2.1, ka.2.2.2⟩
  · cases k.testBit t <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    simp only [RegUpd.gpr_setReg, hr'.2.1, ite_false]
    exact ka.1 r (by simp [hr'.1, hr'.2.2.1, hr'.2.2.2])

/-- Booth's digit plus 16, from the window in `eax` and the bit below in `ebx`. -/
theorem boothAdj_ok (s : State) {w cc : Nat} (hw : w < 16) (hcc : cc < 2)
    (ha : s.gpr .eax = BitVec.ofNat 32 w) (hb : s.gpr .ebx = BitVec.ofNat 32 cc) :
    WP isa (.block [.alu .xor .eax (.imm 8), .alu .add .eax (.imm 8), .alu .add .eax (.reg .ebx)]) s
      fun t => t.gpr .eax = BitVec.ofNat 32 ((if w < 8 then w + 16 else w) + cc) ∧ CKeeps [.eax] s t := by
  crun [ha, hb]
  refine ⟨booth_fact w hw cc hcc, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- The number of a magnitude's entry. -/
theorem entryNum_ok (s : State) {m : Nat} (hm : m < 17) (hb : s.gpr .ebx = BitVec.ofNat 32 m) :
    WP isa (.block [.alu .and .ebx (.imm 7), .alu .add .ebx (.imm 1)]) s
      fun t => t.gpr .ebx = BitVec.ofNat 32 (m % 8 + 1) ∧ CKeeps [.ebx] s t := by
  crun [hb]
  refine ⟨entry_fact m hm, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- The digit of a window: its magnitude, and the number of its entry. -/
theorem swinDigit_ok (hc : CfgOk c) {base : Addr} {k : Nat} {s : State} (ctx : WinCtx c base k s)
    (hk : k < 2 ^ (8 * c.C.len)) {j : Nat} (hj : j < c.swinJ) (gj : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa c.swinDigit s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (magH 16 (swV k j)) ∧
      t.gpr .ebx = BitVec.ofNat 32 (magH 16 (swV k j) % 8 + 1) ∧ CKeeps [.eax, .ebx, .ecx, .edx] s t := by
  have h7 := hc.n10
  have hlen := hc.len_hi
  have hbit0 := bitsAt_le c h7 (j := 0) (by decide)
  have hJ : c.swinJ = 2 * c.C.len := rfl
  have hw := combWin4_lt k j
  have hsz : size = 8192 := rfl
  have hb0 : bitsAt c.n 0 = 4096 := rfl
  -- The window, Booth's digit and its magnitude, from the bit below in `ebx`.
  have tail : ∀ (t : State) (cc : Nat), cc < 2 → CKeeps [.eax, .ebx, .ecx, .edx] s t →
      t.gpr .ebx = BitVec.ofNat 32 cc →
      WP isa (.block ((winIndex 4 ++ hornerBits (bitsAt c.n 0) 4) ++
        (([.alu .xor .eax (.imm 8), .alu .add .eax (.imm 8), .alu .add .eax (.reg .ebx)] : List Instr) ++
          (magnitudeH 16 ++ ([.alu .and .ebx (.imm 7), .alu .add .ebx (.imm 1)] : List Instr))))) t
        fun u => u.gpr .eax = BitVec.ofNat 32 (magH 16
            ((if combWin 4 k j < 8 then combWin 4 k j + 16 else combWin 4 k j) + cc)) ∧
          u.gpr .ebx = BitVec.ofNat 32 (magH 16
            ((if combWin 4 k j < 8 then combWin 4 k j + 16 else combWin 4 k j) + cc) % 8 + 1) ∧
          CKeeps [.eax, .ebx, .ecx, .edx] s u := by
    intro t cc hcc kt gb
    have hst : Scr t base size := ctx.scr.of_keeps kt.keeps (by decide)
    have hxt : t.gpr .esi = BitVec.ofNat 32 j := by rw [kt.1 _ (by decide), gj]
    have hbt : ∀ i < 8 * c.C.len, t.mem (off base (bitsAt c.n 0 + i)) = if k.testBit i then 1 else 0 :=
      fun i hi => by rw [kt.2.1]; exact ctx.bits i hi
    have hv : (if combWin 4 k j < 8 then combWin 4 k j + 16 else combWin 4 k j) + cc < 32 := by
      split <;> omega_arith
    refine WP.block_append (WP.mono (winBits_ok hst (k := k) (j := j) (cnt := 4) (N := 8 * c.C.len)
      (by decide) (Nat.le_refl 4) (by omega_using [hj, hJ]) (by omega_using [hj, hJ, hlen, h7])
      (by omega_using [hbit0, hlen]) hxt hbt (window_without_padding (Nat.le_refl 4) (Or.inl rfl) hk))
      fun t₁ ⟨a₁, k₁⟩ => ?_)
    have b₁ : t₁.gpr .ebx = BitVec.ofNat 32 cc := by rw [k₁.1 _ (by decide), gb]
    refine WP.block_append (WP.mono (boothAdj_ok t₁ hw hcc a₁ b₁) fun t₂ ⟨a₂, k₂⟩ => ?_)
    refine WP.block_append (WP.mono (magnitudeH_ok t₂ (w := 5) (by decide) hv a₂) fun t₃ ⟨a₃, b₃, k₃⟩ => ?_)
    have hm : magH 16 ((if combWin 4 k j < 8 then combWin 4 k j + 16 else combWin 4 k j) + cc) < 17 := by
      unfold magH
      by_cases h8 : combWin 4 k j < 8 <;> simp only [h8, ↓reduceIte] <;> split <;> omega_arith
    refine WP.mono (entryNum_ok t₃ hm b₃) fun u ⟨b₄, k₄⟩ => ⟨?_, b₄, ?_⟩
    · rw [k₄.1 _ (by decide)]; exact a₃
    · exact kt.trans (((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans
        ((k₃.mono (by decide)).trans (k₄.mono (by decide))))
  unfold Cfg.swinDigit
  refine WP.seq (wp_testCounter (by omega_using [hj, hJ, hlen, h7]) gj fun s₁ f₁ z₁ => WP.block_nil ?_)
  have k₁ : CKeeps [] s s₁ := ⟨fun r _ => (f₁.keeps []).1 r List.not_mem_nil, f₁.mem, (f₁.keeps []).2.1,
    (f₁.keeps []).2.2⟩
  refine WP.ite (decide (j = 0)) z₁ (fun h => ?_) (fun h => ?_)
  · have hj0 : j = 0 := of_decide_eq_true h
    have hcz : (if 0 < j ∧ k.testBit (4 * j - 1) = true then 1 else 0) = 0 := by
      rw [hj0]; rfl
    unfold Cfg.swinDigitB
    simp only [↓reduceIte]
    refine WP.block_append (wp_movS rfl fun t u _ => WP.block_nil ?_)
    refine WP.mono (tail t 0 (by decide) ((k₁.mono (fun _ h => nomatch h)).trans
      ⟨fun r hr => u.other r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact hr.2.1),
        u.mem, u.rd, u.wr⟩) u.gpr) fun v ⟨va, vb, vk⟩ => ?_
    unfold swV
    rw [hcz]
    exact ⟨va, vb, vk⟩
  · have hj0 : j ≠ 0 := of_decide_eq_false h
    have hcz : (if 0 < j ∧ k.testBit (4 * j - 1) = true then 1 else 0) = (k.testBit (4 * j - 1)).toNat := by
      have : 0 < j := by omega_arith
      cases k.testBit (4 * j - 1) <;> simp [this]
    have hs₁ : Scr s₁ base size := ctx.scr.of_keeps k₁.keeps (by decide)
    have hx₁ : s₁.gpr .esi = BitVec.ofNat 32 j := by rw [k₁.1 _ List.not_mem_nil, gj]
    have hb₁ : ∀ i < 8 * c.C.len, s₁.mem (off base (bitsAt c.n 0 + i)) = if k.testBit i then 1 else 0 :=
      fun i hi => by rw [k₁.2.1]; exact ctx.bits i hi
    unfold Cfg.swinDigitB
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.block_append (WP.mono (winBit_ok hs₁ (k := k) (j := j) (N := 8 * c.C.len) (D := bitsAt c.n 0 - 1)
      (t := 4 * j - 1) (bits := bitsAt c.n 0) (w := 4) (by decide) (by omega_using [hj, hJ, hlen, h7])
      (by omega_using [hj0, hb0]) (by omega_using [hj, hJ, hj0]) (by omega_using [hbit0, hlen, hsz]) hx₁ hb₁)
      fun t ⟨tb, tk⟩ => ?_)
    refine WP.mono (tail t _ (by cases k.testBit (4 * j - 1) <;> decide)
      ((k₁.mono (fun _ h => nomatch h)).trans tk) tb) fun v ⟨va, vb, vk⟩ => ?_
    unfold swV
    rw [hcz]
    exact ⟨va, vb, vk⟩

/-- A slot kept, or replaced by another under the mask in `ecx`. -/
theorem selSlot_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) (b : Bool)
    (hm : s.gpr .ecx = if b then BitVec.allOnes 32 else 0) {o a x : Nat} (ho : o < 45) (ha : a < 45)
    (hx : x < 45) :
    WP isa (.block (sel (2 * c.n) (c.sl o) (c.sl a) (c.sl x))) s fun s' =>
      sv c base s' o = (if b then sv c base s x else sv c base s a) ∧
      Keeps [.eax, .edx] s s' ∧ Unch base (slW c [o]) s.mem s'.mem := by
  have h7 := hc.n10
  have hO := sl_le c h7 ho
  have hA := sl_le c h7 ha
  have hX := sl_le c h7 hx
  have cond : ∀ {i : Nat}, c.sl o ≤ c.sl i ∨ c.sl i + 4 * (2 * c.n) ≤ c.sl o := fun {i} => by
    by_cases h : o = i
    · subst h; exact Or.inl (Nat.le_refl _)
    · rcases sl_apart c h with h' | h'
      · exact Or.inl (by omega_arith)
      · exact Or.inr (by omega_arith)
  refine WP.mono (sel_ok b (2 * c.n) hs hm (o := c.sl o) (a := c.sl a) (b := c.sl x) (by omega_arith)
    (by omega_arith) (by omega_arith) cond cond) fun s' ⟨e, k, O⟩ => ⟨?_, k, ?_⟩
  · rw [← wordsVal_eq_val32, ← wordsVal_eq_val32, ← wordsVal_eq_val32] at e
    exact e
  · rw [show 4 * (2 * c.n) = 8 * c.n by omega_arith] at O
    exact O.unch

/-- A point's slots kept, or replaced by another's under the mask in `ecx`. -/
theorem selSelf3_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) (b : Bool)
    (hm : s.gpr .ecx = if b then BitVec.allOnes 32 else 0) {o₁ o₂ o₃ x₁ x₂ x₃ : Nat}
    (h45 : ∀ i ∈ [o₁, o₂, o₃, x₁, x₂, x₃], i < 45) (hnd : [o₁, o₂, o₃].Nodup)
    (hxo : ∀ i ∈ [x₁, x₂, x₃], i ∉ [o₁, o₂, o₃]) :
    WP isa (.block (selPt c.n (c.pt o₁ o₂ o₃) (c.pt o₁ o₂ o₃) (c.pt x₁ x₂ x₃))) s fun s' =>
      sv c base s' o₁ = (if b then sv c base s x₁ else sv c base s o₁) ∧
      sv c base s' o₂ = (if b then sv c base s x₂ else sv c base s o₂) ∧
      sv c base s' o₃ = (if b then sv c base s x₃ else sv c base s o₃) ∧
      Keeps [.eax, .edx] s s' ∧ Unch base (slW c [o₁, o₂, o₃]) s.mem s'.mem := by
  have h7 := hc.n10
  have hn := hs.nowrap
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true, not_false_eq_true] at hnd
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, forall_eq_or_imp, forall_eq] at hxo h45
  obtain ⟨⟨n12, n13⟩, n23⟩ := hnd
  obtain ⟨⟨x11, x12, x13⟩, ⟨x21, x22, x23⟩, ⟨x31, x32, x33⟩⟩ := hxo
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := h45
  have keep : ∀ {m m' : Mem} {o i : Nat}, Unch base (slW c [o]) m m' → i < 45 → i ≠ o →
      wordsVal m' base (c.sl i) c.n = wordsVal m base (c.sl i) c.n := fun U hi hne =>
    sv_unch U h7 hn hi (apart_slW (by simpa using hne))
  show WP isa (.block (sel (2 * c.n) (c.sl o₁) (c.sl o₁) (c.sl x₁) ++ sel (2 * c.n) (c.sl o₂) (c.sl o₂) (c.sl x₂) ++
    sel (2 * c.n) (c.sl o₃) (c.sl o₃) (c.sl x₃))) s _
  refine WP.block_append (WP.block_append (WP.mono (selSlot_ok hc hs b hm l1 l1 l4) fun s₁ ⟨e₁, k₁, U₁⟩ => ?_))
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.mono (selSlot_ok hc hs₁ b (by rw [k₁.1 _ (by decide)]; exact hm) l2 l2 l5) fun s₂ ⟨e₂, k₂, U₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.mono (selSlot_ok hc hs₂ b (by rw [k₂.1 _ (by decide), k₁.1 _ (by decide)]; exact hm) l3 l3 l6)
    fun s₃ ⟨e₃, k₃, U₃⟩ => ⟨?_, ?_, ?_, (k₁.trans k₂).trans k₃, ?_⟩
  · show wordsVal s₃.mem base (c.sl o₁) c.n = _
    rw [keep U₃ l1 n13, keep U₂ l1 n12]; exact e₁
  · show wordsVal s₃.mem base (c.sl o₂) c.n = _
    rw [keep U₃ l2 n23]
    refine e₂.trans ?_
    show (if b then wordsVal s₁.mem base (c.sl x₂) c.n else wordsVal s₁.mem base (c.sl o₂) c.n) = _
    rw [keep U₁ l5 x21, keep U₁ l2 (Ne.symm n12)]
  · refine e₃.trans ?_
    show (if b then wordsVal s₂.mem base (c.sl x₃) c.n else wordsVal s₂.mem base (c.sl o₃) c.n) = _
    rw [keep U₂ l6 x32, keep U₂ l3 (Ne.symm n23), keep U₁ l6 x31, keep U₁ l3 (Ne.symm n13)]
  · refine ((U₁.trans U₂).trans U₃).mono fun w hw => ?_
    simpa only [slW, List.map_cons, List.map_nil, List.cons_append, List.nil_append] using hw

/-- `ecx` all ones if the magnitude in `eax` is zero. -/
theorem zeroMask_ok (s : State) {m : Nat} (hm : m < 17) (ha : s.gpr .eax = BitVec.ofNat 32 m) :
    WP isa (.block [.mov .ecx (.reg .eax), .alu .cmp .ecx (.imm 1), .alu .sbb .ecx (.reg .ecx)]) s
      fun t => t.gpr .ecx = (if decide (m = 0) then BitVec.allOnes 32 else 0) ∧ CKeeps [.ecx] s t := by
  crun [ha]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · exact zero_fact m hm
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- The negation of a point on numbered slots (zero at `14 … 16`). -/
def negN : List FOp := [.add 6 11 14, .sub 7 15 12, .add 8 13 16]

theorem negN_ok : NumOk negN := ⟨by decide, by decide, by decide⟩

theorem negN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    (runOps negN e 6, runOps negN e 7, runOps negN e 8) = (e 11 + e 14, e 15 - e 12, e 13 + e 16) := rfl

theorem swMag_le (k j : Nat) : magH 16 (swV k j) ≤ 8 := by
  have hw := combWin4_lt k j
  unfold magH swV
  obtain ⟨cc, hc, hc1⟩ : ∃ cc, (if 0 < j ∧ k.testBit (4 * j - 1) = true then 1 else 0) = cc ∧ cc ≤ 1 :=
    ⟨_, rfl, by split <;> decide⟩
  rw [hc]
  by_cases h8 : combWin 4 k j < 8 <;> simp only [h8, ↓reduceIte] <;> split <;> omega_arith

/-- The signed windows' table: `[e]P` in entry `e`, and `[2^winW]P` in entry 0. -/
def STblOk (c : Cfg) (base : Addr) (P : Point c.C) (m : Mem) : Prop :=
  ∀ e < 2 ^ c.winW, (∀ j < 3, wordsVal m base (tblAt c e (c.n * j)) c.n < c.C.p) ∧
    Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (wordsVal m base (tblAt c e (c.n * 0)) c.n))
      (toM c.C.p (2 ^ (64 * c.n)) (wordsVal m base (tblAt c e (c.n * 1)) c.n))
      (toM c.C.p (2 ^ (64 * c.n)) (wordsVal m base (tblAt c e (c.n * 2)) c.n))
      (mul (if e = 0 then 2 ^ c.winW else e) P)

theorem STblOk.unch {base : Addr} {P : Point c.C} {W : List (Nat × Nat)} {m m' : Mem}
    (h : STblOk c base P m) (h7 : c.n < 10) (hu : Unch base W m m')
    (hfit : c.winTbl + 16 * c.winPc * 2 ^ c.winW ≤ 8192)
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ c.winTbl ∨ c.winTbl + 16 * c.winPc * 2 ^ c.winW ≤ w.1) :
    STblOk c base P m' := by
  intro e he
  obtain ⟨hl, hr⟩ := h e he
  refine ⟨fun j hj => by rw [winTbl_unch hu h7 he hj hfit hW]; exact hl j hj, ?_⟩
  rw [winTbl_unch hu h7 he (by decide) hfit hW, winTbl_unch hu h7 he (by decide) hfit hW,
    winTbl_unch hu h7 he (by decide) hfit hW]
  exact hr

/-- The signed windows' invariant: `R = [swPre k j]P`. -/
structure SWinInv (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s₀ s : State) (j : Nat) : Prop where
  ctx : WinCtx c base k s
  esi : s.gpr .esi = BitVec.ofNat 32 j
  keep : Keeps powClob s₀ s
  unch : Unch base (pW c winWr) s₀.mem s.mem
  tbl : STblOk c base P s.mem
  lt : ∀ i ∈ [RX, RY, RZ], sv c base s i < c.C.p
  rep : Rep c.C (fv c base s RX) (fv c base s RY) (fv c base s RZ) (mul (swPre k j) P)

/-! SW6-BEGIN -/
/-- A signed window. -/
theorem swinStep_ok (hc : CfgOk c) (hC : Law c.C) (h3 : c.winW = 3) {base : Addr} {P : Point c.C}
    (hP : onCurve c.C P = true) {k : Nat} (hk : k < 2 ^ (8 * c.C.len)) {s₀ s : State} {j : Nat}
    (hj : 1 ≤ j) (hjn : j ≤ c.swinJ) (I : SWinInv c base P k s₀ s j) :
    WP isa c.swinStep s fun s' => SWinInv c base P k s₀ s' (j - 1) ∧ s'.zf = some (decide (j - 1 = 0)) := by
  have h7 := hc.n10
  have hlen := hc.len_hi
  have hJ : c.swinJ = 2 * c.C.len := rfl
  have hbit0 := bitsAt_le c h7 (j := 0) (by decide)
  have hfit := winTbl_fit (c := c) hc.n10
  have hn := I.ctx.scr.nowrap
  have h8 : 2 ^ c.winW = 8 := by rw [h3]; rfl
  have mul0 : mul 0 P = .infinity := by rw [Spec.Weierstrass.mul]; simp
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega_using [hj]⟩
  rw [Nat.add_sub_cancel]
  have hQ := hC.onCurve_mul hP (swPre k (i + 1))
  have below : ∀ {l : List Nat}, (∀ i ∈ l, i < 45) → ∀ w ∈ pW c l,
      w.1 + w.2 ≤ c.winTbl ∨ c.winTbl + 16 * c.winPc * 2 ^ c.winW ≤ w.1 :=
    fun hl => pW_tbl h7 hl hfit
  obtain ⟨m, hm⟩ : ∃ m, magH 16 (swV k i) = m := ⟨_, rfl⟩
  have hm8 : m ≤ 8 := hm ▸ swMag_le k i
  rw [Cfg.swinStep]
  refine WP.seq (wp_decCounter hj I.esi fun s₁ g₁ k₁ m₁ => WP.block_nil ?_)
  rw [Nat.add_sub_cancel] at g₁
  obtain ctx₁ := I.ctx.same hc k₁ (by decide) (by decide) m₁
  -- `R = 16 R`.
  refine WP.seq (WP.mono (winQuadN_ok hc hC 4 ctx₁ hQ
    (fun i hi => by show wordsVal s₁.mem _ _ _ < _; rw [m₁]; exact I.lt i hi)
    (by show Rep _ (toM _ _ (wordsVal s₁.mem _ _ _)) (toM _ _ (wordsVal s₁.mem _ _ _))
          (toM _ _ (wordsVal s₁.mem _ _ _)) _
        rw [m₁]; exact I.rep)) fun s₂ ⟨K₂, U₂, L₂, R₂⟩ => ?_)
  obtain ctx₂ := ctx₁.next hc K₂ edi_clob esp_clob U₂ (winW_winWr h7)
  obtain g₂ : s₂.gpr .esi = BitVec.ofNat 32 i := by rw [K₂.1 _ esi_clob, g₁]
  obtain U₂' : Unch base (pW c winWr) s.mem s₂.mem := by rw [← m₁]; exact U₂
  obtain tbl₂ : STblOk c base P s₂.mem := I.tbl.unch h7 U₂' hfit (below (by decide))
  -- The digit's magnitude, and its entry.
  refine WP.seq (WP.mono (swinDigit_ok hc ctx₂ hk (j := i) (by omega_using [hjn]) g₂)
    fun s₃ ⟨a₃, g₃, k₃⟩ => ?_)
  rw [hm] at a₃ g₃
  obtain m₃ : s₃.mem = s₂.mem := k₃.2.1
  obtain ctx₃ := ctx₂.same hc k₃.keeps (by decide) (by decide) m₃
  have ha8 : m % 8 < 2 ^ c.winW := by rw [h8]; exact Nat.mod_lt _ (by decide)
  refine WP.seq (WP.mono (winSel_ok hc ctx₃.scr ha8 g₃) fun s₄ ⟨V₄, k₄, O₄⟩ => ?_)
  obtain ctx₄ := ctx₃.next hc k₄ (by decide) (by decide) O₄.unch (winW_sel h7)
  rw [m₃] at V₄ O₄
  obtain U₄' : Unch base (pW c winWr) s₂.mem s₄.mem := unch_winWr_sel h7 O₄
  obtain ⟨tl, tr⟩ := tbl₂ (m % 8) ha8
  obtain r₄ : ∀ i ∈ [RX, RY, RZ], sv c base s₄ i = sv c base s₂ i := fun i hi =>
    O₄.wordsVal (d := c.sl i) (k := c.n)
      (Or.inl (sl_lt c (i := i) (j := TX) ((by decide : ∀ i ∈ [RX, RY, RZ], i < TX) i hi)))
      (by
        have := sl_le c h7 ((by decide : ∀ i ∈ [RX, RY, RZ], i < 45) i hi)
        have hsz : size = 8192 := rfl
        omega_using [this, hsz])
  -- `T = O` where the magnitude is zero.
  have a₄ : s₄.gpr .eax = BitVec.ofNat 32 m := by rw [k₄.1 _ (by decide), a₃]
  rw [Cfg.swinZero]
  refine WP.seq (WP.block_append (WP.mono (zeroMask_ok s₄ (by omega_using [hm8]) a₄) fun s₅ ⟨c₅, k₅⟩ => ?_))
  obtain m₅ : s₅.mem = s₄.mem := k₅.2.1
  obtain ctx₅ := ctx₄.same hc k₅.keeps (by decide) (by decide) m₅
  refine WP.mono (selSelf3_ok hc ctx₅.scr (decide (m = 0)) c₅ (o₁ := TX) (o₂ := TY) (o₃ := TZ)
    (x₁ := ZERO) (x₂ := ONEP) (x₃ := ZERO) (by decide) (by decide) (by decide))
    fun s₆ ⟨ex₆, ey₆, ez₆, k₆, U₆⟩ => ?_
  obtain ctx₆ := ctx₅.next hc k₆ (by decide) (by decide) U₆ (winW_slW h7 (by decide))
  have e45 : ∀ {i : Nat}, sv c base s₅ i = sv c base s₄ i := fun {i} => by
    show wordsVal s₅.mem _ _ _ = _; rw [m₅]
  obtain ⟨ltT₆, repT₆⟩ : (∀ i ∈ [TX, TY, TZ], sv c base s₆ i < c.C.p) ∧
      Rep c.C (fv c base s₆ TX) (fv c base s₆ TY) (fv c base s₆ TZ) (mul m P) := by
    by_cases h0 : m = 0
    · rw [decide_eq_true h0] at ex₆ ey₆ ez₆
      simp only [↓reduceIte] at ex₆ ey₆ ez₆
      refine ⟨fun i hi => ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl
        · rw [ex₆]; exact ctx₅.lt hc _ (by decide)
        · rw [ey₆]; exact ctx₅.lt hc _ (by decide)
        · rw [ez₆]; exact ctx₅.lt hc _ (by decide)
      · show Rep _ (toM _ _ (sv c base s₆ TX)) (toM _ _ (sv c base s₆ TY)) (toM _ _ (sv c base s₆ TZ)) _
        rw [ex₆, ey₆, ez₆, h0, mul0]
        exact ⟨ctx₅.fv_zero, by
          rw [show toM c.C.p (2 ^ (64 * c.n)) (sv c base s₅ ONEP) = fv c base s₅ ONEP from rfl,
            ctx₅.fv_onep hc]
          exact hC.one_ne_zero, ctx₅.fv_zero⟩
    · rw [decide_eq_false h0] at ex₆ ey₆ ez₆
      simp only [Bool.false_eq_true, ↓reduceIte] at ex₆ ey₆ ez₆
      obtain vx : sv c base s₄ TX = _ := V₄ 0 (by decide)
      obtain vy : sv c base s₄ TY = _ := V₄ 1 (by decide)
      obtain vz : sv c base s₄ TZ = _ := V₄ 2 (by decide)
      rw [e45, vx] at ex₆
      rw [e45, vy] at ey₆
      rw [e45, vz] at ez₆
      have he : (if m % 8 = 0 then 2 ^ c.winW else m % 8) = m := by
        rw [h8]
        by_cases hz : m % 8 = 0 <;> simp only [hz, ↓reduceIte] <;> omega_using [hm8, h0, hz]
      rw [he] at tr
      refine ⟨fun i hi => ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl
        · rw [ex₆]; exact tl 0 (by decide)
        · rw [ey₆]; exact tl 1 (by decide)
        · rw [ez₆]; exact tl 2 (by decide)
      · show Rep _ (toM _ _ (sv c base s₆ TX)) (toM _ _ (sv c base s₆ TY)) (toM _ _ (sv c base s₆ TZ)) _
        rw [ex₆, ey₆, ez₆]; exact tr
  -- `-T`, into `D`.
  rw [Cfg.swinNeg]
  rw [show fprog c.SP [.add (c.sl DX) (c.sl TX) (c.sl ZERO), .sub (c.sl DY) (c.sl ZERO) (c.sl TY),
      .add (c.sl DZ) (c.sl TZ) (c.sl ZERO)] =
    fprog c.SP (ofN negN c.rcbSlots (c.pt TX TY TZ) (c.pt ZERO ZERO ZERO) (c.pt DX DY DZ)) from rfl]
  refine WP.seq (WP.seq (WP.mono (ptOp_ok hc negN_ok (p₁ := TX) (p₂ := TY) (p₃ := TZ) (q₁ := ZERO)
    (q₂ := ZERO) (q₃ := ZERO) (o₁ := DX) (o₂ := DY) (o₃ := DZ) (by decide) (by decide) (by decide) ctx₆.scr
    ctx₆.mp (ctx₆.lt8 hc ltT₆ (fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hi
      rw [hi]; exact ctx₆.lt hc _ (by decide)))) fun s₇ ⟨K₇, U₇, L₇, V₇⟩ => ?_))
  obtain ctx₇ := ctx₆.next hc K₇ edi_clob esp_clob U₇ (winW_pW h7 (by decide))
  obtain g₇ : s₇.gpr .esi = BitVec.ofNat 32 i := by
    rw [K₇.1 _ esi_clob, k₆.1 _ (by decide), k₅.1 _ (by decide), k₄.1 _ (by decide), k₃.1 _ (by decide), g₂]
  obtain V₇' := V₇.trans (negN_run _)
  simp only [Prod.mk.injEq] at V₇'
  obtain dy₇ : fv c base s₇ DY = -fv c base s₆ TY := by
    rw [V₇'.2.1]
    show fv c base s₆ ZERO - fv c base s₆ TY = _
    rw [ctx₆.fv_zero]; grind
  obtain t₇ : ∀ i ∈ [TX, TY, TZ], sv c base s₇ i = sv c base s₆ i := fun i hi =>
    sv_pW U₇ h7 hn ((by decide : ∀ i ∈ [TX, TY, TZ], i < 45) i hi)
      ((by decide : ∀ i ∈ [TX, TY, TZ], i ∉ [T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP]) i hi)
  -- `T`'s `y` kept where the digit is not negative.
  have hw4 : c.winScan.w = 4 := by show c.winW + 1 = 4; rw [h3]
  refine WP.block_append (WP.mono (signMask_ok c.winScan ctx₇.scr (k := k) (j := i) (N := 8 * c.C.len)
    (by rw [hw4]; decide) (by rw [hw4]; decide) (by rw [hw4]; omega_using [hjn, hJ])
    (by show bitsAt c.n 0 + _ ≤ _; omega_using [hbit0, hlen]) g₇ ctx₇.bits) fun s₈ ⟨c₈, k₈⟩ => ?_)
  rw [hw4] at c₈
  obtain m₈ : s₈.mem = s₇.mem := k₈.2.1
  obtain ctx₈ := ctx₇.same hc k₈.keeps (by decide) (by decide) m₈
  refine WP.mono (selSlot_ok hc ctx₈.scr (decide (combWin 4 k i < 8)) c₈ (o := TY) (a := DY) (x := TY)
    (by decide) (by decide) (by decide)) fun s₉ ⟨ey₉, k₉, U₉⟩ => ?_
  obtain ctx₉ := ctx₈.next hc k₉ (by decide) (by decide) U₉ (winW_slW h7 (by decide))
  have e78 : ∀ {i : Nat}, sv c base s₈ i = sv c base s₇ i := fun {i} => by
    show wordsVal s₈.mem _ _ _ = _; rw [m₈]
  obtain o₉ : ∀ {i}, i < 45 → i ≠ TY → sv c base s₉ i = sv c base s₇ i := fun {i} hi hne =>
    (sv_unch U₉ h7 hn hi (apart_slW (l := [TY]) (by simpa using hne))).trans e78
  obtain ltT₉ : ∀ i ∈ [TX, TY, TZ], sv c base s₉ i < c.C.p := fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · rw [o₉ (by decide) (by decide), t₇ _ (by decide)]; exact ltT₆ _ (by decide)
    · rw [ey₉, e78, e78]
      split
      · rw [t₇ _ (by decide)]; exact ltT₆ _ (by decide)
      · exact L₇ _ (by decide)
    · rw [o₉ (by decide) (by decide), t₇ _ (by decide)]; exact ltT₆ _ (by decide)
  obtain repT₉ : Rep c.C (fv c base s₉ TX) (fv c base s₉ TY) (fv c base s₉ TZ)
      (if combWin 4 k i < 8 then mul m P else negPt (mul m P)) := by
    show Rep _ (toM _ _ (sv c base s₉ TX)) (toM _ _ (sv c base s₉ TY)) (toM _ _ (sv c base s₉ TZ)) _
    rw [o₉ (by decide) (by decide), t₇ _ (by decide), o₉ (i := TZ) (by decide) (by decide),
      t₇ TZ (by decide), ey₉, e78, e78]
    by_cases hw8 : combWin 4 k i < 8
    · simp only [hw8, decide_true, ↓reduceIte]
      rw [t₇ _ (by decide)]; exact repT₆
    · simp only [hw8, decide_false, Bool.false_eq_true, ↓reduceIte]
      have := repT₆.negY
      rw [← dy₇] at this
      exact this
  obtain r₉ : ∀ i ∈ [RX, RY, RZ], sv c base s₉ i = sv c base s₂ i := fun i hi => by
    have h45 := (by decide : ∀ i ∈ [RX, RY, RZ], i < 45) i hi
    exact (o₉ h45 ((by decide : ∀ i ∈ [RX, RY, RZ], i ≠ TY) i hi)).trans
      ((sv_pW U₇ h7 hn h45
        ((by decide : ∀ i ∈ [RX, RY, RZ], i ∉ [T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP]) i hi)).trans
      ((sv_unch U₆ h7 hn h45 (apart_slW ((by decide : ∀ i ∈ [RX, RY, RZ], i ∉ [TX, TY, TZ]) i hi))).trans
        (e45.trans (r₄ i hi))))
  obtain ltR₉ : ∀ i ∈ [RX, RY, RZ], sv c base s₉ i < c.C.p := fun i hi => by rw [r₉ i hi]; exact L₂ i hi
  obtain repR₉ : Rep c.C (fv c base s₉ RX) (fv c base s₉ RY) (fv c base s₉ RZ)
      (dblPt (mul (swPre k (i + 1)) P) 4) := by
    show Rep _ (toM _ _ (sv c base s₉ RX)) (toM _ _ (sv c base s₉ RY)) (toM _ _ (sv c base s₉ RZ)) _
    rw [r₉ RX (by decide), r₉ RY (by decide), r₉ RZ (by decide)]; exact R₂
  have hTon : onCurve c.C (if combWin 4 k i < 8 then mul m P else negPt (mul m P)) = true := by
    split
    · exact hC.onCurve_mul hP _
    · exact onCurve_negPt (hC.onCurve_mul hP _)
  -- `D = R + T`.
  obtain ⟨N, hN, eN, hadd⟩ := winAdd_ok (c := c) hC
  rw [eN]
  refine WP.seq (WP.mono (ptOp_ok hc hN (p₁ := RX) (p₂ := RY) (p₃ := RZ) (q₁ := TX) (q₂ := TY)
    (q₃ := TZ) (o₁ := DX) (o₂ := DY) (o₃ := DZ) (by decide) (by decide) (by decide) ctx₉.scr
    ctx₉.mp (ctx₉.lt8 hc ltR₉ ltT₉)) fun s₁₀ ⟨K₁₀, U₁₀, L₁₀, V₁₀⟩ => ?_)
  obtain ctx₁₀ := ctx₉.next hc K₁₀ edi_clob esp_clob U₁₀ (winW_pW h7 (by decide))
  obtain repD₁₀ : Rep c.C (fv c base s₁₀ DX) (fv c base s₁₀ DY) (fv c base s₁₀ DZ) (mul (swPre k i) P) := by
    rw [← swin_pt hC hP k i, hm]
    have := hadd (fun y => tmv c.C c.n base s₉ (rcbσ c.rcbSlots (c.pt RX RY RZ) (c.pt TX TY TZ)
      (c.pt DX DY DZ) y)) (onCurve_dblPt hC _ hQ) hTon (ctx₉.fv_ap hc) (ctx₉.fv_b3p hc)
      nofun repR₉ repT₉
    simp only [Prod.mk.injEq] at V₁₀
    rw [V₁₀.1, V₁₀.2.1, V₁₀.2.2]; exact this
  -- `R = D`.
  refine WP.block_append (WP.mono (copySlots_ok hc ctx₁₀.scr (o₁ := RX) (o₂ := RY) (o₃ := RZ)
    (a₁ := DX) (a₂ := DY) (a₃ := DZ) (by decide) (by decide) (by decide))
    fun s₁₁ ⟨ex₁₁, ey₁₁, ez₁₁, k₁₁, U₁₁⟩ => ?_)
  obtain ctx₁₁ := ctx₁₀.next hc k₁₁ (by decide) (by decide) U₁₁ (winW_slW h7 (by decide))
  obtain g₁₁ : s₁₁.gpr .esi = BitVec.ofNat 32 i := by
    rw [k₁₁.1 _ (by decide), K₁₀.1 _ esi_clob, k₉.1 _ (by decide), k₈.1 _ (by decide), g₇]
  have U₆' := unch_winWr_slW (c := c) (base := base) (by decide) U₆
  have U₇' := unch_winWr_pW (c := c) (base := base) (by decide) U₇
  have U₉' := unch_winWr_slW (c := c) (base := base) (by decide) U₉
  have U₁₀' := unch_winWr_pW (c := c) (base := base) (by decide) U₁₀
  have U₁₁' := unch_winWr_slW (c := c) (base := base) (by decide) U₁₁
  rw [← m₅] at U₄'
  rw [← m₈] at U₇'
  refine wp_testCounter (by omega_using [hjn, hJ, hlen, h7]) g₁₁ fun s₁₂ f₁₂ z₁₂ =>
    WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, z₁₂⟩
  · exact ctx₁₁.same hc (f₁₂.keeps []) (by decide) (by decide) f₁₂.mem
  · rw [f₁₂.gpr, g₁₁]
  · exact (((((((((((I.keep.trans (k₁.mono (by decide))).trans (K₂.mono esi_powClob)).trans
      (k₃.keeps.mono (by decide))).trans (k₄.mono (by decide))).trans (k₅.keeps.mono (by decide))).trans
      (k₆.mono (by decide))).trans (K₇.mono esi_powClob)).trans (k₈.keeps.mono (by decide))).trans
      (k₉.mono (by decide))).trans (K₁₀.mono esi_powClob)).trans (k₁₁.mono (by decide))).trans (f₁₂.keeps _)
  · rw [f₁₂.mem]
    exact unch_winWr_trans I.unch (unch_winWr_trans U₂' (unch_winWr_trans U₄' (unch_winWr_trans U₆'
      (unch_winWr_trans U₇' (unch_winWr_trans U₉' (unch_winWr_trans U₁₀' U₁₁'))))))
  · rw [f₁₂.mem]
    exact ((((((tbl₂.unch h7 U₄' hfit (below (by decide))).unch h7 U₆' hfit (below (by decide))).unch h7
      U₇' hfit (below (by decide))).unch h7 U₉' hfit (below (by decide))).unch h7 U₁₀' hfit
      (below (by decide))).unch h7 U₁₁' hfit (below (by decide)))
  · intro i hi
    show wordsVal s₁₂.mem _ _ _ < _
    rw [f₁₂.mem]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact lt_of_eq_of_lt ex₁₁ (L₁₀ _ (by decide))
    · exact lt_of_eq_of_lt ey₁₁ (L₁₀ _ (by decide))
    · exact lt_of_eq_of_lt ez₁₁ (L₁₀ _ (by decide))
  · show Rep _ (toM _ _ (wordsVal s₁₂.mem _ _ _)) (toM _ _ (wordsVal s₁₂.mem _ _ _))
      (toM _ _ (wordsVal s₁₂.mem _ _ _)) _
    rw [f₁₂.mem]
    show Rep _ (toM _ _ (sv c base s₁₁ RX)) (toM _ _ (sv c base s₁₁ RY)) (toM _ _ (sv c base s₁₁ RZ)) _
    rw [ex₁₁, ey₁₁, ez₁₁]; exact repD₁₀
/-! SW6-END -/

/-! SWIN-END -/

end VG.Proof.Ecdsa.X86
