module

public import VerifiedGarbage.Impl.Ecdsa.X86.Window
public import VerifiedGarbage.Proof.Ecdsa.X86.Stages
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.JacMul
public import VerifiedGarbage.Proof.Weierstrass.CombW
public import VerifiedGarbage.Proof.Weierstrass.CombDigitW
public import VerifiedGarbage.Proof.Weierstrass.X86.TCombScan
import VerifiedGarbage.Proof.Ecdsa.X86.Lays
import VerifiedGarbage.Proof.Ecdsa.X86.Flags
import VerifiedGarbage.Proof.Weierstrass.X86.TCombRcb
import VerifiedGarbage.Proof.Weierstrass.X86.NafAdjust
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

/-- A byte of table 0 is apart from what the windows write. -/
theorem WinW.apart_bits {W : List (Nat × Nat)} (hW : WinW c W) (h7 : c.n < 10) {t : Nat} (ht : t < 64 * c.n) :
    ∀ w ∈ W, bitsAt c.n 0 + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n 0 + t := by
  intro w hw
  rw [bitsAt_eq]
  rcases hW w hw with ⟨h1, h2⟩ | ⟨-, h⟩ | h
  · rw [h1, h2]
    have := sl_below_wk c (i := TMP) (by decide)
    have := wk_eq c
    exact Or.inr (by omega_arith)
  · exact Or.inr (by omega_arith)
  · rw [winTbl_eq] at h
    exact Or.inl (by omega_arith)

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
  rw [tbl_unch hu h7 (j := 0) (by decide) ht' (hW.apart_bits h7 ht'), h.bits t ht]

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
theorem winQuad_ok (hc : CfgOk c) (hC : Law c.C) {base : Addr} {kk : Nat} {s : State}
    (ctx : WinCtx c base kk s) {Q : Point c.C} (hQ : onCurve c.C Q = true)
    (hlt : ∀ i ∈ [RX, RY, RZ], sv c base s i < c.C.p)
    (hR : Rep c.C (fv c base s RX) (fv c base s RY) (fv c base s RZ) Q) :
    WP isa c.winQuad s fun s' => Keeps clob s s' ∧ Unch base (pW c winWr) s.mem s'.mem ∧
      (∀ i ∈ [RX, RY, RZ], sv c base s' i < c.C.p) ∧
      Rep c.C (fv c base s' RX) (fv c base s' RY) (fv c base s' RZ) (dblPt Q c.winW) := by
  have h7 := hc.n10
  have hn0 := hc.n0
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  rw [Cfg.winQuad, Cfg.zeroPt, toJ_eq]
  -- To Jacobian coordinates, in `D`.
  refine WP.seq (WP.mono (ptOp_ok hc toJN_ok (p₁ := RX) (p₂ := RY) (p₃ := RZ) (q₁ := ZERO) (q₂ := ZERO)
    (q₃ := ZERO) (o₁ := DX) (o₂ := DY) (o₃ := DZ) (by decide) (by decide) (by decide) ctx.scr
    ctx.mp (ctx.lt8 hc hlt (ctx.lt_zero hc))) fun s₁ ⟨K₁, U₁, L₁, V₁⟩ => ?_)
  obtain ctx₁ := ctx.next hc K₁ edi_clob esp_clob U₁ (winW_pW h7 (by decide))
  obtain J₁ : InvJ c.C (fv c base s₁ DX) (fv c base s₁ DY) (fv c base s₁ DZ) Q :=
    InvJ.of_toJ hC hR ctx.fv_zero (V₁.trans (toJN_run _))
  -- The doublings, and back.
  refine WP.seq (WP.mono (winDbls_ok hc hC c.winW true ctx₁ hQ L₁ J₁)
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
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi hj
    rcases hi with rfl | rfl | rfl <;> rcases hj with h | h | h <;>
      first | exact x1 h | exact x2 h | exact x3 h | exact y1 h | exact y2 h | exact y3 h | exact z1 h
        | exact z2 h | exact z3 h
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
  have h16 := (pow_winW_le c).1
  unfold Cfg.winEntryAddr
  refine wp_mov fun s₁ u₁ => wp_movi fun s₂ u₂ => wp_mul fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_addS rfl fun s₅ u₅ _ => wp_addS rfl fun s₆ u₆ _ => WP.block_nil ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · have hm : s₃.gpr .eax = BitVec.ofNat 32 (16 * c.winPc * e) := by
      rw [u₃.eax, u₂.other _ (by decide), u₁.gpr, ge, u₂.gpr]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mul_comm]
    rw [u₆.gpr, u₅.gpr, u₄.gpr, readSrc] at *
    all_goals sorry
  · sorry
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

end VG.Proof.Ecdsa.X86
