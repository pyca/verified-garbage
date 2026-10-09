import VerifiedGarbage.Proof.Weierstrass.JacMul
import VerifiedGarbage.Proof.Weierstrass.AArch64.WinSelect
import VerifiedGarbage.Proof.Weierstrass.AArch64.Comb
import VerifiedGarbage.Proof.Weierstrass.WinLay
import VerifiedGarbage.Proof.Weierstrass.Window
import VerifiedGarbage.Proof.Weierstrass.Jac
import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero

/-!
# The window method on AArch64: what its proofs share

The window method's offsets (`WinA`), what it reads and never writes (`WinFixed`),
its table (`TblOk`) and the loop's state (`WinSt`, `WinInv`); `Window` has the method.
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass


/-- `x ∈ l` for the window method's lists, by searching `l` (unfolding its
definitions by unification): cheaper than `win_mem`'s `simp`. -/
syntax "win_in" : tactic
macro_rules
  | `(tactic| win_in) => `(tactic| first
    | exact List.mem_cons_self
    | exact List.mem_cons_of_mem _ (by win_in)
    | exact List.mem_append_left _ (by win_in)
    | exact List.mem_append_right _ (by win_in))

/-- The window method's slots and modulus at offsets that loads and stores
can encode, and the table of bits at offsets `ldrb` can encode. -/
structure WinA (K : WinCfg) : Prop where
  sl : ∀ x ∈ winSlots K, x % 8 = 0
  mod : ModA K.M
  bits4 : K.bits + 3 < 4096
  /-- If the products are calls of a function, it computes them, and the
  slots but the table's are below its own working space. -/
  call : ∀ f m', Mont.callOf K.M = some (f, m') → Mont.ModOk K.M.n m' ∧
    ∀ x ∈ winRo K ++ winOther K, x + 8 * K.M.n ≤ Mont.own K.M.n

theorem WinA.al {K : WinCfg} (h : WinA K) : Aligned K.M (· ∈ winSlots K) :=
  ⟨h.sl, h.mod, fun f m' h' => (h.call f m' h').1⟩

theorem WinA.low {K : WinCfg} (h : WinA K) {l : List Nat} (hl : ∀ x ∈ l, x ∈ winRo K ++ winOther K) :
    Low K.M l :=
  Low.of_call fun f m' h' x hx => (h.call f m' h').2 x (hl x hx)


theorem winOther_mem {K : WinCfg} {x : Nat} (h : x ∈ winOther K) : x ∈ winSlots K := by
  simp only [winSlots, List.mem_append]; exact Or.inl (Or.inr h)

/-! ## The table -/

/-- What the window method reads and never writes, at the start: the curve's
`a` and `3b`, zero, `P`, and the table of the bits of `k`. -/
structure WinFixed (K : WinCfg) (C : Curve) (base : Addr) (s₀ : State) (P : Point C) (k : Nat) :
    Prop where
  a : tmv C K.M.n base s₀ K.S.a = Fin.ofNat C.p C.a
  b : tmv C K.M.n base s₀ K.S.b3 = Fin.ofNat C.p C.b
  ro_lt : ∀ x ∈ winRo K, wordsVal s₀.mem base x K.M.n < C.p
  zero : wordsVal s₀.mem base K.zero K.M.n = 0
  pt : Rep C (tmv C K.M.n base s₀ K.P.x) (tmv C K.M.n base s₀ K.P.y) (tmv C K.M.n base s₀ K.P.z) P
  bits : ∀ t < 4 * K.J, s₀.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0

/-- A slot read only keeps its number. -/
theorem _root_.VG.Proof.Weierstrass.WinLay.ro_val {K : WinCfg} {size : Nat} (hL : WinLay K size) {base : Addr} {m m' : Mem}
    (hU : Unch base (winW K) m m') (hn : base.toNat + size ≤ 2 ^ 64) {x : Nat} (hx : x ∈ winRo K) :
    wordsVal m' base x K.M.n = wordsVal m base x K.M.n :=
  hU.wordsVal (hL.ro_w hx) (by have := hL.lay.le x (winRo_slots K x hx); omega_using [hn, this])

theorem _root_.VG.Proof.Weierstrass.WinLay.ro_tmv {K : WinCfg} {C : Curve} {size : Nat} (hL : WinLay K size) {base : Addr}
    {s s' : State} (hU : Unch base (winW K) s.mem s'.mem) (hn : base.toNat + size ≤ 2 ^ 64) {x : Nat}
    (hx : x ∈ winRo K) : tmv C K.M.n base s' x = tmv C K.M.n base s x := by
  show toM _ _ _ = toM _ _ _; rw [hL.ro_val hU hn hx]

/-- What the window method writes misses the modulus. -/
theorem winW_mo {K : WinCfg} {size : Nat} (hL : WinLay K size) {m : Nat} {mem : Mem} {base : Addr}
    (hM : ModOkA K.M size m mem base) :
    ∀ w ∈ winW K, K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo := by
  intro w hw
  simp only [winW, List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · have := hL.lay.mo y (winWs_slots K y hy); dsimp only; omega_using [this]
  · have := hM.sep; dsimp only; omega_using [this]

/-- Entries `[1 … m]P` of the table. -/
def TblOk (K : WinCfg) (C : Curve) (base : Addr) (P : Point C) (m : Nat) (s : State) : Prop :=
  ∀ j, 1 ≤ j → j ≤ m →
    (∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z], wordsVal s.mem base x K.M.n < C.p) ∧
    Rep C (tmv C K.M.n base s (K.tblPt j).x) (tmv C K.M.n base s (K.tblPt j).y)
      (tmv C K.M.n base s (K.tblPt j).z) (mul j P)

/-! ## The loop -/

/-- What the loop writes: the slots but the table's, and the temporary area. -/
def loopW (K : WinCfg) : List (Nat × Nat) := (winOther K).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n)]

theorem loopW_sub (K : WinCfg) : ∀ w ∈ loopW K, w ∈ winW K := by
  intro w hw
  simp only [loopW, winW, winWs, List.mem_append, List.mem_map, List.mem_singleton] at hw ⊢
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · exact Or.inl ⟨y, Or.inl hy, rfl⟩
  · exact Or.inr rfl

/-- The table survives what the loop writes. -/
theorem TblOk.unch {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    {P : Point C} {s s' : State} (hT : TblOk K C base P 8 s) (hU : Unch base (loopW K) s.mem s'.mem)
    (hn : base.toNat + size ≤ 2 ^ 64) : TblOk K C base P 8 s' := by
  intro j h1 h8
  have T := hT j h1 h8
  have e : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
      wordsVal s'.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
    intro x hx
    obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K h1 h8 x hx
    have hs : K.tbl + 8 * K.M.n * i ∈ winSlots K := by
      simp only [winSlots, List.mem_append]; exact Or.inr (winTbl_mem K hi)
    refine hU.wordsVal (fun w hw => ?_) (by have := hL.lay.le _ hs; omega_using [hn, this])
    simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw
    rcases hw with ⟨y, hy, rfl⟩ | rfl
    · exact (hL.tbl_apart (List.mem_append_right _ hy) hi).symm
    · exact hL.lay.tmp _ hs
  refine ⟨fun x hx => by rw [e x hx]; exact T.1 x hx, ?_⟩
  have ex : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
      tmv C K.M.n base s' x = tmv C K.M.n base s x := fun x hx => by
    show toM _ _ _ = toM _ _ _; rw [e x hx]
  rw [ex _ (by simp), ex _ (by simp), ex _ (by simp)]
  exact T.2

/-- What holds throughout the loop, from `s₀` (the state before the table). -/
structure WinSt (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ s : State) :
    Prop where
  scr : Scr s base size
  keep : KeepRegs (combClob K.M.n) s₀ s
  unch : Unch base (winW K) s₀.mem s.mem
  mod : ModOkA K.M size C.p s.mem base
  tbl : TblOk K C base P 8 s

theorem clob_combClob {n : Nat} : ∀ r ∈ clob n, r ∈ combClob n := fun _ hr =>
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hr))

/-- The state after a change of `loopW` only. -/
theorem WinSt.next {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    {P : Point C} {s₀ s s' : State} (h : WinSt K C base size P s₀ s) (hs' : Scr s' base size)
    (hk : KeepRegs (combClob K.M.n) s s') (hU : Unch base (loopW K) s.mem s'.mem) :
    WinSt K C base size P s₀ s' :=
  ⟨hs', h.keep.trans hk, (h.unch.trans hU).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact loopW_sub K w hw,
    h.mod.unch hU (fun w hw => winW_mo hL h.mod w (loopW_sub K w hw)) h.scr.nowrap,
    h.tbl.unch hL hU h.scr.nowrap⟩

theorem WinSt.ro_tmv {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    {P : Point C} {s₀ s : State} (h : WinSt K C base size P s₀ s) (hF : WinFixed K C base s₀ P k) :
    tmv C K.M.n base s K.S.a = Fin.ofNat C.p C.a ∧ tmv C K.M.n base s K.S.b3 = Fin.ofNat C.p C.b ∧
      (∀ x ∈ winRo K, wordsVal s.mem base x K.M.n < C.p) ∧ wordsVal s.mem base K.zero K.M.n = 0 := by
  have hn := h.scr.nowrap
  refine ⟨?_, ?_, fun x hx => ?_, ?_⟩
  · rw [hL.ro_tmv h.unch hn (by simp [winRo])]; exact hF.a
  · rw [hL.ro_tmv h.unch hn (by simp [winRo])]; exact hF.b
  · rw [hL.ro_val h.unch hn hx]; exact hF.ro_lt x hx
  · rw [hL.ro_val h.unch hn (by simp [winRo])]; exact hF.zero

/-- The loop's invariant at `x19 = j`: `R` represents `[winE k J j]P`. -/
structure WinInv (K : WinCfg) (C : Curve) (base : Addr) (size k : Nat) (P : Point C) (s₀ s : State)
    (j : Nat) : Prop where
  st : WinSt K C base size P s₀ s
  x19 : s.gpr .x19 = BitVec.ofNat 64 j
  lt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p
  rep : Rep C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
    (mul (winE k K.J j) P)

end VG.Proof.Weierstrass.AArch64
