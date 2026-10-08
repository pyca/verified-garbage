import VerifiedGarbage.Impl.Weierstrass.X86.Window
import VerifiedGarbage.Proof.Weierstrass.X86.TComb
import VerifiedGarbage.Proof.Weierstrass.X86.WinLay
import VerifiedGarbage.Proof.Weierstrass.WinLay
import VerifiedGarbage.Proof.Weierstrass.Window
import VerifiedGarbage.Proof.Weierstrass.Jac

/-!
# The window method on x86 (32-bit): the table and the additions

As on AArch64 (`Proof/Weierstrass/AArch64/Window.lean`): the table `[1 … 8]P`
(`build_ok`: `P`, then `[m + 1]P = [m]P + P` by the complete addition for
`a = -3`, `addT_ok`), and the addition of an entry to `R` (`winAdd_ok`: into
`D`, then copied). `WinEntry.lean` selects the entry of a digit, `WinQuad.lean`
multiplies `R` by 16, and `WinLoop.lean` is the loop.
-/

namespace VG.Proof.Weierstrass.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

open Spec.Weierstrass

variable {F : Spec.Weierstrass.Mont.Modulus} {pm : Nat}

/-! ## The complete addition into `R` -/

/-- After a sum into `D` copied to `R`: `R` holds `v`, the sum's value. -/
structure SumPostW (K : WinCfg) (wk : Nat) (C : Curve) (base : Addr) (size : Nat) (v : Fe C × Fe C × Fe C)
    (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs clob s s'
  unch : Unch base (loopWX K wk) s.mem s'.mem
  lt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p
  val : (tmv C K.M.n base s' K.R.x, tmv C K.M.n base s' K.R.y, tmv C K.M.n base s' K.R.z) = v

theorem winOther_mem {K : WinCfg} {x : Nat} (h : x ∈ winOther K) : x ∈ winSlots K := by
  simp only [winSlots, List.mem_append]; exact Or.inl (Or.inr h)

/-- `R` and `D`, written and apart. -/
theorem winRD {K : WinCfg} {size wk : Nat} (hL : WinLay K size) (_hAcc : WinWk K F pm size wk) :
    (∀ x ∈ [K.R.x, K.R.y, K.R.z, K.D.x, K.D.y, K.D.z], x + 8 * K.M.n ≤ size) ∧
    (∀ x ∈ [K.R.x, K.R.y, K.R.z], ∀ y ∈ [K.R.x, K.R.y, K.R.z, K.D.x, K.D.y, K.D.z], x ≠ y →
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x) ∧
    (∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∉ [K.D.x, K.D.y, K.D.z]) ∧
    (K.R.x ≠ K.R.y ∧ K.R.x ≠ K.R.z ∧ K.R.y ≠ K.R.z) := by
  obtain ⟨rxy, rxz, ryz, hRD, -, -, -, -, -, -⟩ := hL.other_ne
  have hw : ∀ z ∈ [K.R.x, K.R.y, K.R.z, K.D.x, K.D.y, K.D.z], z ∈ winWs K := by
    intro z hz
    refine winOther_ws K z ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> win_mem
  refine ⟨fun x hx => hL.lay.le x (winWs_slots K x (hw x hx)),
    fun x hx y hy hxy => hL.apart₂ (hw x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h <;> simp [h])) (hw y hy) hxy, fun x hx hd => ?_, rxy, rxz, ryz⟩
  refine hRD x hx (List.mem_append_right _ ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl <;> simp [rcbW]

/-- A sum into `D` (the field program `ops`, writing `rcbW K.S K.D` and computing `v`),
then copied to `R`. -/
theorem winCopy_ok {K : WinCfg} {C : Curve} {base : Addr} {size wk : Nat} (hL : WinLay K size) (hAcc : WinWk K F C.p size wk)
    {ops : List FOp} {V : List Nat} {E' : Nat → Fe C} {v : Fe C × Fe C × Fe C}
    {s : State} (hs : Scr s base size)
    (W : WP isa (fprog F ops) s fun s' => ProgKeep K.M base wk (rcbW K.S K.D) s s' ∧
      Inv K.M base size C.p (· ∈ winSlots K) ([K.D.x, K.D.y, K.D.z] ++ V) E' s' ∧
      (E' K.D.x, E' K.D.y, E' K.D.z) = v) :
    WP isa (.seq (fprog F ops) (.block (copyPt K.M.n K.R K.D))) s (SumPostW K wk C base size v s) := by
  refine WP.seq ((WP.mono W fun s₁ h₁ => ?_))
  obtain ⟨k₁, I₁, v₁⟩ := h₁
  obtain ⟨hle, hap, hne, ho⟩ := winRD hL hAcc
  refine WP.mono (copyPt_ok (k₁.scr hs) hle hap hne ho) fun s₂ ⟨wx, wy, wz, k₂, U₂⟩ => ?_
  have hDx : K.D.x ∈ [K.D.x, K.D.y, K.D.z] ++ V := by simp
  have hDy : K.D.y ∈ [K.D.x, K.D.y, K.D.z] ++ V := by simp
  have hDz : K.D.z ∈ [K.D.x, K.D.y, K.D.z] ++ V := by simp
  refine ⟨(k₁.scr hs).of_keepRegs k₂ (by decide), ?_, ?_, ?_, ?_⟩
  · have c1 : ∀ r ∈ [Reg.eax], r ∈ clob := by intro r hr; simp at hr; subst hr; simp [clob]
    exact Keeps.trans ⟨k₁.gpr, k₁.rd, k₁.wr⟩ (k₂.mono c1)
  · refine (k₁.unch.trans U₂).mono ?_
    intro w hw
    simp only [loopWX, winOther, rcbW, progW, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      List.cons_append, List.nil_append] at hw ⊢
    grind
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [wx]; exact I₁.lt _ hDx
    · rw [wy]; exact I₁.lt _ hDy
    · rw [wz]; exact I₁.lt _ hDz
  · rw [← v₁]
    show (toM _ _ _, toM _ _ _, toM _ _ _) = _
    rw [wx, wy, wz, I₁.val _ hDx, I₁.val _ hDy, I₁.val _ hDz]

/-- `R = R + E` by Algorithm 4 into `D`, then copied. -/
theorem winAdd_ok {K : WinCfg} {C : Curve} {base : Addr} {size wk : Nat} (hL : WinLay K size) (hAcc : WinWk K F C.p size wk)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {s : State} (hs : Scr s base size)
    (hM : ModOkW K.M size C.p s.mem base)
    (hlt : ∀ x ∈ rcbR K.S K.R K.E, wordsVal s.mem base x K.M.n < C.p) :
    WP isa (.seq (fprog F (rcb3 K.S K.R K.E K.D)) (.block (copyPt K.M.n K.R K.D))) s
      (SumPostW K wk C base size (VG.Proof.Weierstrass.rcbAdd3 (tmv C K.M.n base s K.S.b3)
        (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
        (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z)) s) := by
  have hO : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.R K.E, x ∈ winSlots K := by
    intro x hx
    simp only [rcbW, rcbR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> win_mem
  have hI : Inv K.M base size C.p (· ∈ winSlots K) (rcbR K.S K.R K.E) (tmv C K.M.n base s) s :=
    ⟨hs, hM, fun x hx => hO x (List.mem_append_right _ hx), hlt, fun _ _ => rfl⟩
  exact winCopy_ok hL hAcc hs (rcb3_ok hL.lay hAcc.acc hp (hL.rcbApart_D (Or.inr rfl)) hO hI (fun x hx => hx))

/-! ## The table -/

/-- What the window method reads and never writes, at the start: the curve's
`a` and `b`, zero, `P`, and the table of the bits of `k`. -/
structure WinFixed (K : WinCfg) (C : Curve) (base : Addr) (s₀ : State) (P : Point C) (k : Nat) :
    Prop where
  a : tmv C K.M.n base s₀ K.S.a = Fin.ofNat C.p C.a
  b : tmv C K.M.n base s₀ K.S.b3 = Fin.ofNat C.p C.b
  ro_lt : ∀ x ∈ winRo K, wordsVal s₀.mem base x K.M.n < C.p
  zero : wordsVal s₀.mem base K.zero K.M.n = 0
  pt : Rep C (tmv C K.M.n base s₀ K.P.x) (tmv C K.M.n base s₀ K.P.y) (tmv C K.M.n base s₀ K.P.z) P
  bits : ∀ t < 4 * K.J, s₀.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0

/-- A slot read only keeps its number. -/
theorem winRo_val {K : WinCfg} {size wk : Nat} (hL : WinLay K size) (hAcc : WinWk K F pm size wk) {base : Addr}
    {m m' : Mem} (hU : Unch base (winWX K wk) m m') (hn : base.toNat + size ≤ 2 ^ 32) {x : Nat}
    (hx : x ∈ winRo K) : wordsVal m' base x K.M.n = wordsVal m base x K.M.n :=
  hU.wordsVal (winRo_apart hL hAcc hx) (by have := hL.lay.le x (winRo_slots K x hx); omega)

theorem winRo_tmv {K : WinCfg} {C : Curve} {size wk : Nat} (hL : WinLay K size) (hAcc : WinWk K F C.p size wk)
    {base : Addr} {s s' : State} (hU : Unch base (winWX K wk) s.mem s'.mem) (hn : base.toNat + size ≤ 2 ^ 32)
    {x : Nat} (hx : x ∈ winRo K) : tmv C K.M.n base s' x = tmv C K.M.n base s x := by
  show toM _ _ _ = toM _ _ _; rw [winRo_val hL hAcc hU hn hx]

/-- What the window method writes misses the modulus. -/
theorem winW_mo {K : WinCfg} {size wk : Nat} (hL : WinLay K size) (hAcc : WinWk K F pm size wk) {m : Nat} {mem : Mem} {base : Addr}
    (hM : ModOkW K.M size m mem base) :
    ∀ w ∈ winWX K wk, K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo := by
  intro w hw
  simp only [winWX, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with ⟨y, hy, rfl⟩ | rfl | rfl | rfl
  · have := hL.lay.mo y (winWs_slots K y hy); dsimp only; omega
  · have := hM.sep; dsimp only; omega
  · exact Or.inl hAcc.acc.mo
  · have := hAcc.acc.mo; have := hAcc.wk_le; exact Or.inl (by dsimp only [Mont.outW]; omega)

/-- Entries `[1 … m]P` of the table. -/
def TblOk (K : WinCfg) (C : Curve) (base : Addr) (P : Point C) (m : Nat) (s : State) : Prop :=
  ∀ j, 1 ≤ j → j ≤ m →
    (∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z], wordsVal s.mem base x K.M.n < C.p) ∧
    Rep C (tmv C K.M.n base s (K.tblPt j).x) (tmv C K.M.n base s (K.tblPt j).y)
      (tmv C K.M.n base s (K.tblPt j).z) (mul j P)

/-- The table's invariant: entries `[1 … m]P` built. -/
structure BuildInv (K : WinCfg) (wk : Nat) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (m : Nat) (s : State) : Prop where
  scr : Scr s base size
  keep : KeepRegs clob s₀ s
  unch : Unch base (winWX K wk) s₀.mem s.mem
  mod : ModOkW K.M size C.p s.mem base
  tbl : TblOk K C base P m s

theorem tblPt_slots (K : WinCfg) {m : Nat} (h1 : 1 ≤ m) (h8 : m ≤ 8) :
    ∀ x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z], x ∈ winSlots K ∧ x ∈ winWs K := by
  intro x hx
  obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K h1 h8 x hx
  refine ⟨?_, winTbl_ws K hi⟩
  simp only [winSlots, List.mem_append]
  exact Or.inr (winTbl_mem K hi)

/-- The slots of entry `j` are apart from what the addition into entry
`m + 1 ≠ j` writes. -/
theorem tbl_apart_add {K : WinCfg} {size wk : Nat} (hL : WinLay K size) (hAcc : WinWk K F pm size wk) {j m : Nat} (hj1 : 1 ≤ j)
    (hj8 : j ≤ 8) (hm1 : 1 ≤ m + 1) (hm8 : m + 1 ≤ 8) (hjm : j ≠ m + 1) :
    ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
      ∀ w ∈ progW K.M wk (rcbW K.S (K.tblPt (m + 1))),
        x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro x hx w hw
  obtain ⟨i, hi, rfl, hi₁, hi₂⟩ := tblPt_mem K hj1 hj8 x hx
  simp only [progW, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with ⟨y, hy, rfl⟩ | rfl | rfl | rfl
  · have ets : rcbW K.S (K.tblPt (m + 1)) = [K.S.t0, K.S.t1, K.S.t2, K.S.t3, K.S.t4, K.S.t5] ++
        [(K.tblPt (m + 1)).x, (K.tblPt (m + 1)).y, (K.tblPt (m + 1)).z] := rfl
    rw [ets, List.mem_append] at hy
    dsimp only
    rcases hy with hy | hy
    · exact (hL.tbl_apart (rcbW_mem_other y hy) hi).symm
    · obtain ⟨i', hi', rfl, hi'₁, hi'₂⟩ := tblPt_mem K hm1 hm8 y hy
      exact winTbl_apart K (by omega)
  · exact hL.lay.tmp _ (by
      simp only [winSlots, List.mem_append]; exact Or.inr (winTbl_mem K hi))
  · exact Or.inl (hAcc.acc.sl _ (List.mem_append_right _ (winTbl_mem K hi)))
  · have := hAcc.acc.sl _ (List.mem_append_right _ (winTbl_mem K hi)); have := hAcc.wk_le
    exact Or.inl (by dsimp only [Mont.outW]; omega)

/-- `[m + 1]P = [m]P + P`. -/
theorem addT_ok {K : WinCfg} {C : Curve} {base : Addr} {size wk k : Nat} (hL : WinLay K size) (hAcc : WinWk K F C.p size wk)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) {s₀ : State} (hF : WinFixed K C base s₀ P k) {m : Nat} (h1 : 1 ≤ m)
    (h7 : m ≤ 7) {s : State} (hI : BuildInv K wk C base size P s₀ m s) :
    WP isa (fprog F (rcb3 K.S (K.tblPt m) (K.tblPt 1) (K.tblPt (m + 1)))) s
      (BuildInv K wk C base size P s₀ (m + 1)) := by
  have hn := hI.scr.nowrap
  have tb : tmv C K.M.n base s K.S.b3 = Fin.ofNat C.p C.b := by
    rw [winRo_tmv hL hAcc hI.unch hn (by simp [winRo])]; exact hF.b
  have ro_lt : ∀ x ∈ winRo K, wordsVal s.mem base x K.M.n < C.p := fun x hx => by
    rw [winRo_val hL hAcc hI.unch hn hx]; exact hF.ro_lt x hx
  have Tm := hI.tbl m h1 (Nat.le_refl _)
  have T1 := hI.tbl 1 (Nat.le_refl _) h1
  have sm := tblPt_slots K (m := m) h1 (by omega)
  have s1 := tblPt_slots K (m := 1) (Nat.le_refl _) (by omega)
  have so := tblPt_slots K (m := m + 1) (by omega) (by omega)
  have hO : ∀ x ∈ rcbW K.S (K.tblPt (m + 1)) ++ rcbR K.S (K.tblPt m) (K.tblPt 1), x ∈ winSlots K := by
    intro x hx
    simp only [rcbW, rcbR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    any_goals (win_mem; done)
    · exact (so (K.tblPt (m + 1)).x (by simp)).1
    · exact (so (K.tblPt (m + 1)).y (by simp)).1
    · exact (so (K.tblPt (m + 1)).z (by simp)).1
    · exact (sm (K.tblPt m).x (by simp)).1
    · exact (sm (K.tblPt m).y (by simp)).1
    · exact (sm (K.tblPt m).z (by simp)).1
    · exact (s1 (K.tblPt 1).x (by simp)).1
    · exact (s1 (K.tblPt 1).y (by simp)).1
    · exact (s1 (K.tblPt 1).z (by simp)).1
  have hlt : ∀ x ∈ rcbR K.S (K.tblPt m) (K.tblPt 1), wordsVal s.mem base x K.M.n < C.p := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ro_lt _ (by simp [winRo])
    · exact ro_lt _ (by simp [winRo])
    · exact Tm.1 _ (by simp)
    · exact Tm.1 _ (by simp)
    · exact Tm.1 _ (by simp)
    · exact T1.1 _ (by simp)
    · exact T1.1 _ (by simp)
    · exact T1.1 _ (by simp)
  have hI' : Inv K.M base size C.p (· ∈ winSlots K) (rcbR K.S (K.tblPt m) (K.tblPt 1))
      (tmv C K.M.n base s) s :=
    ⟨hI.scr, hI.mod, fun x hx => hO x (List.mem_append_right _ hx), hlt, fun _ _ => rfl⟩
  have W := rcb3_ok hL.lay hAcc.acc hp (hL.rcbApart_tbl h1 h7) hO hI' (fun x hx => hx)
  refine (WP.mono W fun s₁ h₁ => ?_)
  obtain ⟨k₁, I₁, v₁⟩ := h₁
  have hWrites : ∀ w ∈ progW K.M wk (rcbW K.S (K.tblPt (m + 1))),
      w ∈ winWX K wk := by
    intro w hw
    simp only [winWX, progW, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with ⟨y, hy, rfl⟩ | rfl | rfl | rfl
    · refine Or.inl ⟨y, ?_, rfl⟩
      have ets : rcbW K.S (K.tblPt (m + 1)) = [K.S.t0, K.S.t1, K.S.t2, K.S.t3, K.S.t4, K.S.t5] ++
          [(K.tblPt (m + 1)).x, (K.tblPt (m + 1)).y, (K.tblPt (m + 1)).z] := rfl
      rw [ets, List.mem_append] at hy
      rcases hy with hy | hy
      · exact winOther_ws K y (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> win_mem)
      · exact (so y hy).2
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  have U₁ := k₁.unch
  have hox : (K.tblPt (m + 1)).x ∈ [(K.tblPt (m + 1)).x, (K.tblPt (m + 1)).y, (K.tblPt (m + 1)).z] ++
      rcbR K.S (K.tblPt m) (K.tblPt 1) := by simp
  have hoy : (K.tblPt (m + 1)).y ∈ [(K.tblPt (m + 1)).x, (K.tblPt (m + 1)).y, (K.tblPt (m + 1)).z] ++
      rcbR K.S (K.tblPt m) (K.tblPt 1) := by simp
  have hoz : (K.tblPt (m + 1)).z ∈ [(K.tblPt (m + 1)).x, (K.tblPt (m + 1)).y, (K.tblPt (m + 1)).z] ++
      rcbR K.S (K.tblPt m) (K.tblPt 1) := by simp
  refine ⟨k₁.scr hI.scr, hI.keep.trans ⟨k₁.gpr, k₁.rd, k₁.wr⟩,
    (hI.unch.trans U₁).mono fun w hw => ?_, hI.mod.unch U₁ (fun w hw => winW_mo hL hAcc hI.mod w (hWrites w hw)) (by omega),
    fun j hj1 hjm => ?_⟩
  · rcases List.mem_append.mp hw with hw | hw
    · exact hw
    · exact hWrites w hw
  rcases Nat.lt_or_ge j (m + 1) with hj | hj
  · -- An entry built before keeps its numbers.
    have ap := tbl_apart_add hL hAcc (j := j) (m := m) hj1 (by omega) (by omega) (by omega) (by omega)
    have e : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
        wordsVal s₁.mem base x K.M.n = wordsVal s.mem base x K.M.n := fun x hx =>
      U₁.wordsVal (ap x hx) (by have := hL.lay.le x ((tblPt_slots K hj1 (by omega)) x hx).1; omega)
    have Tj := hI.tbl j hj1 (by omega)
    refine ⟨fun x hx => by rw [e x hx]; exact Tj.1 x hx, ?_⟩
    have ex : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
        tmv C K.M.n base s₁ x = tmv C K.M.n base s x := fun x hx => by
      show toM _ _ _ = toM _ _ _; rw [e x hx]
    rw [ex _ (by simp), ex _ (by simp), ex _ (by simp)]
    exact Tj.2
  · obtain rfl : j = m + 1 := by omega
    refine ⟨fun x hx => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact I₁.lt _ hox
      · exact I₁.lt _ hoy
      · exact I₁.lt _ hoz
    · have hS : (tmv C K.M.n base s₁ (K.tblPt (m + 1)).x, tmv C K.M.n base s₁ (K.tblPt (m + 1)).y,
          tmv C K.M.n base s₁ (K.tblPt (m + 1)).z) = VG.Proof.Weierstrass.rcbAdd3
            (tmv C K.M.n base s K.S.b3)
            (tmv C K.M.n base s (K.tblPt m).x) (tmv C K.M.n base s (K.tblPt m).y)
            (tmv C K.M.n base s (K.tblPt m).z) (tmv C K.M.n base s (K.tblPt 1).x)
            (tmv C K.M.n base s (K.tblPt 1).y) (tmv C K.M.n base s (K.tblPt 1).z) := by
        rw [← v₁]
        show (toM _ _ _, toM _ _ _, toM _ _ _) = _
        rw [I₁.val _ hox, I₁.val _ hoy, I₁.val _ hoz]
      rw [tb] at hS
      have hR := hC.add3 hM3 (hC.onCurve_mul hP m) (hC.onCurve_mul hP 1) Tm.2 T1.2 hS.symm
      rw [hC.add_mul_mul hP] at hR
      exact hR

/-- `[m + 1]P = [m]P + P` for `m = 1 … i`. -/
theorem adds_ok {K : WinCfg} {C : Curve} {base : Addr} {size wk k : Nat} (hL : WinLay K size) (hAcc : WinWk K F C.p size wk)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) {s₀ : State} (hF : WinFixed K C base s₀ P k) :
    ∀ i ≤ 7, ∀ s, BuildInv K wk C base size P s₀ 1 s →
      WP isa (WinCfg.adds K F i) s (BuildInv K wk C base size P s₀ (i + 1))
  | 0, _, _, h => WP.block_nil h
  | i + 1, hi, s, h => by
    rw [WinCfg.adds]
    exact WP.seq (WP.mono (adds_ok hL hAcc hp hC hM3 hP hF i (by omega) s h) fun s₁ h₁ =>
      addT_ok hL hAcc hp hC hM3 hP hF (m := i + 1) (by omega) (by omega) h₁)

/-- The table `[1 … 8]P`. -/
theorem build_ok {K : WinCfg} {C : Curve} {base : Addr} {size wk k : Nat} (hL : WinLay K size) (hAcc : WinWk K F C.p size wk)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) {s : State} (hs : Scr s base size) (hM : ModOkW K.M size C.p s.mem base)
    (hF : WinFixed K C base s P k) :
    WP isa (WinCfg.build K F) s (BuildInv K wk C base size P s 8) := by
  have hn := hs.nowrap
  rw [WinCfg.build]
  refine WP.seq (WP.mono (?_ : WP isa (.block (copyPt K.M.n (K.tblPt 1) K.P)) s
    (BuildInv K wk C base size P s 1)) fun s' h => adds_ok hL hAcc hp hC hM3 hP hF 7 (by decide) s' h)
  have s1 := tblPt_slots K (m := 1) (Nat.le_refl _) (by omega)
  have mP : ∀ x ∈ [K.P.x, K.P.y, K.P.z], x ∈ winRo K ++ winOther K := fun x hx =>
    List.mem_append_left _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [winRo])
  have pT : ∀ x ∈ [K.P.x, K.P.y, K.P.z], ∀ y ∈ [(K.tblPt 1).x, (K.tblPt 1).y, (K.tblPt 1).z],
      y + 8 * K.M.n ≤ x ∨ x + 8 * K.M.n ≤ y := by
    intro x hx y hy
    obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K (m := 1) (Nat.le_refl _) (by omega) y hy
    exact (hL.tbl_apart (mP x hx) hi).symm
  have ne₁ : (K.tblPt 1).x ≠ (K.tblPt 1).y := by rw [tblPt_x, tblPt_y]; exact hL.tbl_ne₂ (by omega)
  have ne₂ : (K.tblPt 1).x ≠ (K.tblPt 1).z := by rw [tblPt_x, tblPt_z]; exact hL.tbl_ne₂ (by omega)
  have ne₃ : (K.tblPt 1).y ≠ (K.tblPt 1).z := by rw [tblPt_y, tblPt_z]; exact hL.tbl_ne₂ (by omega)
  have hle : ∀ x ∈ [(K.tblPt 1).x, (K.tblPt 1).y, (K.tblPt 1).z, K.P.x, K.P.y, K.P.z],
      x + 8 * K.M.n ≤ size := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h
    · exact hL.lay.le x (s1 x (by simp [h])).1
    · exact hL.lay.le x (s1 x (by simp [h])).1
    · exact hL.lay.le x (s1 x (by simp [h])).1
    all_goals exact hL.lay.le x (by
      have := mP x (by simp [h])
      simp only [winSlots, List.mem_append] at this ⊢; exact Or.inl this)
  have hap : ∀ x ∈ [(K.tblPt 1).x, (K.tblPt 1).y, (K.tblPt 1).z],
      ∀ y ∈ [(K.tblPt 1).x, (K.tblPt 1).y, (K.tblPt 1).z, K.P.x, K.P.y, K.P.z], x ≠ y →
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := by
    intro x hx y hy hxy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with h | h | h | h | h | h
    · exact hL.apart₂ (s1 x hx).2 (s1 y (by simp [h])).2 hxy
    · exact hL.apart₂ (s1 x hx).2 (s1 y (by simp [h])).2 hxy
    · exact hL.apart₂ (s1 x hx).2 (s1 y (by simp [h])).2 hxy
    · exact pT y (by simp [h]) x hx
    · exact pT y (by simp [h]) x hx
    · exact pT y (by simp [h]) x hx
  have hne : ∀ x ∈ [(K.tblPt 1).x, (K.tblPt 1).y, (K.tblPt 1).z], x ∉ [K.P.x, K.P.y, K.P.z] := by
    intro x hx hP'
    have := hL.lay.le x (s1 x hx).1
    have h0 := hL.n0
    rcases pT x hP' x hx with h | h <;> omega
  refine WP.mono (copyPt_ok hs hle hap hne ⟨ne₁, ne₂, ne₃⟩) fun s₁ ⟨vx, vy, vz, k₁, U₁⟩ => ?_
  have U : Unch base (winWX K wk) s.mem s₁.mem := by
    refine U₁.mono fun w hw => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [winWX, List.mem_append, List.mem_map]
    refine Or.inl ⟨w.1, ?_, ?_⟩
    · rcases hw with rfl | rfl | rfl
      · exact (s1 _ (by simp)).2
      · exact (s1 _ (by simp)).2
      · exact (s1 _ (by simp)).2
    · rcases hw with rfl | rfl | rfl <;> rfl
  have c1 : ∀ r ∈ [Reg.eax], r ∈ clob := by intro r hr; simp at hr; subst hr; simp [clob]
  refine ⟨hs.of_keepRegs k₁ (by decide), k₁.mono c1, U, hM.unch U (winW_mo hL hAcc hM) (by omega), fun j hj1 hj => ?_⟩
  obtain rfl : j = 1 := by omega
  refine ⟨fun x hx => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [vx]; exact hF.ro_lt _ (by simp [winRo])
    · rw [vy]; exact hF.ro_lt _ (by simp [winRo])
    · rw [vz]; exact hF.ro_lt _ (by simp [winRo])
  · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [vx, vy, vz, mul_one_pt]
    exact hF.pt

end VG.Proof.Weierstrass.X86
