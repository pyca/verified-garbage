import VerifiedGarbage.Proof.Weierstrass.AArch64.WinSelect
import VerifiedGarbage.Proof.Weierstrass.AArch64.Comb
import VerifiedGarbage.Proof.Weierstrass.WinLay
import VerifiedGarbage.Proof.Weierstrass.Window
import VerifiedGarbage.Proof.Weierstrass.Jac
import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero

/-!
# The window method on AArch64

The table `[1 … 8]P` (`build_ok`: `P`, then `[m + 1]P = [m]P + P` by the
complete addition), then, from `R = O`, iterations (`winStep_ok`) that multiply
`R` by 16 (`quad_ok`: four doublings in Jacobian coordinates, `jac_ok`, and
`Y = 1` where the result is `O`, `ySel_ok`) and add the entry of the digit (`winEntry_ok`: selected in
constant time, its `y` negated for a negative digit), so that `R`, which
represented `[winE k J (j+1)]P`, represents `[winE k J j]P` (`win_add`). After
all `J` digits `R` represents `[k - 8 Σ_{i<J} 16^i]P` (`window_ok`), for
`k < 16^J` whose bits are the table at `K.bits`.
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- The window method's slots and modulus at offsets that loads and stores
can encode. -/
structure WinA (K : WinCfg) : Prop where
  sl : ∀ x ∈ winSlots K, x % 8 = 0
  mod : ModA K.M

/-! ## The complete addition into `R` -/

/-- After a sum into `D` copied to `R`: `R` holds `v`, the sum's value. -/
structure SumPostW (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (v : Fe C × Fe C × Fe C)
    (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (clob K.M.n) s s'
  unch : Unch base ((winOther K).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n)]) s.mem s'.mem
  lt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p
  val : (tmv C K.M.n base s' K.R.x, tmv C K.M.n base s' K.R.y, tmv C K.M.n base s' K.R.z) = v

theorem winOther_mem {K : WinCfg} {x : Nat} (h : x ∈ winOther K) : x ∈ winSlots K := by
  simp only [winSlots, List.mem_append]; exact Or.inl (Or.inr h)

/-- A sum into `D` (the field program `ops`, writing `rcbW K.S K.D` and computing `v`),
then copied to `R`. -/
theorem winCopy_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) {ops : List FOp} {V : List Nat} {E' : Nat → Fe C} {v : Fe C × Fe C × Fe C}
    {s : State} (hs : Scr s base size)
    (W : WP isa (.block (fprog K.M ops)) s fun s' => ProgKeep K.M base (rcbW K.S K.D) s s' ∧
      Inv K.M base size C.p (· ∈ winSlots K) ([K.D.x, K.D.y, K.D.z] ++ V) E' s' ∧
      (E' K.D.x, E' K.D.y, E' K.D.z) = v) :
    WP isa (.seq (fprogB K.M ops) (.block (copyPt K.M.n K.R K.D))) s (SumPostW K C base size v s) := by
  have hn := hs.nowrap
  refine WP.seq ((fprogB_wp _ _).mpr (WP.mono W fun s₁ h₁ => ?_))
  obtain ⟨k₁, I₁, v₁⟩ := h₁
  obtain ⟨rxy, rxz, ryz, hRD, -, -, -, -, -, hD⟩ := hL.other_ne
  simp only [rcbW, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hD
  have hRD' : ∀ x ∈ [K.R.x, K.R.y, K.R.z], ∀ y ∈ [K.D.x, K.D.y, K.D.z], x ≠ y := by
    intro x hx y hy e
    subst e
    refine hRD x hx (List.mem_append_right _ ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl <;> simp [rcbW]
  have wR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ winWs K := fun x hx => winOther_ws K x (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> win_mem)
  have wD : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ winWs K := fun x hx => winOther_ws K x (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> win_mem)
  have ap : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.D.x, K.D.y, K.D.z],
      ∀ y ∈ [K.R.x, K.R.y, K.R.z, K.D.x, K.D.y, K.D.z], x ≠ y →
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := by
    intro x hx y hy hxy
    have hw : ∀ z ∈ [K.R.x, K.R.y, K.R.z, K.D.x, K.D.y, K.D.z], z ∈ winWs K := by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with h | h | h | h | h | h
      · exact wR z (by simp [h])
      · exact wR z (by simp [h])
      · exact wR z (by simp [h])
      · exact wD z (by simp [h])
      · exact wD z (by simp [h])
      · exact wD z (by simp [h])
    exact hL.apart₂ (hw x hx) (hw y hy) hxy
  have rd : ∀ {x y}, x ∈ [K.R.x, K.R.y, K.R.z] → y ∈ [K.D.x, K.D.y, K.D.z] → x ≠ y := fun hx hy =>
    hRD' _ hx _ hy
  have axd := ap K.R.x (by simp) K.D.x (by simp) (rd (by simp) (by simp))
  have ayd := ap K.R.y (by simp) K.D.y (by simp) (rd (by simp) (by simp))
  have azd := ap K.R.z (by simp) K.D.z (by simp) (rd (by simp) (by simp))
  have axy := ap K.R.x (by simp) K.R.y (by simp) rxy
  have axz := ap K.R.x (by simp) K.R.z (by simp) rxz
  have ayz := ap K.R.y (by simp) K.R.z (by simp) ryz
  have dyax := ap K.D.y (by simp) K.R.x (by simp) (Ne.symm (rd (by simp) (by simp)))
  have dzax := ap K.D.z (by simp) K.R.x (by simp) (Ne.symm (rd (by simp) (by simp)))
  have dzay := ap K.D.z (by simp) K.R.y (by simp) (Ne.symm (rd (by simp) (by simp)))
  have le : ∀ x ∈ winOther K, x + 8 * K.M.n ≤ size := fun x hx => hL.lay.le x (winOther_mem hx)
  have al : ∀ x ∈ winOther K, x % 8 = 0 := fun x hx => hA.sl x (winOther_mem hx)
  have b64 : ∀ x ∈ winOther K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := le x hx; omega_using [this, hn]
  have hs₁ := k₁.scr hs
  rw [copyPt, List.append_assoc, WP.block_append_iff]
  have W2 := copy_ok K.M.n hs₁ (le _ (by win_mem)) (le _ (by win_mem)) (al _ (by win_mem))
    (al _ (by win_mem)) (o := K.R.x) (a := K.D.x) (axd.imp (fun h => by omega_using [h]) id)
  refine WP.mono W2 fun s₂ h₂ => ?_
  obtain ⟨e₂, k₂, O₂⟩ := h₂
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  have W3 := copy_ok K.M.n hs₂ (le _ (by win_mem)) (le _ (by win_mem)) (al _ (by win_mem))
    (al _ (by win_mem)) (o := K.R.y) (a := K.D.y) (ayd.imp (fun h => by omega_using [h]) id)
  refine WP.mono W3 fun s₃ h₃ => ?_
  obtain ⟨e₃, k₃, O₃⟩ := h₃
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have W4 := copy_ok K.M.n hs₃ (le _ (by win_mem)) (le _ (by win_mem)) (al _ (by win_mem))
    (al _ (by win_mem)) (o := K.R.z) (a := K.D.z) (azd.imp (fun h => by omega_using [h]) id)
  refine WP.mono W4 fun s₄ h₄ => ?_
  obtain ⟨e₄, k₄, O₄⟩ := h₄
  have hDx : K.D.x ∈ [K.D.x, K.D.y, K.D.z] ++ V := by simp
  have hDy : K.D.y ∈ [K.D.x, K.D.y, K.D.z] ++ V := by simp
  have hDz : K.D.z ∈ [K.D.x, K.D.y, K.D.z] ++ V := by simp
  have bAx := b64 K.R.x (by win_mem)
  have bAy := b64 K.R.y (by win_mem)
  have bAz := b64 K.R.z (by win_mem)
  have bDy := b64 K.D.y (by win_mem)
  have bDz := b64 K.D.z (by win_mem)
  have wx : wordsVal s₄.mem base K.R.x K.M.n = wordsVal s₁.mem base K.D.x K.M.n := by
    rw [O₄.wordsVal axz bAx, O₃.wordsVal axy bAx, e₂]
  have wy : wordsVal s₄.mem base K.R.y K.M.n = wordsVal s₁.mem base K.D.y K.M.n := by
    rw [O₄.wordsVal ayz bAy, e₃, O₂.wordsVal dyax bDy]
  have wz : wordsVal s₄.mem base K.R.z K.M.n = wordsVal s₁.mem base K.D.z K.M.n := by
    rw [e₄, O₃.wordsVal dzay bDz, O₂.wordsVal dzax bDz]
  refine ⟨hs₃.of_keepRegs k₄ (by decide), ?_, ?_, ?_, ?_⟩
  · have c1 : ∀ r ∈ [Reg.x1], r ∈ clob K.M.n := by intro r hr; simp at hr; subst hr; simp [clob]
    exact ((⟨k₁.gpr, k₁.rd, k₁.wr, k₁.sp⟩ : KeepRegs (clob K.M.n) s s₁).trans
      ((k₂.mono c1).trans ((k₃.mono c1).trans (k₄.mono c1))))
  · refine (k₁.unch.trans (O₂.unch.trans (O₃.unch.trans O₄.unch))).mono ?_
    intro w hw
    simp only [winOther, rcbW, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
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
theorem winAdd_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {s : State} (hs : Scr s base size)
    (hM : ModOk K.M size C.p s.mem base)
    (hlt : ∀ x ∈ rcbR K.S K.R K.E, wordsVal s.mem base x K.M.n < C.p) :
    WP isa (.seq (fprogB K.M (rcb3 K.S K.R K.E K.D)) (.block (copyPt K.M.n K.R K.D))) s
      (SumPostW K C base size (VG.Proof.Weierstrass.rcbAdd3 (tmv C K.M.n base s K.S.b3)
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
  exact winCopy_ok hL hA hs
    (rcb3_ok hL.lay ⟨hA.sl, hA.mod⟩ hp (hL.rcbApart_D (Or.inr rfl)) hO hI (fun x hx => hx))

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
  hU.wordsVal (hL.ro_w hx) (by have := hL.lay.le x (winRo_slots K x hx); omega)

theorem _root_.VG.Proof.Weierstrass.WinLay.ro_tmv {K : WinCfg} {C : Curve} {size : Nat} (hL : WinLay K size) {base : Addr}
    {s s' : State} (hU : Unch base (winW K) s.mem s'.mem) (hn : base.toNat + size ≤ 2 ^ 64) {x : Nat}
    (hx : x ∈ winRo K) : tmv C K.M.n base s' x = tmv C K.M.n base s x := by
  show toM _ _ _ = toM _ _ _; rw [hL.ro_val hU hn hx]

/-- What the window method writes misses the modulus. -/
theorem winW_mo {K : WinCfg} {size : Nat} (hL : WinLay K size) {m : Nat} {mem : Mem} {base : Addr}
    (hM : ModOk K.M size m mem base) :
    ∀ w ∈ winW K, K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo := by
  intro w hw
  simp only [winW, List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · have := hL.lay.mo y (winWs_slots K y hy); dsimp only; omega
  · have := hM.sep; dsimp only; omega

/-- Entries `[1 … m]P` of the table. -/
def TblOk (K : WinCfg) (C : Curve) (base : Addr) (P : Point C) (m : Nat) (s : State) : Prop :=
  ∀ j, 1 ≤ j → j ≤ m →
    (∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z], wordsVal s.mem base x K.M.n < C.p) ∧
    Rep C (tmv C K.M.n base s (K.tblPt j).x) (tmv C K.M.n base s (K.tblPt j).y)
      (tmv C K.M.n base s (K.tblPt j).z) (mul j P)

/-- The table's invariant: entries `[1 … m]P` built. -/
structure BuildInv (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (m : Nat) (s : State) : Prop where
  scr : Scr s base size
  keep : KeepRegs (clob K.M.n) s₀ s
  unch : Unch base (winW K) s₀.mem s.mem
  mod : ModOk K.M size C.p s.mem base
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
theorem tbl_apart_add {K : WinCfg} {size : Nat} (hL : WinLay K size) {j m : Nat} (hj1 : 1 ≤ j)
    (hj8 : j ≤ 8) (hm1 : 1 ≤ m + 1) (hm8 : m + 1 ≤ 8) (hjm : j ≠ m + 1) :
    ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
      ∀ w ∈ (rcbW K.S (K.tblPt (m + 1))).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n)],
        x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro x hx w hw
  obtain ⟨i, hi, rfl, hi₁, hi₂⟩ := tblPt_mem K hj1 hj8 x hx
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with ⟨y, hy, rfl⟩ | rfl
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

/-- `[m + 1]P = [m]P + P`. -/
theorem addT_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) {s₀ : State} (hF : WinFixed K C base s₀ P k) {m : Nat} (h1 : 1 ≤ m)
    (h7 : m ≤ 7) {s : State} (hI : BuildInv K C base size P s₀ m s) :
    WP isa (fprogB K.M (rcb3 K.S (K.tblPt m) (K.tblPt 1) (K.tblPt (m + 1)))) s
      (BuildInv K C base size P s₀ (m + 1)) := by
  have hn := hI.scr.nowrap
  have tb : tmv C K.M.n base s K.S.b3 = Fin.ofNat C.p C.b := by
    rw [hL.ro_tmv hI.unch hn (by simp [winRo])]; exact hF.b
  have ro_lt : ∀ x ∈ winRo K, wordsVal s.mem base x K.M.n < C.p := fun x hx => by
    rw [hL.ro_val hI.unch hn hx]; exact hF.ro_lt x hx
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
  have W := rcb3_ok hL.lay ⟨hA.sl, hA.mod⟩ hp (hL.rcbApart_tbl h1 h7) hO hI' (fun x hx => hx)
  refine (fprogB_wp _ _).mpr (WP.mono W fun s₁ h₁ => ?_)
  obtain ⟨k₁, I₁, v₁⟩ := h₁
  have hW : ∀ w ∈ (rcbW K.S (K.tblPt (m + 1))).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n)],
      w ∈ winW K := by
    intro w hw
    simp only [winW, List.mem_append, List.mem_map, List.mem_singleton] at hw ⊢
    rcases hw with ⟨y, hy, rfl⟩ | rfl
    · refine Or.inl ⟨y, ?_, rfl⟩
      have ets : rcbW K.S (K.tblPt (m + 1)) = [K.S.t0, K.S.t1, K.S.t2, K.S.t3, K.S.t4, K.S.t5] ++
          [(K.tblPt (m + 1)).x, (K.tblPt (m + 1)).y, (K.tblPt (m + 1)).z] := rfl
      rw [ets, List.mem_append] at hy
      rcases hy with hy | hy
      · exact winOther_ws K y (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> win_mem)
      · exact (so y hy).2
    · exact Or.inr rfl
  have U₁ := k₁.unch
  have hox : (K.tblPt (m + 1)).x ∈ [(K.tblPt (m + 1)).x, (K.tblPt (m + 1)).y, (K.tblPt (m + 1)).z] ++
      rcbR K.S (K.tblPt m) (K.tblPt 1) := by simp
  have hoy : (K.tblPt (m + 1)).y ∈ [(K.tblPt (m + 1)).x, (K.tblPt (m + 1)).y, (K.tblPt (m + 1)).z] ++
      rcbR K.S (K.tblPt m) (K.tblPt 1) := by simp
  have hoz : (K.tblPt (m + 1)).z ∈ [(K.tblPt (m + 1)).x, (K.tblPt (m + 1)).y, (K.tblPt (m + 1)).z] ++
      rcbR K.S (K.tblPt m) (K.tblPt 1) := by simp
  refine ⟨k₁.scr hI.scr, hI.keep.trans ⟨k₁.gpr, k₁.rd, k₁.wr, k₁.sp⟩,
    (hI.unch.trans U₁).mono fun w hw => ?_, hI.mod.unch U₁ (fun w hw => winW_mo hL hI.mod w (hW w hw)) hn,
    fun j hj1 hjm => ?_⟩
  · rcases List.mem_append.mp hw with hw | hw
    · exact hw
    · exact hW w hw
  rcases Nat.lt_or_ge j (m + 1) with hj | hj
  · -- An entry built before keeps its numbers.
    have ap := tbl_apart_add hL (j := j) (m := m) hj1 (by omega) (by omega) (by omega) (by omega)
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
theorem adds_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) {s₀ : State} (hF : WinFixed K C base s₀ P k) :
    ∀ i ≤ 7, ∀ s, BuildInv K C base size P s₀ 1 s →
      WP isa (WinCfg.adds K i) s (BuildInv K C base size P s₀ (i + 1))
  | 0, _, _, h => WP.block_nil h
  | i + 1, hi, s, h => by
    rw [WinCfg.adds]
    exact WP.seq (WP.mono (adds_ok hL hA hp hC hM3 hP hF i (by omega) s h) fun s₁ h₁ =>
      addT_ok hL hA hp hC hM3 hP hF (m := i + 1) (by omega) (by omega) h₁)

/-- The table `[1 … 8]P`. -/
theorem build_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) {s : State} (hs : Scr s base size) (hM : ModOk K.M size C.p s.mem base)
    (hF : WinFixed K C base s P k) :
    WP isa (WinCfg.build K) s (BuildInv K C base size P s 8) := by
  have hn := hs.nowrap
  rw [WinCfg.build]
  refine WP.seq (WP.mono (?_ : WP isa (.block (copyPt K.M.n (K.tblPt 1) K.P)) s
    (BuildInv K C base size P s 1)) fun s' h => adds_ok hL hA hp hC hM3 hP hF 7 (by decide) s' h)
  have s1 := tblPt_slots K (m := 1) (Nat.le_refl _) (by omega)
  have le : ∀ x ∈ winSlots K, x + 8 * K.M.n ≤ size := fun x hx => hL.lay.le x hx
  have al : ∀ x ∈ winSlots K, x % 8 = 0 := fun x hx => hA.sl x hx
  have pT : ∀ x ∈ [K.P.x, K.P.y, K.P.z], ∀ y ∈ [(K.tblPt 1).x, (K.tblPt 1).y, (K.tblPt 1).z],
      y + 8 * K.M.n ≤ x ∨ x + 8 * K.M.n ≤ y := by
    intro x hx y hy
    obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K (m := 1) (Nat.le_refl _) (by omega) y hy
    have hxo : x ∈ winRo K ++ winOther K := List.mem_append_left _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [winRo])
    exact (hL.tbl_apart hxo hi).symm
  have tt : ∀ x ∈ [(K.tblPt 1).x, (K.tblPt 1).y, (K.tblPt 1).z],
      ∀ y ∈ [(K.tblPt 1).x, (K.tblPt 1).y, (K.tblPt 1).z], x ≠ y →
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := fun x hx y hy hxy =>
    hL.apart₂ (s1 x hx).2 (s1 y hy).2 hxy
  have ne₁ : (K.tblPt 1).x ≠ (K.tblPt 1).y := by rw [tblPt_x, tblPt_y]; exact hL.tbl_ne₂ (by omega)
  have ne₂ : (K.tblPt 1).x ≠ (K.tblPt 1).z := by rw [tblPt_x, tblPt_z]; exact hL.tbl_ne₂ (by omega)
  have ne₃ : (K.tblPt 1).y ≠ (K.tblPt 1).z := by rw [tblPt_y, tblPt_z]; exact hL.tbl_ne₂ (by omega)
  have xy := tt _ (by simp) _ (by simp) ne₁
  have xz := tt _ (by simp) _ (by simp) ne₂
  have yz := tt _ (by simp) _ (by simp) ne₃
  have mP : ∀ x ∈ [K.P.x, K.P.y, K.P.z], x ∈ winSlots K := fun x hx => winRo_slots K x (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [winRo])
  have b64 : ∀ x ∈ winSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := le x hx; omega_using [this, hn]
  rw [copyPt, List.append_assoc, WP.block_append_iff]
  have W1 := copy_ok K.M.n hs (le _ (s1 _ (by simp)).1) (le _ (mP _ (by simp)))
    (al _ (s1 _ (by simp)).1) (al _ (mP _ (by simp))) (o := (K.tblPt 1).x) (a := K.P.x)
    ((pT _ (by simp) _ (by simp)).imp (fun h => by omega_using [h]) id)
  refine WP.mono W1 fun s₁ h₁ => ?_
  obtain ⟨e₁, k₁, O₁⟩ := h₁
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  have W2 := copy_ok K.M.n hs₁ (le _ (s1 _ (by simp)).1) (le _ (mP _ (by simp)))
    (al _ (s1 _ (by simp)).1) (al _ (mP _ (by simp))) (o := (K.tblPt 1).y) (a := K.P.y)
    ((pT _ (by simp) _ (by simp)).imp (fun h => by omega_using [h]) id)
  refine WP.mono W2 fun s₂ h₂ => ?_
  obtain ⟨e₂, k₂, O₂⟩ := h₂
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have W3 := copy_ok K.M.n hs₂ (le _ (s1 _ (by simp)).1) (le _ (mP _ (by simp)))
    (al _ (s1 _ (by simp)).1) (al _ (mP _ (by simp))) (o := (K.tblPt 1).z) (a := K.P.z)
    ((pT _ (by simp) _ (by simp)).imp (fun h => by omega_using [h]) id)
  refine WP.mono W3 fun s₃ h₃ => ?_
  obtain ⟨e₃, k₃, O₃⟩ := h₃
  have bTx := b64 _ (s1 (K.tblPt 1).x (by simp)).1
  have bTy := b64 _ (s1 (K.tblPt 1).y (by simp)).1
  have bPy := b64 _ (mP K.P.y (by simp))
  have bPz := b64 _ (mP K.P.z (by simp))
  have pyx := pT K.P.y (by simp) (K.tblPt 1).x (by simp)
  have pzx := pT K.P.z (by simp) (K.tblPt 1).x (by simp)
  have pzy := pT K.P.z (by simp) (K.tblPt 1).y (by simp)
  have vx : wordsVal s₃.mem base (K.tblPt 1).x K.M.n = wordsVal s.mem base K.P.x K.M.n := by
    rw [O₃.wordsVal xz bTx, O₂.wordsVal xy bTx, e₁]
  have vy : wordsVal s₃.mem base (K.tblPt 1).y K.M.n = wordsVal s.mem base K.P.y K.M.n := by
    rw [O₃.wordsVal yz bTy, e₂, O₁.wordsVal (pyx.imp id id |>.symm) bPy]
  have vz : wordsVal s₃.mem base (K.tblPt 1).z K.M.n = wordsVal s.mem base K.P.z K.M.n := by
    rw [e₃, O₂.wordsVal (pzy.symm) bPz, O₁.wordsVal (pzx.symm) bPz]
  have U : Unch base (winW K) s.mem s₃.mem := by
    refine (O₁.unch.trans (O₂.unch.trans O₃.unch)).mono fun w hw => ?_
    simp only [List.mem_append, List.mem_singleton] at hw
    simp only [winW, List.mem_append, List.mem_map]
    refine Or.inl ⟨w.1, ?_, ?_⟩
    · rcases hw with rfl | rfl | rfl
      · exact (s1 _ (by simp)).2
      · exact (s1 _ (by simp)).2
      · exact (s1 _ (by simp)).2
    · rcases hw with rfl | rfl | rfl <;> rfl
  have c1 : ∀ r ∈ [Reg.x1], r ∈ clob K.M.n := by intro r hr; simp at hr; subst hr; simp [clob]
  refine ⟨hs₂.of_keepRegs k₃ (by decide), (k₁.mono c1).trans ((k₂.mono c1).trans (k₃.mono c1)), U,
    hM.unch U (winW_mo hL hM) hn, fun j hj1 hj => ?_⟩
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

/-! ## The entry of a digit -/

theorem tblSlot_eq (K : WinCfg) (c i : Nat) : tblSlot K c i = K.tbl + 8 * K.M.n * (3 * i + c) := by
  unfold tblSlot; grind

theorem tblSlot_pt (K : WinCfg) (a : Nat) :
    tblSlot K 0 (a - 1) = (K.tblPt a).x ∧ tblSlot K 1 (a - 1) = (K.tblPt a).y ∧
      tblSlot K 2 (a - 1) = (K.tblPt a).z := by
  simp only [tblSlot, WinCfg.tblPt]; omega

theorem winSelect_eq (K : WinCfg) : WinCfg.select K =
    (List.range K.M.n).flatMap (WinCfg.selectWord K 0 K.E.x) ++
    ((List.range K.M.n).flatMap (WinCfg.selectWord K 1 K.E.y) ++
    (List.range K.M.n).flatMap (WinCfg.selectWord K 2 K.E.z)) := by
  simp only [WinCfg.select, List.append_assoc]

/-- After the selection and the negation: `E` represents the point of digit
`i`, and only `E`, `-y` and the temporary area changed. -/
structure EntryPostW (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (k i : Nat)
    (s s' : State) : Prop where
  scr : Scr s' base size
  x19 : s'.gpr .x19 = s.gpr .x19
  keep : KeepRegs (combClob K.M.n) s s'
  unch : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n),
    (K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)] s.mem s'.mem
  lt : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s'.mem base x K.M.n < C.p
  rep : Rep C (tmv C K.M.n base s' K.E.x) (tmv C K.M.n base s' K.E.y) (tmv C K.M.n base s' K.E.z)
    (winPt C P k i)

theorem winE_mem {K : WinCfg} : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], x ∈ winOther K := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> win_mem

theorem mul_zero_pt' {C : Curve} (P : Point C) : mul 0 P = .infinity := by
  rw [Spec.Weierstrass.mul]; simp

/-- The digit's masks, its entry from the table, and its `y` negated for a
negative digit. -/
theorem winEntry_ok {K : WinCfg} {C : Curve} {base : Addr} {size k i : Nat} (hL : WinLay K size)
    (hA : WinA K) (hC : Law C) {P : Point C} (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s : State} (hs : Scr s base size)
    (hM : ModOk K.M size C.p s.mem base) (hi : i < K.J) (hx : s.gpr .x19 = BitVec.ofNat 64 i)
    (hbits : ∀ t < 4 * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0)
    (hz : wordsVal s.mem base K.zero K.M.n = 0) (hT : TblOk K C base P 8 s) :
    WP isa (.block (digit K.bits ++ WinCfg.select K ++ negY K.M K.neg K.zero K.E.y K.bits)) s
      (EntryPostW K C base size P k i s) := by
  have hn := hs.nowrap
  have hJ := hL.J
  have h0 := hL.n0
  have hmag := mag_le (nib_lt k i)
  have hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hone_lt
  obtain ⟨-, -, -, -, exy, exz, eyz, hEo, -, -⟩ := hL.other_ne
  have wE : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], x ∈ winWs K := fun x hx => winOther_ws K x (winE_mem x hx)
  have le : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], x + 8 * K.M.n ≤ size := fun x hx =>
    hL.lay.le x (winOther_mem (winE_mem x hx))
  have al : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], x % 8 = 0 := fun x hx =>
    hA.sl x (winOther_mem (winE_mem x hx))
  have xy := hL.apart₂ (wE K.E.x (by simp)) (wE K.E.y (by simp)) exy
  have xz := hL.apart₂ (wE K.E.x (by simp)) (wE K.E.z (by simp)) exz
  have yz := hL.apart₂ (wE K.E.y (by simp)) (wE K.E.z (by simp)) eyz
  have neN : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ≠ K.neg := fun x hx e => hEo x hx (by rw [e]; simp)
  have xneg := hL.apart₂ (wE K.E.x (by simp)) (wE K.neg (by simp)) (neN _ (by simp))
  have yneg := hL.apart₂ (wE K.E.y (by simp)) (wE K.neg (by simp)) (neN _ (by simp))
  have zneg := hL.apart₂ (wE K.E.z (by simp)) (wE K.neg (by simp)) (neN _ (by simp))
  -- The table's slots, apart from `E`.
  have hslot : ∀ c < 3, ∀ i' < 8, tblSlot K c i' + 8 * K.M.n ≤ size ∧ tblSlot K c i' % 8 = 0 := by
    intro c hc i' hi'
    rw [tblSlot_eq]
    have hm : K.tbl + 8 * K.M.n * (3 * i' + c) ∈ winSlots K := by
      simp only [winSlots, List.mem_append]; exact Or.inr (winTbl_mem K (by omega))
    exact ⟨hL.lay.le _ hm, hA.sl _ hm⟩
  have hsep : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], ∀ c < 3, ∀ i' < 8,
      tblSlot K c i' + 8 * K.M.n ≤ x ∨ x + 8 * K.M.n ≤ tblSlot K c i' := by
    intro x hx c hc i' hi'
    rw [tblSlot_eq]
    exact (hL.tbl_apart (List.mem_append_right _ (winE_mem x hx)) (i := 3 * i' + c) (by omega)).symm
  have sub3 : ∀ o ∈ [K.E.x, K.E.y, K.E.z], o ∈ [K.E.x, K.E.y, K.E.z, K.neg] := by
    intro o ho; simp only [List.mem_cons, List.not_mem_nil, or_false] at ho ⊢
    rcases ho with h | h | h <;> simp [h]
  have hd : ∀ c < 3, ∀ o ∈ [K.E.x, K.E.y, K.E.z], ∀ i' < 8, tblSlot K c i' + 8 * K.M.n ≤ size ∧
      tblSlot K c i' % 8 = 0 ∧ (tblSlot K c i' + 8 * K.M.n ≤ o ∨ o + 8 * K.M.n ≤ tblSlot K c i') :=
    fun c hc o ho i' hi' => ⟨(hslot c hc i' hi').1, (hslot c hc i' hi').2,
      hsep o (sub3 o ho) c hc i' hi'⟩
  -- The digit's masks.
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (digit_ok hs K.bits (k := k) (j := i) (N := 4 * K.J) (by omega) hL.bits hL.bits4 hx
    hbits) fun s₁ ⟨m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : MasksOf s₁ (mag (nib k i)) := m₁
  -- The entry.
  rw [winSelect_eq, List.append_assoc, WP.block_append_iff]
  have W2 := selectCoord_ok hs₁ K hmag hm₁ (c := 0) (o := K.E.x) (al _ (by simp)) (le _ (by simp))
    (hd 0 (by decide) K.E.x (by simp)) (Nat.lt_trans hone_lt hpn)
  refine WP.mono W2 fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [List.append_assoc, WP.block_append_iff]
  have W3 := selectCoord_ok hs₂ K hmag (hm₁.keepRegs k₂) (c := 1) (o := K.E.y) (al _ (by simp))
    (le _ (by simp)) (hd 1 (by decide) K.E.y (by simp)) (Nat.lt_trans hone_lt hpn)
  refine WP.mono W3 fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [WP.block_append_iff]
  have W4 := selectCoord_ok hs₃ K hmag ((hm₁.keepRegs k₂).keepRegs k₃) (c := 2) (o := K.E.z)
    (al _ (by simp)) (le _ (by simp)) (hd 2 (by decide) K.E.z (by simp)) (Nat.lt_trans hone_lt hpn)
  refine WP.mono W4 fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  -- The table's numbers, unchanged by the selection.
  have tb : ∀ c < 3, ∀ i' < 8, ∀ {m m' : Mem} {o : Nat}, o ∈ [K.E.x, K.E.y, K.E.z] →
      Outside base o (8 * K.M.n) m m' →
      wordsVal m' base (tblSlot K c i') K.M.n = wordsVal m base (tblSlot K c i') K.M.n :=
    fun c hc i' hi' m m' o ho O => O.wordsVal (hsep o (sub3 o ho) c hc i' hi')
      (by have := (hslot c hc i' hi').1; omega)
  have m₁ : s₁.mem = s.mem := k₁.mem
  -- What `E` holds, from the table at `s`.
  have vx : wordsVal s₄.mem base K.E.x K.M.n = (if mag (nib k i) = 0 then 0 else
      wordsVal s.mem base (tblSlot K 0 (mag (nib k i) - 1)) K.M.n) := by
    rw [O₄.wordsVal xz (by have := le K.E.x (by simp); omega),
      O₃.wordsVal xy (by have := le K.E.x (by simp); omega), e₂, m₁]
    rfl
  have vy : wordsVal s₄.mem base K.E.y K.M.n = (if mag (nib k i) = 0 then K.one else
      wordsVal s.mem base (tblSlot K 1 (mag (nib k i) - 1)) K.M.n) := by
    rw [O₄.wordsVal yz (by have := le K.E.y (by simp); omega), e₃]
    split
    · rfl
    · rw [tb 1 (by decide) _ (by omega) (o := K.E.x) (by simp) O₂, m₁]
  have vz : wordsVal s₄.mem base K.E.z K.M.n = (if mag (nib k i) = 0 then 0 else
      wordsVal s.mem base (tblSlot K 2 (mag (nib k i) - 1)) K.M.n) := by
    rw [e₄]
    split
    · rfl
    · rw [tb 2 (by decide) _ (by omega) (o := K.E.y) (by simp) O₃,
        tb 2 (by decide) _ (by omega) (o := K.E.x) (by simp) O₂, m₁]
  have U₄ : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] s.mem s₄.mem := by
    rw [← m₁]; exact (O₂.unch.trans (O₃.unch.trans O₄.unch)).mono (by simp)
  have hEW : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n), (K.neg, 8 * K.M.n),
      (K.M.tmp, 8 * K.M.n)], w ∈ winW K := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [winW, List.mem_append, List.mem_map, List.mem_singleton]
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨_, wE _ (by simp), rfl⟩
    · exact Or.inl ⟨_, wE _ (by simp), rfl⟩
    · exact Or.inl ⟨_, wE _ (by simp), rfl⟩
    · exact Or.inl ⟨_, wE _ (by simp), rfl⟩
    · exact Or.inr rfl
  have U₄' : Unch base (winW K) s.mem s₄.mem := U₄.mono fun w hw => hEW w (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢; rcases hw with h | h | h <;> simp [h])
  have hM₄ : ModOk K.M size C.p s₄.mem base := hM.unch U₄' (winW_mo hL hM) hn
  have hz₄ : wordsVal s₄.mem base K.zero K.M.n = 0 := by
    rw [hL.ro_val U₄' hn (by simp [winRo]), hz]
  -- The entry's numbers, below `p`.
  have Ta := fun (h : mag (nib k i) ≠ 0) => hT (mag (nib k i)) (by omega) hmag
  have hpt := tblSlot_pt K (mag (nib k i))
  have hEy₄ : wordsVal s₄.mem base K.E.y K.M.n < C.p := by
    rw [vy]; split
    · exact hone_lt
    · rename_i h; rw [hpt.2.1]; exact (Ta h).1 _ (by simp)
  -- The negation.
  rw [negY, List.append_assoc, WP.block_append_iff]
  have hneg := le K.neg (by simp)
  have hzl := hL.lay.le K.zero (winRo_slots K _ (by simp [winRo]))
  have W5 := sub_ok hs₄ hM₄ hA.mod (o := K.neg) (a := K.zero) (b := K.E.y) hneg hzl
    (le _ (by simp)) (al _ (by simp)) (hA.sl _ (winRo_slots K _ (by simp [winRo]))) (al _ (by simp))
    (by rw [hz₄]; exact hp0) hEy₄
  refine WP.mono W5 fun s₅ h₅ => ?_
  obtain ⟨k₅, e₅⟩ := h₅
  have hs₅ : Scr s₅ base size := ⟨(k₅.gpr _ (x0_not_clob _)).trans hs₄.x0, k₅.wr ▸ hs₄.wr,
    hs₄.nowrap, hs₄.enc⟩
  have U₅ := k₅.unch
  have U₄₅ : Unch base (winW K) s.mem s₅.mem := (U₄'.trans U₅).mono fun w hw => by
    rcases List.mem_append.mp hw with hw | hw
    · exact hw
    · exact hEW w (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢; grind)
  have hx₅ : s₅.gpr .x19 = BitVec.ofNat 64 i := by
    rw [k₅.gpr _ (x19_not_clob _), k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide),
      k₁.gpr _ (by decide), hx]
  have hbits₅ : ∀ t < 4 * K.J, s₅.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by
      have := hL.bits
      rw [U₄₅.byte (fun w hw => by have := hL.bits_w w hw; omega) (by omega)]; exact hbits t ht
  rw [WP.block_append_iff]
  have W6 := signMask_ok hs₅ K.bits (k := k) (j := i) (N := 4 * K.J) (by omega) hL.bits hL.bits4 hx₅
    hbits₅
  refine WP.mono W6 fun s₆ h₆ => ?_
  obtain ⟨x₆, k₆⟩ := h₆
  have hs₆ := hs₅.of_keeps k₆ (by decide)
  have W7 := sel_ok (decide (nib k i < 8)) K.M.n hs₆ (by rw [x₆]; rfl) (o := K.E.y) (a := K.E.y)
    (b := K.neg) (le _ (by simp)) (le _ (by simp)) hneg (al _ (by simp)) (al _ (by simp))
    (al _ (by simp)) (Or.inl (Nat.le_refl _)) (by omega)
  refine WP.mono W7 fun s₇ h₇ => ?_
  obtain ⟨e₇, k₇, O₇⟩ := h₇
  have m₆ : s₆.mem = s₅.mem := k₆.mem
  have pt : ∀ x ∈ [(K.E.x, 8 * K.M.n), (K.E.z, 8 * K.M.n)], ∀ w ∈ [(K.neg, 8 * K.M.n),
      (K.M.tmp, 8 * K.M.n)], x.1 + x.2 ≤ w.1 ∨ w.1 + w.2 ≤ x.1 := by
    intro x hx w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hw
    rcases hx with rfl | rfl <;> rcases hw with rfl | rfl <;> dsimp only
    · exact xneg
    · exact hL.lay.tmp _ (winOther_mem (winE_mem _ (by simp)))
    · exact zneg
    · exact hL.lay.tmp _ (winOther_mem (winE_mem _ (by simp)))
  have lx := le K.E.x (by simp)
  have lz := le K.E.z (by simp)
  have ly := le K.E.y (by simp)
  have vx₇ : wordsVal s₇.mem base K.E.x K.M.n = wordsVal s₄.mem base K.E.x K.M.n := by
    rw [O₇.wordsVal (by omega) (by omega), m₆,
      U₅.wordsVal (pt (K.E.x, 8 * K.M.n) (by simp)) (by omega)]
  have vz₇ : wordsVal s₇.mem base K.E.z K.M.n = wordsVal s₄.mem base K.E.z K.M.n := by
    rw [O₇.wordsVal (by omega) (by omega), m₆,
      U₅.wordsVal (pt (K.E.z, 8 * K.M.n) (by simp)) (by omega)]
  have vy₅ : wordsVal s₅.mem base K.E.y K.M.n = wordsVal s₄.mem base K.E.y K.M.n :=
    U₅.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> dsimp only
      · exact yneg
      · exact hL.lay.tmp _ (winOther_mem (winE_mem _ (by simp)))) (by omega)
  have vy₇ : wordsVal s₇.mem base K.E.y K.M.n = if decide (nib k i < 8) then
      (0 + C.p - wordsVal s₄.mem base K.E.y K.M.n) % C.p else wordsVal s₄.mem base K.E.y K.M.n := by
    rw [e₇, m₆, e₅, hz₄, vy₅]
  refine ⟨hs₆.of_keepRegs k₇ (by decide), ?_, ?_, ?_, ?_, ?_⟩
  · rw [k₇.gpr _ (by decide), k₆.gpr _ (by decide), k₅.gpr _ (x19_not_clob _), k₄.gpr _ (by decide),
      k₃.gpr _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
  · have c1 : ∀ r ∈ clob K.M.n, r ∈ combClob K.M.n := fun r hr =>
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hr))
    refine (((((((Keeps.regs k₁).mono ?_).trans ((k₂.trans (k₃.trans k₄)).mono ?_)).trans
      ((⟨k₅.gpr, k₅.rd, k₅.wr, k₅.sp⟩ : KeepRegs (clob K.M.n) s₄ s₅).mono c1)).trans
      ((Keeps.regs k₆).mono ?_)).trans (k₇.mono ?_)))
    · intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | rfl | rfl | rfl | hr
      · exact combClob_mem (by simp)
      · exact combClob_mem (by simp)
      · simp [combClob]
      · exact combClob_mem (by simp)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hr))
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [combClob, clob]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [combClob, clob]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [combClob, clob]
  · refine ((U₄.trans (U₅.trans (m₆ ▸ O₇.unch))).mono ?_)
    intro w hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    grind
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [vx₇, vx]; split
      · exact hp0
      · rename_i h; rw [hpt.1]; exact (Ta h).1 _ (by simp)
    · rw [vy₇]; split
      · exact Nat.mod_lt _ hp0
      · exact hEy₄
    · rw [vz₇, vz]; split
      · exact hp0
      · rename_i h; rw [hpt.2.2]; exact (Ta h).1 _ (by simp)
  · -- The point: `[|d|]P` (`O` for `0`), reflected for a negative digit.
    have hR : Rep C (toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₄.mem base K.E.x K.M.n))
        (toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₄.mem base K.E.y K.M.n))
        (toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₄.mem base K.E.z K.M.n)) (mul (mag (nib k i)) P) := by
      rw [vx, vy, vz]
      by_cases h : mag (nib k i) = 0
      · simp only [h, ↓reduceIte, toM_zero, hone, mul_zero_pt']
        exact rep_infinity' hC
      · simp only [h, ↓reduceIte]
        rw [hpt.1, hpt.2.1, hpt.2.2]
        exact (Ta h).2
    have ex : tmv C K.M.n base s₇ K.E.x = toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₄.mem base K.E.x K.M.n) := by
      show toM _ _ _ = _; rw [vx₇]
    have ez : tmv C K.M.n base s₇ K.E.z = toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₄.mem base K.E.z K.M.n) := by
      show toM _ _ _ = _; rw [vz₇]
    rw [ex, ez]
    unfold winPt
    by_cases h8 : 8 ≤ nib k i
    · have hy : tmv C K.M.n base s₇ K.E.y = toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₄.mem base K.E.y K.M.n) := by
        show toM _ _ _ = _
        rw [vy₇, decide_eq_false (show ¬ nib k i < 8 by omega)]; rfl
      rw [hy]
      simp only [h8, ↓reduceIte]
      have : mag (nib k i) = nib k i - 8 := by simp [mag, h8]
      rw [this] at hR
      exact hR
    · have hy : tmv C K.M.n base s₇ K.E.y = -toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₄.mem base K.E.y K.M.n) := by
        show toM _ _ _ = _
        rw [vy₇, decide_eq_true (show nib k i < 8 by omega)]
        simp only [↓reduceIte]
        rw [toM_sub (by omega), toM_zero]
        grind
      rw [hy]
      simp only [h8, ↓reduceIte]
      have : mag (nib k i) = 8 - nib k i := by simp [mag, h8]
      rw [this] at hR
      exact Rep.negY hR

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
    refine hU.wordsVal (fun w hw => ?_) (by have := hL.lay.le _ hs; omega)
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
  mod : ModOk K.M size C.p s.mem base
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

/-- `R = R + E`, for `R` representing `PR` and `E` `PQ`. -/
theorem sumStep_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    {s₀ s : State} (hF : WinFixed K C base s₀ P k) (hS : WinSt K C base size P s₀ s)
    {PR PQ : Point C} (hPR : onCurve C PR = true) (hPQ : onCurve C PQ = true)
    (hltR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hltq : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : Rep C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z) PR)
    (hQ : Rep C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z) PQ) :
    WP isa (.seq (fprogB K.M (rcb3 K.S K.R K.E K.D)) (.block (copyPt K.M.n K.R K.D))) s fun s' =>
      WinSt K C base size P s₀ s' ∧ s'.gpr .x19 = s.gpr .x19 ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (Spec.Weierstrass.add PR PQ) := by
  obtain ⟨-, tb, ro_lt, -⟩ := hS.ro_tmv hL hF
  have hlt : ∀ x ∈ rcbR K.S K.R K.E, wordsVal s.mem base x K.M.n < C.p := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ro_lt _ (by simp [winRo])
    · exact ro_lt _ (by simp [winRo])
    · exact hltR _ (by simp)
    · exact hltR _ (by simp)
    · exact hltR _ (by simp)
    · exact hltq _ (by simp)
    · exact hltq _ (by simp)
    · exact hltq _ (by simp)
  refine WP.mono (winAdd_ok hL hA hp hS.scr hS.mod hlt) fun s' S => ?_
  have hV := S.val
  rw [tb] at hV
  exact ⟨hS.next hL S.scr (S.keep.mono clob_combClob) S.unch, S.keep.gpr _ (x19_not_clob _), S.lt,
    hC.add3 hM3 hPR hPQ hR hQ hV.symm⟩

/-- The loop's invariant at `x19 = j`: `R` represents `[winE k J j]P`. -/
structure WinInv (K : WinCfg) (C : Curve) (base : Addr) (size k : Nat) (P : Point C) (s₀ s : State)
    (j : Nat) : Prop where
  st : WinSt K C base size P s₀ s
  x19 : s.gpr .x19 = BitVec.ofNat 64 j
  lt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p
  rep : Rep C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
    (mul (winE k K.J j) P)

/-! ## Four doublings in Jacobian coordinates -/

/-- A field program on numbered slots, writing slots of `winOther`: the loop's frame. -/
theorem winN_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {N : List FOp} (hN : NumOk N) {p q o : Pt}
    (hAp : RcbApart K.S p q o) (hSl : ∀ x ∈ rcbW K.S o ++ rcbR K.S p q, x ∈ winSlots K)
    (hW : ∀ x ∈ rcbW K.S o, x ∈ winOther K) {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (· ∈ winSlots K) V E s) (hV : ∀ x ∈ rcbR K.S p q, x ∈ V) :
    WP isa (fprogB K.M (ofN N K.S p q o)) s fun s' => KeepRegs (clob K.M.n) s s' ∧
      Unch base (loopW K) s.mem s'.mem ∧ ∃ E' : Nat → Fe C,
      Inv K.M base size C.p (· ∈ winSlots K) ([o.x, o.y, o.z] ++ V) E' s' ∧
      (∀ x, x ∉ rcbW K.S o → E' x = E x) ∧
      (E' o.x, E' o.y, E' o.z) = (runOps N (fun y => E (rcbσ K.S p q o y)) 6,
        runOps N (fun y => E (rcbσ K.S p q o y)) 7, runOps N (fun y => E (rcbσ K.S p q o y)) 8) := by
  refine (fprogB_wp _ _).mpr (WP.mono (ofN_ok hL.lay ⟨hA.sl, hA.mod⟩ hp hN hAp hSl hI hV)
    fun s' ⟨k, I, v⟩ => ⟨⟨k.gpr, k.rd, k.wr, k.sp⟩, k.unch.mono fun w hw => ?_, _, I,
      fun x hx => runOps_of_not_out _ _ fun op hop h => hx (h ▸ ofN_out hN op hop), v⟩)
  simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw ⊢
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · exact Or.inl ⟨y, hW y hy, rfl⟩
  · exact Or.inr rfl

/-- The slots of a numbered program from `p` and `q` into `o`, a point written. -/
theorem winJ_sl {K : WinCfg} {o p q : Pt} (ho : ∀ x ∈ [o.x, o.y, o.z], x ∈ winOther K)
    (hp : ∀ x ∈ [p.x, p.y, p.z], x ∈ winSlots K) (hq : ∀ x ∈ [q.x, q.y, q.z], x ∈ winSlots K) :
    (∀ x ∈ rcbW K.S o ++ rcbR K.S p q, x ∈ winSlots K) ∧ ∀ x ∈ rcbW K.S o, x ∈ winOther K := by
  have hW : ∀ x ∈ rcbW K.S o, x ∈ winOther K := by
    intro x hx
    simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h | h | h | h <;> subst h
    · win_mem
    · win_mem
    · win_mem
    · win_mem
    · win_mem
    · win_mem
    · exact ho _ (by simp)
    · exact ho _ (by simp)
    · exact ho _ (by simp)
  refine ⟨fun x hx => ?_, hW⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact winOther_mem (hW x hx)
  · simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h | h | h <;> subst h
    · win_mem
    · win_mem
    · exact hp _ (by simp)
    · exact hp _ (by simp)
    · exact hp _ (by simp)
    · exact hq _ (by simp)
    · exact hq _ (by simp)
    · exact hq _ (by simp)

/-- What a program reads is in `V`. -/
local macro "rcb_sub" : tactic => `(tactic| (
  intro x hx
  simp only [rcbR, WinCfg.zeroPt, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hx ⊢
  rcases hx with h | h | h | h | h | h | h | h <;> simp only [h, true_or, or_true]))

/-- `R = 16 R` in Jacobian coordinates, but `Y`: the triple `(X : Y : Z)` stands for
`[16 e]P` (or `Z = 0`), `R` is `(XZ : Y : Z³)` and `E.z` is `Z`. -/
theorem jac_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) {s₀ s : State} (hF : WinFixed K C base s₀ P k)
    (hS : WinSt K C base size P s₀ s) {e : Nat}
    (hlt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : Rep C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
      (mul e P)) :
    WP isa (WinCfg.jac K) s fun s' =>
      WinSt K C base size P s₀ s' ∧ s'.gpr .x19 = s.gpr .x19 ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      ∃ X Y Z : Fe C, InvJ C X Y Z (mul (16 * e) P) ∧ tmv C K.M.n base s' K.R.x = X * Z ∧
        tmv C K.M.n base s' K.R.y = Y ∧ tmv C K.M.n base s' K.R.z = Z * Z * Z ∧
        tmv C K.M.n base s' K.E.z = Z := by
  obtain ⟨-, -, ro_lt, hz⟩ := hS.ro_tmv hL hF
  obtain ⟨a1, a2, a3, a4⟩ := hL.rcbApart_jac
  have oR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ winOther K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> win_mem
  have oE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∈ winOther K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> win_mem
  have oD : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ winOther K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> win_mem
  have sZ : ∀ x ∈ [(WinCfg.zeroPt K).x, (WinCfg.zeroPt K).y, (WinCfg.zeroPt K).z], x ∈ winSlots K := by
    intro x hx
    simp only [WinCfg.zeroPt, List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
    subst hx; win_mem
  have sl := fun (P : Pt) (h : ∀ x ∈ [P.x, P.y, P.z], x ∈ winOther K) x (hx : x ∈ [P.x, P.y, P.z]) =>
    winOther_mem (h x hx)
  have w1 := winJ_sl oE (sl _ oR) sZ
  have w2 := winJ_sl oD (sl _ oE) (sl _ oE)
  have w3 := winJ_sl oE (sl _ oD) (sl _ oD)
  have w4 := winJ_sl oR (sl _ oE) sZ
  have V0 : ∀ x ∈ [K.S.a, K.S.b3, K.zero, K.R.x, K.R.y, K.R.z],
      x ∈ winSlots K ∧ wordsVal s.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | h | h | h
    · exact ⟨by win_mem, ro_lt _ (by simp [winRo])⟩
    · exact ⟨by win_mem, ro_lt _ (by simp [winRo])⟩
    · exact ⟨by win_mem, ro_lt _ (by simp [winRo])⟩
    all_goals exact ⟨winOther_mem (oR _ (by simp [h])), hlt _ (by simp [h])⟩
  have I₀ : Inv K.M base size C.p (· ∈ winSlots K) [K.S.a, K.S.b3, K.zero, K.R.x, K.R.y, K.R.z]
      (tmv C K.M.n base s) s :=
    ⟨hS.scr, hS.mod, fun x hx => (V0 x hx).1, fun x hx => (V0 x hx).2, fun _ _ => rfl⟩
  have hQ := fun (a : Nat) => hC.onCurve_mul hP a
  simp only [WinCfg.jac, toJ_eq, dblJ_eq, fromJ_eq]
  -- Into Jacobian coordinates, in `E`.
  refine WP.seq (WP.mono (winN_ok hL hA hp toJN_ok a1 w1.1 w1.2 I₀ (by rcb_sub))
    fun s₁ ⟨k₁, U₁, E₁, I₁, _, v₁⟩ => ?_)
  have S₁ := hS.next hL I₁.scr (k₁.mono clob_combClob) U₁
  have J₁ : InvJ C (E₁ K.E.x) (E₁ K.E.y) (E₁ K.E.z) (mul e P) :=
    InvJ.of_toJ (z := tmv C K.M.n base s K.zero) hC hR (show toM _ _ _ = 0 by rw [hz]; exact toM_zero _ _)
      (v₁.trans (toJN_run _))
  -- Four doublings.
  refine WP.seq (WP.mono (winN_ok hL hA hp dblJN_ok a2 w2.1 w2.2 I₁ (by rcb_sub))
    fun s₂ ⟨k₂, U₂, E₂, I₂, _, v₂⟩ => ?_)
  have S₂ := S₁.next hL I₂.scr (k₂.mono clob_combClob) U₂
  have J₂ := InvJ.dbl' hC hM3 (hQ e) J₁ (v₂.trans (dblJN_run _))
  rw [hC.double hP] at J₂
  refine WP.seq (WP.mono (winN_ok hL hA hp dblJN_ok a3 w3.1 w3.2 I₂ (by rcb_sub))
    fun s₃ ⟨k₃, U₃, E₃, I₃, _, v₃⟩ => ?_)
  have S₃ := S₂.next hL I₃.scr (k₃.mono clob_combClob) U₃
  have J₃ := InvJ.dbl' hC hM3 (hQ _) J₂ (v₃.trans (dblJN_run _))
  rw [hC.double hP] at J₃
  refine WP.seq (WP.mono (winN_ok hL hA hp dblJN_ok a2 w2.1 w2.2 I₃ (by rcb_sub))
    fun s₄ ⟨k₄, U₄, E₄, I₄, _, v₄⟩ => ?_)
  have S₄ := S₃.next hL I₄.scr (k₄.mono clob_combClob) U₄
  have J₄ := InvJ.dbl' hC hM3 (hQ _) J₃ (v₄.trans (dblJN_run _))
  rw [hC.double hP] at J₄
  refine WP.seq (WP.mono (winN_ok hL hA hp dblJN_ok a3 w3.1 w3.2 I₄ (by rcb_sub))
    fun s₅ ⟨k₅, U₅, E₅, I₅, _, v₅⟩ => ?_)
  have S₅ := S₄.next hL I₅.scr (k₅.mono clob_combClob) U₅
  have J₅ := InvJ.dbl' hC hM3 (hQ _) J₄ (v₅.trans (dblJN_run _))
  rw [hC.double hP, show 2 * (2 * (2 * (2 * e))) = 16 * e by omega] at J₅
  -- Back to projective coordinates, in `R`.
  refine WP.mono (winN_ok hL hA hp fromJN_ok a4 w4.1 w4.2 I₅ (by rcb_sub))
    fun s₆ ⟨k₆, U₆, E₆, I₆, o₆, v₆⟩ => ?_
  have S₆ := S₅.next hL I₆.scr (k₆.mono clob_combClob) U₆
  obtain ⟨-, -, -, hz₅⟩ := S₅.ro_tmv hL hF
  have z₅ : E₅ K.zero = 0 := by
    rw [← I₅.val _ (by simp), hz₅]; exact toM_zero _ _
  have r₆ : (E₆ K.R.x, E₆ K.R.y, E₆ K.R.z) = (E₅ K.E.x * E₅ K.E.z, E₅ K.E.y + E₅ K.zero,
      E₅ K.E.z * E₅ K.E.z * E₅ K.E.z) := v₆.trans (fromJN_run _)
  simp only [z₅, Prod.mk.injEq] at r₆
  have ez : E₆ K.E.z = E₅ K.E.z := o₆ _ (a4.apart _ (by simp [rcbR]))
  refine ⟨S₆, by
      rw [k₆.gpr _ (x19_not_clob _), k₅.gpr _ (x19_not_clob _), k₄.gpr _ (x19_not_clob _),
        k₃.gpr _ (x19_not_clob _), k₂.gpr _ (x19_not_clob _), k₁.gpr _ (x19_not_clob _)],
    fun x hx => I₆.lt x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with
      h | h | h | h <;> simp [h]),
    E₅ K.E.x, E₅ K.E.y, E₅ K.E.z, J₅, ?_, ?_, ?_, ?_⟩
  · exact (I₆.val _ (by simp)).trans r₆.1
  · exact (I₆.val _ (by simp)).trans (r₆.2.1.trans (by grind))
  · exact (I₆.val _ (by simp)).trans r₆.2.2
  · exact (I₆.val _ (by simp)).trans ez

/-! ## `Y = 1` where `Z = 0` -/

theorem sel_mask (c v : BitVec 64) (p : Prop) [Decidable p] :
    c &&& mask p ||| v &&& ~~~(mask p) = if p then c else v := by
  by_cases h : p <;> simp [mask, h, -BitVec.reduceAllOnes]

/-- Word `w` of `R.y`: Montgomery's one where `x2` is the mask of `p`. -/
theorem ySelWord_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (K : WinCfg)
    (p : Prop) [Decidable p] (hx2 : s.gpr .x2 = mask p) {w : Nat} (ho : K.R.y + 8 * w + 8 ≤ size)
    (ho8 : K.R.y % 8 = 0) :
    WP isa (.block (WinCfg.ySelWord K w)) s fun t =>
      t.mem = s.mem.writeW (off base (K.R.y + 8 * w))
        (if p then wordOf K.one w else word s.mem base (K.R.y + 8 * w)) ∧
      KeepRegs [.x4, .x9] s t := by
  rw [show WinCfg.ySelWord K w = ([ld .x9 (K.R.y + 8 * w)] : List Instr) ++
      (([.bicRor .x .x9 .x9 .x2 0] : List Instr) ++ (const64 .x4 (wordOf K.one w) ++
        (([.logic .and .x .x4 .x4 .x2, .logic .orr .x .x4 .x4 .x9] : List Instr) ++
          ([st .x4 (K.R.y + 8 * w)] : List Instr)))) by
      simp only [WinCfg.ySelWord, List.cons_append, List.nil_append],
    WP.block_append_iff]
  refine WP.mono (ld_ok hs (d := K.R.y + 8 * w) ho (by omega) .x9) fun s₁ ⟨e₁, k₁, _⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have m₁ : s₁.gpr .x2 = mask p := (k₁.gpr _ (by decide)).trans hx2
  rw [WP.block_append_iff]
  have hb : WP isa (.block [.bicRor .x .x9 .x9 .x2 0]) s₁ fun t =>
      t.gpr .x9 = word s.mem base (K.R.y + 8 * w) &&& ~~~(mask p) ∧ Keeps [.x9] s₁ t := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Size.bits,
      show (0 : Nat) < 64 from by decide, ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq,
      rotateRight_zero', e₁, m₁, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    exact RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr)
  refine WP.mono hb fun s₂ ⟨x₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok s₂ .x4 _) fun s₃ ⟨x₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have m₃ : s₃.gpr .x2 = mask p := by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), m₁]
  have n₃ : s₃.gpr .x9 = word s.mem base (K.R.y + 8 * w) &&& ~~~(mask p) := by
    rw [k₃.gpr _ (by decide), x₂]
  rw [WP.block_append_iff]
  have hc : WP isa (.block [.logic .and .x .x4 .x4 .x2, .logic .orr .x .x4 .x4 .x9]) s₃ fun t =>
      t.gpr .x4 = (if p then wordOf K.one w else word s.mem base (K.R.y + 8 * w)) ∧
        Keeps [.x4] s₃ t := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
      BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, x₃, m₃, n₃, sel_mask,
      Option.some.injEq, exists_eq_left']
    refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]
  refine WP.mono hc fun s₄ ⟨x₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.mono (st_out hs₄ (o := K.R.y + 8 * w) ho (by omega) .x4) fun t ⟨m, kt, _⟩ => ⟨?_, ?_⟩
  · rw [m, x₄, k₄.mem, k₃.mem, k₂.mem, k₁.mem]
  · exact ((((Keeps.regs k₁).mono (by decide)).trans ((Keeps.regs k₂).mono (by decide))).trans
      (((Keeps.regs k₃).mono (by decide)).trans ((Keeps.regs k₄).mono (by decide)))).trans
      (kt.mono (by decide))

/-- The first `k` words of `R.y`. -/
theorem ySelWords_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (K : WinCfg)
    (p : Prop) [Decidable p] (hx2 : s.gpr .x2 = mask p) (ho8 : K.R.y % 8 = 0) :
    ∀ k, K.R.y + 8 * k ≤ size →
    WP isa (.block ((List.range k).flatMap (WinCfg.ySelWord K))) s fun t =>
      (∀ w < k, word t.mem base (K.R.y + 8 * w) =
        if p then wordOf K.one w else word s.mem base (K.R.y + 8 * w)) ∧
      KeepRegs [.x4, .x9] s t ∧ Outside base K.R.y (8 * k) s.mem t.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ySelWords_ok hs K p hx2 ho8 k (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    refine WP.mono (ySelWord_ok hs₁ K p ((k₁.gpr _ (by decide)).trans hx2) (w := k) (by omega) ho8)
      fun s₂ ⟨m₂, k₂⟩ => ?_
    have O₂ : Outside base (K.R.y + 8 * k) 8 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, k₁.trans k₂,
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.word (by omega) (by omega), e₁ j h]
    · obtain rfl : j = k := by omega
      rw [m₂, word_writeW_self, O₁.word (by omega) (by omega)]

/-- `R.y` = Montgomery's one where `E.z` is zero. -/
theorem ySel_ok {K : WinCfg} {base : Addr} {size : Nat} (hL : WinLay K size) (hA : WinA K)
    {s : State} (hs : Scr s base size) (h1 : K.one < 2 ^ (64 * K.M.n)) :
    WP isa (.block (WinCfg.ySel K)) s fun t =>
      wordsVal t.mem base K.R.y K.M.n = (if wordsVal s.mem base K.E.z K.M.n = 0 then K.one
        else wordsVal s.mem base K.R.y K.M.n) ∧
      KeepRegs [.x1, .x2, .x4, .x5, .x7, .x9, .x16] s t ∧
      Unch base [(K.R.y, 8 * K.M.n)] s.mem t.mem := by
  have hn := hs.nowrap
  have hy : K.R.y ∈ winSlots K := by win_mem
  have hz : K.E.z ∈ winSlots K := by win_mem
  rw [WinCfg.ySel, WP.block_append_iff]
  refine WP.mono (zeroMask_ok hs hL.n0 (hL.lay.le _ hz) (hA.sl _ hz)) fun s₁ ⟨m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.mono (ySelWords_ok hs₁ K _ m₁ (hA.sl _ hy) K.M.n (hL.lay.le _ hy))
    fun t ⟨e, kt, O⟩ => ⟨?_, ?_, ?_⟩
  · by_cases hz0 : wordsVal s.mem base K.E.z K.M.n = 0
    · simp only [hz0, ↓reduceIte]
      exact wordsVal_of_shifts _ _ _ _ _ h1 fun j hj => by simp only [e j hj, hz0, ↓reduceIte]; rfl
    · simp only [hz0, ↓reduceIte]
      rw [← k₁.mem]
      exact wordsVal_of_words _ _ _ _ _ _ fun j hj => by simp only [e j hj, hz0, ↓reduceIte]
  · exact ((Keeps.regs k₁).mono (by decide)).trans (kt.mono (by decide))
  · rw [← k₁.mem]; exact O.unch.mono (by simp)

/-- `R = 16 R`: `[e]P` to `[16 e]P`. -/
theorem quad_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s₀ s : State} (hF : WinFixed K C base s₀ P k)
    (hS : WinSt K C base size P s₀ s) {e : Nat}
    (hlt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : Rep C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
      (mul e P)) :
    WP isa (WinCfg.quad K) s fun s' =>
      WinSt K C base size P s₀ s' ∧ s'.gpr .x19 = s.gpr .x19 ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (mul (16 * e) P) := by
  rw [WinCfg.quad]
  refine WP.seq (WP.mono (jac_ok hL hA hp hC hM3 hP hF hS hlt hR)
    fun s₁ ⟨S₁, x₁, l₁, X, Y, Z, hJ, ex, ey, ez, eE⟩ => ?_)
  have hn := S₁.scr.nowrap
  refine WP.mono (ySel_ok hL hA S₁.scr (Nat.lt_trans hone_lt hpn)) fun s₂ ⟨v₂, k₂, U₂⟩ => ?_
  have hRy : K.R.y ∈ winOther K := by win_mem
  have c₂ : ∀ r ∈ [Reg.x1, .x2, .x4, .x5, .x7, .x9, .x16], r ∈ combClob K.M.n := by
    intro r hr
    simp only [combClob, clob, maskRegs, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have S₂ := S₁.next hL (S₁.scr.of_keepRegs k₂ (by decide)) (k₂.mono c₂)
    (U₂.mono fun w hw => by
      rw [List.mem_singleton.mp hw]
      exact List.mem_append_left _ (List.mem_map_of_mem hRy))
  obtain ⟨rxy, -, ryz, -⟩ := hL.other_ne
  have hws : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ winWs K := fun x hx => winOther_ws K x (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> win_mem)
  have eR : ∀ x ∈ [K.R.x, K.R.z], x ≠ K.R.y →
      wordsVal s₂.mem base x K.M.n = wordsVal s₁.mem base x K.M.n := by
    intro x hx hne
    have hxw : x ∈ winWs K := hws x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h <;> simp [h])
    refine U₂.wordsVal (fun w hw => ?_) (by have := hL.lay.le x (winWs_slots K x hxw); omega)
    rw [List.mem_singleton.mp hw]
    exact hL.apart₂ hxw (hws _ (by simp)) hne
  have ex₂ := eR K.R.x (by simp) rxy
  have ez₂ := eR K.R.z (by simp) (Ne.symm ryz)
  have tm : ∀ {x}, wordsVal s₂.mem base x K.M.n = wordsVal s₁.mem base x K.M.n →
      tmv C K.M.n base s₂ x = tmv C K.M.n base s₁ x := fun h => by
    show toM _ _ _ = toM _ _ _; rw [h]
  have hZ : (wordsVal s₁.mem base K.E.z K.M.n = 0) ↔ Z = 0 := by
    rw [← toM_eq_zero_iff hp (l₁ _ (by simp)), ← eE]
  have ey₂ : tmv C K.M.n base s₂ K.R.y = if Z = 0 then 1 else Y := by
    by_cases h : wordsVal s₁.mem base K.E.z K.M.n = 0
    · have e₂ : wordsVal s₂.mem base K.R.y K.M.n = K.one := by rw [v₂]; simp only [h, ↓reduceIte]
      show toM _ _ _ = _
      rw [e₂, hone]; simp only [hZ.mp h, ↓reduceIte]
    · have e₂ : wordsVal s₂.mem base K.R.y K.M.n = wordsVal s₁.mem base K.R.y K.M.n := by
        rw [v₂]; simp only [h, ↓reduceIte]
      rw [tm e₂, ey]
      exact (ite_eq_right_iff.mpr fun h' => absurd (hZ.mpr h') h).symm
  refine ⟨S₂, (k₂.gpr _ (by decide)).trans x₁, fun x hx => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [ex₂]; exact l₁ _ (by simp)
    · rw [v₂]; split
      · exact hone_lt
      · exact l₁ _ (by simp)
    · rw [ez₂]; exact l₁ _ (by simp)
  · rw [tm ex₂, ey₂, tm ez₂, ex, ez]
    exact InvJ.out hC hJ

/-- An iteration. -/
theorem winStep_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s₀ : State} (hF : WinFixed K C base s₀ P k)
    (hk8 : 8 * geom K.J ≤ k) {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ K.J)
    (hI : WinInv K C base size k P s₀ s j) :
    WP isa (WinCfg.step K) s fun s' =>
      WinInv K C base size k P s₀ s' (j - 1) ∧ s'.gpr .x19 = BitVec.ofNat 64 (j - 1) := by
  have hJ := hL.J
  rw [WinCfg.step]
  refine WP.seq (WP.mono (decCounter_ok s hj (by omega) hI.x19) fun s₁ ⟨b₁, k₁⟩ => ?_)
  have hS₁ : WinSt K C base size P s₀ s₁ := hI.st.next hL (hI.st.scr.of_keeps k₁ (by decide))
    ((Keeps.regs k₁).mono (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [combClob]))
    (by rw [k₁.mem]; exact Unch.refl _ _ _)
  have lt₁ : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₁.mem base x K.M.n < C.p := by
    rw [k₁.mem]; exact hI.lt
  have rep₁ : Rep C (tmv C K.M.n base s₁ K.R.x) (tmv C K.M.n base s₁ K.R.y)
      (tmv C K.M.n base s₁ K.R.z) (mul (winE k K.J j) P) := by
    have e : ∀ x, tmv C K.M.n base s₁ x = tmv C K.M.n base s x := fun x => by
      show toM _ _ _ = toM _ _ _; rw [k₁.mem]
    rw [e, e, e]; exact hI.rep
  refine WP.seq (WP.mono (quad_ok hL hA hp hC hM3 hP hpn hone_lt hone hF hS₁ lt₁ rep₁)
    fun s₅ ⟨S₅, x₅, l₅, r₅⟩ => ?_)
  have hx₅ : s₅.gpr .x19 = BitVec.ofNat 64 (j - 1) := by rw [x₅, b₁]
  obtain ⟨-, -, -, hz₅⟩ := S₅.ro_tmv hL hF
  have hbits₅ : ∀ t < 4 * K.J, s₅.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by
      have := hL.bits
      rw [S₅.unch.byte (fun w hw => by have := hL.bits_w w hw; omega) (by have := S₅.scr.nowrap; omega)]
      exact hF.bits t ht
  refine WP.seq (WP.mono (winEntry_ok hL hA hC (P := P) hpn hone_lt hone S₅.scr S₅.mod
    (i := j - 1) (by omega) hx₅ hbits₅ hz₅ S₅.tbl) fun s₆ E₆ => ?_)
  have hn := S₅.scr.nowrap
  have hEW : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n), (K.neg, 8 * K.M.n),
      (K.M.tmp, 8 * K.M.n)], w ∈ loopW K := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton]
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨_, winE_mem _ (by simp), rfl⟩
    · exact Or.inl ⟨_, winE_mem _ (by simp), rfl⟩
    · exact Or.inl ⟨_, winE_mem _ (by simp), rfl⟩
    · exact Or.inl ⟨_, winE_mem _ (by simp), rfl⟩
    · exact Or.inr rfl
  have S₆ := S₅.next hL E₆.scr E₆.keep (E₆.unch.mono hEW)
  -- `R` is apart from what the entry writes.
  obtain ⟨-, -, -, hRo, -⟩ := hL.other_ne
  have eR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₆.mem base x K.M.n = wordsVal s₅.mem base x K.M.n := by
    intro x hx
    have hxw : x ∈ winWs K := winOther_ws K x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> win_mem)
    refine E₆.unch.wordsVal (fun w hw => ?_) (by
      have := hL.lay.le x (winWs_slots K x hxw); omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    have hne : ∀ y ∈ [K.E.x, K.E.y, K.E.z, K.neg], x ≠ y := fun y hy e => hRo x hx (by
      rw [e]; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> simp)
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact hL.apart₂ hxw (winOther_ws K _ (winE_mem _ (by simp))) (hne _ (by simp))
    · exact hL.apart₂ hxw (winOther_ws K _ (winE_mem _ (by simp))) (hne _ (by simp))
    · exact hL.apart₂ hxw (winOther_ws K _ (winE_mem _ (by simp))) (hne _ (by simp))
    · exact hL.apart₂ hxw (winOther_ws K _ (winE_mem _ (by simp))) (hne _ (by simp))
    · exact hL.lay.tmp x (winWs_slots K x hxw)
  have lt₆ : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₆.mem base x K.M.n < C.p := fun x hx => by
    rw [eR x hx]; exact l₅ x hx
  have rep₆ : Rep C (tmv C K.M.n base s₆ K.R.x) (tmv C K.M.n base s₆ K.R.y)
      (tmv C K.M.n base s₆ K.R.z) (mul (16 * winE k K.J j) P) := by
    have e : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base s₆ x = tmv C K.M.n base s₅ x := fun x hx => by
      show toM _ _ _ = toM _ _ _; rw [eR x hx]
    rw [e _ (by simp), e _ (by simp), e _ (by simp)]; exact r₅
  refine WP.mono (sumStep_ok hL hA hp hC hM3 hF S₆ (hC.onCurve_mul hP _)
    (onCurve_winPt hC hP k (j - 1)) lt₆ E₆.lt rep₆ E₆.rep) fun s₇ ⟨S₇, x₇, l₇, r₇⟩ => ?_
  have hadd := win_add hC hP (k := k) (J := K.J) (j := j - 1) hk8 (by omega)
  rw [Nat.sub_add_cancel hj] at hadd
  rw [hadd] at r₇
  have hx₇ : s₇.gpr .x19 = BitVec.ofNat 64 (j - 1) := by rw [x₇, E₆.x19, hx₅]
  exact ⟨⟨S₇, hx₇, l₇, r₇⟩, hx₇⟩

/-- `[k - 8 Σ_{i<J} 16^i]P` into `R`, for `8 Σ_{i<J} 16^i ≤ k < 16^J` whose bits
are the table at `K.bits`; only `combClob` and `winW` change. -/
theorem window_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s : State} (hs : Scr s base size)
    (hM : ModOk K.M size C.p s.mem base) (hF : WinFixed K C base s P k) (hk : k < 16 ^ K.J)
    (hk8 : 8 * geom K.J ≤ k) :
    WP isa (WinCfg.window K) s fun s' => KeepRegs (combClob K.M.n) s s' ∧
      Unch base (winW K) s.mem s'.mem ∧ ModOk K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (mul (k - 8 * geom K.J) P) := by
  have hn := hs.nowrap
  have hJ := hL.J
  rw [WinCfg.window]
  refine WP.seq (WP.mono (build_ok hL hA hp hC hM3 hP hs hM hF) fun s₁ B => ?_)
  have S₁ : WinSt K C base size P s s₁ :=
    ⟨B.scr, B.keep.mono clob_combClob, B.unch, B.mod, B.tbl⟩
  obtain ⟨rxy, rxz, ryz, -⟩ := hL.other_ne
  have wR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ winOther K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> win_mem
  have le : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x + 8 * K.M.n ≤ size := fun x hx =>
    hL.lay.le x (winOther_mem (wR x hx))
  have al : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x % 8 = 0 := fun x hx => hA.sl x (winOther_mem (wR x hx))
  have ap := fun {x y} (hx : x ∈ [K.R.x, K.R.y, K.R.z]) (hy : y ∈ [K.R.x, K.R.y, K.R.z]) (h : x ≠ y) =>
    hL.apart₂ (winOther_ws K x (wR x hx)) (winOther_ws K y (wR y hy)) h
  have axy := ap (x := K.R.x) (y := K.R.y) (by simp) (by simp) rxy
  have axz := ap (x := K.R.x) (y := K.R.z) (by simp) (by simp) rxz
  have ayz := ap (x := K.R.y) (y := K.R.z) (by simp) (by simp) ryz
  have hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hone_lt
  refine WP.seq ?_
  rw [WinCfg.init, List.append_assoc, List.append_assoc, WP.block_append_iff]
  have W1 := setConst_ok S₁.scr (n := K.M.n) (o := K.R.x) (x := 0) (le _ (by simp)) (al _ (by simp))
    (Nat.two_pow_pos _)
  refine WP.mono W1 fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := S₁.scr.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  have W2 := setConst_ok hs₂ (n := K.M.n) (o := K.R.y) (x := K.one) (le _ (by simp)) (al _ (by simp))
    (Nat.lt_trans hone_lt hpn)
  refine WP.mono W2 fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [WP.block_append_iff]
  have W3 := setConst_ok hs₃ (n := K.M.n) (o := K.R.z) (x := 0) (le _ (by simp)) (al _ (by simp))
    (Nat.two_pow_pos _)
  refine WP.mono W3 fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  refine WP.mono (setCounter_ok s₄ (j := K.J) (by omega)) fun s₅ ⟨b₅, k₅⟩ => ?_
  have hU : Unch base (loopW K) s₁.mem s₅.mem := by
    rw [k₅.mem]
    refine (O₂.unch.trans (O₃.unch.trans O₄.unch)).mono fun w hw => ?_
    simp only [List.mem_append, List.mem_singleton] at hw
    simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton]
    refine Or.inl ⟨w.1, ?_, ?_⟩
    · rcases hw with rfl | rfl | rfl
      · exact wR _ (by simp)
      · exact wR _ (by simp)
      · exact wR _ (by simp)
    · rcases hw with rfl | rfl | rfl <;> rfl
  have c1 : ∀ r ∈ [Reg.x1], r ∈ combClob K.M.n := fun r hr =>
    combClob_mem (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hr)))
  have S₅ : WinSt K C base size P s s₅ := S₁.next hL (hs₄.of_keeps k₅ (by decide))
    ((((k₂.mono c1).trans (k₃.mono c1)).trans (k₄.mono c1)).trans
      ((Keeps.regs k₅).mono (by intro r hr; simp only [List.mem_singleton] at hr; subst hr
                                simp [combClob]))) hU
  have b64 : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := le x hx; omega
  have vx : wordsVal s₅.mem base K.R.x K.M.n = 0 := by
    rw [k₅.mem, O₄.wordsVal axz (b64 _ (by simp)), O₃.wordsVal axy (b64 _ (by simp)), e₂]
  have vy : wordsVal s₅.mem base K.R.y K.M.n = K.one := by
    rw [k₅.mem, O₄.wordsVal ayz (b64 _ (by simp)), e₃]
  have vz : wordsVal s₅.mem base K.R.z K.M.n = 0 := by rw [k₅.mem, e₄]
  have I₅ : WinInv K C base size k P s s₅ K.J := by
    refine ⟨S₅, b₅, fun x hx => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · rw [vx]; exact hp0
      · rw [vy]; exact hone_lt
      · rw [vz]; exact hp0
    · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
      rw [vx, vy, vz, toM_zero, hone, winE_top hk, mul_zero_pt']
      exact rep_infinity' hC
  exact countLoop_ok (Inv := fun j s' => WinInv K C base size k P s s' j) (n := K.J) (by omega)
    (fun j s' h1 h2 hi => winStep_ok hL hA hp hC hM3 hP hpn hone_lt hone hF hk8 h1 h2 hi)
    (fun s' hi => ⟨hi.st.keep, hi.st.unch, hi.st.mod, hi.lt, by rw [← winE_zero]; exact hi.rep⟩)
    hJ.1 I₅

end VG.Proof.Weierstrass.AArch64
