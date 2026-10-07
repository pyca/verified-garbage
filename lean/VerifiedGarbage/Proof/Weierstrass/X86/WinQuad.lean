import VerifiedGarbage.Proof.Weierstrass.X86.Window
import VerifiedGarbage.Proof.Weierstrass.JacMul

/-!
# The x86 window loop's frame and Jacobian doublings

The table survives each iteration's writes. The accumulator is converted
from homogeneous to Jacobian coordinates for four doublings, then converted
back. `WinFlags` and `WinFinish` handle the point at infinity.
-/

namespace VG.Proof.Weierstrass.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

open Spec.Weierstrass

/-! ## The loop -/

theorem loopW_sub (K : WinCfg) (wk : Nat) : ∀ w ∈ loopWX K wk, w ∈ winWX K wk := by
  intro w hw
  simp only [loopWX, winWX, winWs, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
  rcases hw with ⟨y, hy, rfl⟩ | rfl | rfl
  · exact Or.inl ⟨y, Or.inl hy, rfl⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- The table survives what the loop writes. -/
theorem TblOk.unch {K : WinCfg} {C : Curve} {base : Addr} {size wk : Nat} (hL : WinLay K size) (hAcc : WinWk K size wk)
    {P : Point C} {s s' : State} (hT : TblOk K C base P 8 s) (hU : Unch base (loopWX K wk) s.mem s'.mem)
    (hn : base.toNat + size ≤ 2 ^ 32) : TblOk K C base P 8 s' := by
  intro j h1 h8
  have T := hT j h1 h8
  have e : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
      wordsVal s'.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
    intro x hx
    obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K h1 h8 x hx
    have hs : K.tbl + 8 * K.M.n * i ∈ winSlots K := by
      simp only [winSlots, List.mem_append]; exact Or.inr (winTbl_mem K hi)
    refine hU.wordsVal (fun w hw => ?_) (by have := hL.lay.le _ hs; omega)
    simp only [loopWX, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with ⟨y, hy, rfl⟩ | rfl | rfl
    · exact (hL.tbl_apart (List.mem_append_right _ hy) hi).symm
    · exact hL.lay.tmp _ hs
    · exact Or.inl (hAcc.acc.sl _ hs)
  refine ⟨fun x hx => by rw [e x hx]; exact T.1 x hx, ?_⟩
  have ex : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
      tmv C K.M.n base s' x = tmv C K.M.n base s x := fun x hx => by
    show toM _ _ _ = toM _ _ _; rw [e x hx]
  rw [ex _ (by simp), ex _ (by simp), ex _ (by simp)]
  exact T.2

/-- What holds throughout the loop, from `s₀` (the state before the table). -/
structure WinSt (K : WinCfg) (wk : Nat) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ s : State) :
    Prop where
  scr : Scr s base size
  keep : KeepRegs powClob s₀ s
  unch : Unch base (winWX K wk) s₀.mem s.mem
  mod : ModOkW K.M size C.p s.mem base
  tbl : TblOk K C base P 8 s

/-- The state after a change of `loopW` only. -/
theorem WinSt.next {K : WinCfg} {C : Curve} {base : Addr} {size wk : Nat} (hL : WinLay K size) (hAcc : WinWk K size wk)
    {P : Point C} {s₀ s s' : State} (h : WinSt K wk C base size P s₀ s) (hs' : Scr s' base size)
    (hk : KeepRegs powClob s s') (hU : Unch base (loopWX K wk) s.mem s'.mem) :
    WinSt K wk C base size P s₀ s' :=
  ⟨hs', h.keep.trans hk, (h.unch.trans hU).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact loopW_sub K wk w hw,
    h.mod.unch hU (fun w hw => winW_mo hL hAcc h.mod w (loopW_sub K wk w hw)) (by have := h.scr.nowrap; omega),
    h.tbl.unch hL hAcc hU h.scr.nowrap⟩

theorem WinSt.ro_tmv {K : WinCfg} {C : Curve} {base : Addr} {size wk k : Nat} (hL : WinLay K size) (hAcc : WinWk K size wk)
    {P : Point C} {s₀ s : State} (h : WinSt K wk C base size P s₀ s) (hF : WinFixed K C base s₀ P k) :
    tmv C K.M.n base s K.S.a = Fin.ofNat C.p C.a ∧ tmv C K.M.n base s K.S.b3 = Fin.ofNat C.p C.b ∧
      (∀ x ∈ winRo K, wordsVal s.mem base x K.M.n < C.p) ∧ wordsVal s.mem base K.zero K.M.n = 0 := by
  have hn := h.scr.nowrap
  refine ⟨?_, ?_, fun x hx => ?_, ?_⟩
  · rw [winRo_tmv hL hAcc h.unch hn (by simp [winRo])]; exact hF.a
  · rw [winRo_tmv hL hAcc h.unch hn (by simp [winRo])]; exact hF.b
  · rw [winRo_val hL hAcc h.unch hn hx]; exact hF.ro_lt x hx
  · rw [winRo_val hL hAcc h.unch hn (by simp [winRo])]; exact hF.zero

/-- `R = R + E`, for `R` representing `PR` and `E` `PQ`. -/
theorem sumStep_ok {K : WinCfg} {C : Curve} {base : Addr} {size wk k : Nat} (hL : WinLay K size) (hAcc : WinWk K size wk)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    {s₀ s : State} (hF : WinFixed K C base s₀ P k) (hS : WinSt K wk C base size P s₀ s)
    {PR PQ : Point C} (hPR : onCurve C PR = true) (hPQ : onCurve C PQ = true)
    (hltR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hltq : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : Rep C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z) PR)
    (hQ : Rep C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z) PQ) :
    WP isa (.seq (fprog K.M wk (rcb3 K.S K.R K.E K.D)) (.block (copyPt K.M.n K.R K.D))) s fun s' =>
      WinSt K wk C base size P s₀ s' ∧ s'.gpr .esi = s.gpr .esi ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (Spec.Weierstrass.add PR PQ) := by
  obtain ⟨-, tb, ro_lt, -⟩ := hS.ro_tmv hL hAcc hF
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
  refine WP.mono (winAdd_ok hL hAcc hp hS.scr hS.mod hlt) fun s' S => ?_
  have hV := S.val
  rw [tb] at hV
  exact ⟨hS.next hL hAcc S.scr (S.keep.mono clob_powClob) S.unch, S.keep.gpr _ (esi_not_clob), S.lt,
    hC.add3 hM3 hPR hPQ hR hQ hV.symm⟩

/-- The loop's invariant at `esi = j`: `R` represents `[winE k J j]P`. -/
structure WinInv (K : WinCfg) (wk : Nat) (C : Curve) (base : Addr) (size k : Nat) (P : Point C) (s₀ s : State)
    (j : Nat) : Prop where
  st : WinSt K wk C base size P s₀ s
  esi : s.gpr .esi = BitVec.ofNat 32 j
  lt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p
  rep : Rep C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
    (mul (winE k K.J j) P)

/-! ## Four doublings in Jacobian coordinates -/

/-- A field program on numbered slots, writing slots of `winOther`: the loop's frame. -/
theorem winN_ok {K : WinCfg} {C : Curve} {base : Addr} {size wk : Nat} (hL : WinLay K size) (hAcc : WinWk K size wk)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {N : List FOp} (hN : NumOk N) {p q o : Pt}
    (hAp : RcbApart K.S p q o) (hSl : ∀ x ∈ rcbW K.S o ++ rcbR K.S p q, x ∈ winSlots K)
    (hW : ∀ x ∈ rcbW K.S o, x ∈ winOther K) {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (· ∈ winSlots K) V E s) (hV : ∀ x ∈ rcbR K.S p q, x ∈ V) :
    WP isa (fprog K.M wk (ofN N K.S p q o)) s fun s' => KeepRegs clob s s' ∧
      Unch base (loopWX K wk) s.mem s'.mem ∧ ∃ E' : Nat → Fe C,
      Inv K.M base size C.p (· ∈ winSlots K) ([o.x, o.y, o.z] ++ V) E' s' ∧
      (∀ x, x ∉ rcbW K.S o → E' x = E x) ∧
      (E' o.x, E' o.y, E' o.z) = (runOps N (fun y => E (rcbσ K.S p q o y)) 6,
        runOps N (fun y => E (rcbσ K.S p q o y)) 7, runOps N (fun y => E (rcbσ K.S p q o y)) 8) := by
  refine (WP.mono (ofN_ok hL.lay hAcc.acc hp hN hAp hSl hI hV)
    fun s' ⟨k, I, v⟩ => ⟨⟨k.gpr, k.rd, k.wr⟩, k.unch.mono fun w hw => ?_, _, I,
      fun x hx => runOps_of_not_out _ _ fun op hop h => hx (h ▸ ofN_out hN op hop), v⟩)
  simp only [loopWX, progW, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
  rcases hw with ⟨y, hy, rfl⟩ | rfl | rfl
  · exact Or.inl ⟨y, hW y hy, rfl⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

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
theorem jac_ok {K : WinCfg} {C : Curve} {base : Addr} {size wk k : Nat} (hL : WinLay K size) (hAcc : WinWk K size wk)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) {s₀ s : State} (hF : WinFixed K C base s₀ P k)
    (hS : WinSt K wk C base size P s₀ s) {e : Nat}
    (hlt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : Rep C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
      (mul e P)) :
    WP isa (WinCfg.jac K wk) s fun s' =>
      WinSt K wk C base size P s₀ s' ∧ s'.gpr .esi = s.gpr .esi ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      ∃ X Y Z : Fe C, InvJ C X Y Z (mul (16 * e) P) ∧ tmv C K.M.n base s' K.R.x = X * Z ∧
        tmv C K.M.n base s' K.R.y = Y ∧ tmv C K.M.n base s' K.R.z = Z * Z * Z ∧
        tmv C K.M.n base s' K.E.z = Z := by
  obtain ⟨-, -, ro_lt, hz⟩ := hS.ro_tmv hL hAcc hF
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
  simp only [WinCfg.jac, WinCfg.double, toJ_eq, fromJ_eq, dblJChoice_eq]
  -- Into Jacobian coordinates, in `E`.
  refine WP.seq (WP.mono (winN_ok hL hAcc hp toJN_ok a1 w1.1 w1.2 I₀ (by rcb_sub))
    fun s₁ ⟨k₁, U₁, E₁, I₁, _, v₁⟩ => ?_)
  have S₁ := hS.next hL hAcc I₁.scr (k₁.mono clob_powClob) U₁
  have J₁ : InvJ C (E₁ K.E.x) (E₁ K.E.y) (E₁ K.E.z) (mul e P) :=
    InvJ.of_toJ (z := tmv C K.M.n base s K.zero) hC hR (show toM _ _ _ = 0 by rw [hz]; exact toM_zero _ _)
      (v₁.trans (toJN_run _))
  refine WP.seq (WP.mono (winN_ok hL hAcc hp (dblJChoiceN_ok (K.M.n == 4)) a2 w2.1 w2.2 I₁ (by rcb_sub))
    fun s₂ ⟨k₂, U₂, E₂, I₂, _, v₂⟩ => ?_)
  have S₂ := S₁.next hL hAcc I₂.scr (k₂.mono clob_powClob) U₂
  have J₂ := InvJ.dbl' hC hM3 (hQ _) J₁ (v₂.trans (dblJChoiceN_run (K.M.n == 4) _))
  rw [hC.double hP] at J₂
  refine WP.seq (WP.mono (winN_ok hL hAcc hp (dblJChoiceN_ok (K.M.n == 4)) a3 w3.1 w3.2 I₂ (by rcb_sub))
    fun s₃ ⟨k₃, U₃, E₃, I₃, _, v₃⟩ => ?_)
  have S₃ := S₂.next hL hAcc I₃.scr (k₃.mono clob_powClob) U₃
  have J₃ := InvJ.dbl' hC hM3 (hQ _) J₂ (v₃.trans (dblJChoiceN_run (K.M.n == 4) _))
  rw [hC.double hP] at J₃
  refine WP.seq (WP.mono (winN_ok hL hAcc hp (dblJChoiceN_ok (K.M.n == 4)) a2 w2.1 w2.2 I₃ (by rcb_sub))
    fun s₄ ⟨k₄, U₄, E₄, I₄, _, v₄⟩ => ?_)
  have S₄ := S₃.next hL hAcc I₄.scr (k₄.mono clob_powClob) U₄
  have J₄ := InvJ.dbl' hC hM3 (hQ _) J₃ (v₄.trans (dblJChoiceN_run (K.M.n == 4) _))
  rw [hC.double hP] at J₄
  refine WP.seq (WP.mono (winN_ok hL hAcc hp (dblJChoiceN_ok (K.M.n == 4)) a3 w3.1 w3.2 I₄ (by rcb_sub))
    fun s₅ ⟨k₅, U₅, E₅, I₅, _, v₅⟩ => ?_)
  have S₅ := S₄.next hL hAcc I₅.scr (k₅.mono clob_powClob) U₅
  have J₅ := InvJ.dbl' hC hM3 (hQ _) J₄ (v₅.trans (dblJChoiceN_run (K.M.n == 4) _))
  rw [hC.double hP] at J₅
  have rb₅ : s₅.gpr .esi = s.gpr .esi := by
    rw [k₅.gpr _ esi_not_clob, k₄.gpr _ esi_not_clob, k₃.gpr _ esi_not_clob,
      k₂.gpr _ esi_not_clob, k₁.gpr _ esi_not_clob]
  have J₅ : InvJ C (E₅ K.E.x) (E₅ K.E.y) (E₅ K.E.z) (mul (16 * e) P) := by
    simpa only [← Nat.mul_assoc] using J₅
  -- Back to projective coordinates, in `R`.
  refine WP.mono (winN_ok hL hAcc hp fromJN_ok a4 w4.1 w4.2 I₅ (by rcb_sub))
    fun s₆ ⟨k₆, U₆, E₆, I₆, o₆, v₆⟩ => ?_
  have S₆ := S₅.next hL hAcc I₆.scr (k₆.mono clob_powClob) U₆
  obtain ⟨-, -, -, hz₅⟩ := S₅.ro_tmv hL hAcc hF
  have z₅ : E₅ K.zero = 0 := by
    rw [← I₅.val _ (by simp), hz₅]; exact toM_zero _ _
  have r₆ : (E₆ K.R.x, E₆ K.R.y, E₆ K.R.z) = (E₅ K.E.x * E₅ K.E.z, E₅ K.E.y + E₅ K.zero,
      E₅ K.E.z * E₅ K.E.z * E₅ K.E.z) := v₆.trans (fromJN_run _)
  simp only [z₅, Prod.mk.injEq] at r₆
  have ez : E₆ K.E.z = E₅ K.E.z := o₆ _ (a4.apart _ (by simp [rcbR]))
  refine ⟨S₆, by
      rw [k₆.gpr _ (esi_not_clob), rb₅],
    fun x hx => I₆.lt x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with
      h | h | h | h <;> simp [h]),
    E₅ K.E.x, E₅ K.E.y, E₅ K.E.z, J₅, ?_, ?_, ?_, ?_⟩
  · exact (I₆.val _ (by simp)).trans r₆.1
  · exact (I₆.val _ (by simp)).trans (r₆.2.1.trans (by grind))
  · exact (I₆.val _ (by simp)).trans r₆.2.2
  · exact (I₆.val _ (by simp)).trans ez


end VG.Proof.Weierstrass.X86
