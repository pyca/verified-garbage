import VerifiedGarbage.Proof.Weierstrass.X86_64.WinEntry
import VerifiedGarbage.Proof.Weierstrass.X86_64.Flags
import VerifiedGarbage.Proof.Weierstrass.X86_64.QuadCounter
import VerifiedGarbage.Proof.Weierstrass.JacMul

/-!
# The window method on x86-64: the loop's frame and 

As on AArch64: what holds through the loop (`WinSt`, the table surviving what
the loop writes), the addition of the entry (`sumStep_ok`), and `R = 16 R`
(`quad_ok`): four doublings in Jacobian coordinates (`jac_ok`), and
`Y = 1` where the result is `O` (`ySel_ok`: the mask of `E.z = 0`,
`winZeroMask_ok`, selecting Montgomery's one word by word, `ySelWord_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

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
theorem TblOkR.unch {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    {Rp : Fe C → Fe C → Fe C → Point C → Prop}
    {P : Point C} {s s' : State} (hT : TblOkR K C base Rp P 8 s) (hU : Unch base (loopW K) s.mem s'.mem)
    (hn : base.toNat + size ≤ 2 ^ 64) : TblOkR K C base Rp P 8 s' := by
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
structure WinStR (K : WinCfg) (C : Curve) (base : Addr) (size : Nat)
    (Rp : Fe C → Fe C → Fe C → Point C → Prop) (P : Point C) (s₀ s : State) : Prop where
  scr : Scr s base size
  keep : KeepRegs (powClob K.M.n) s₀ s
  unch : Unch base (winW K) s₀.mem s.mem
  mod : ModOkW K.M size C.p s.mem base
  tbl : TblOkR K C base Rp P 8 s

/-- `WinStR` with the table in projective coordinates. -/
abbrev WinSt (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ s : State) : Prop :=
  WinStR K C base size (Rep C) P s₀ s

/-- The state after a change of `loopW` only. -/
theorem WinStR.next {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    {Rp : Fe C → Fe C → Fe C → Point C → Prop}
    {P : Point C} {s₀ s s' : State} (h : WinStR K C base size Rp P s₀ s) (hs' : Scr s' base size)
    (hk : KeepRegs (powClob K.M.n) s s') (hU : Unch base (loopW K) s.mem s'.mem) :
    WinStR K C base size Rp P s₀ s' :=
  ⟨hs', h.keep.trans hk, (h.unch.trans hU).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact loopW_sub K w hw,
    h.mod.unch hU (fun w hw => winW_mo hL h.mod w (loopW_sub K w hw)) h.scr.nowrap,
    TblOkR.unch hL h.tbl hU h.scr.nowrap⟩

theorem WinStR.ro_tmv {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    {Rp : Fe C → Fe C → Fe C → Point C → Prop}
    {P : Point C} {s₀ s : State} (h : WinStR K C base size Rp P s₀ s) (hF : WinFixed K C base s₀ P k) :
    tmv C K.M.n base s K.S.a = Fin.ofNat C.p C.a ∧ tmv C K.M.n base s K.S.b3 = Fin.ofNat C.p C.b ∧
      (∀ x ∈ winRo K, wordsVal s.mem base x K.M.n < C.p) ∧ wordsVal s.mem base K.zero K.M.n = 0 := by
  have hn := h.scr.nowrap
  refine ⟨?_, ?_, fun x hx => ?_, ?_⟩
  · rw [winRo_tmv hL h.unch hn (by simp [winRo])]; exact hF.a
  · rw [winRo_tmv hL h.unch hn (by simp [winRo])]; exact hF.b
  · rw [winRo_val hL h.unch hn hx]; exact hF.ro_lt x hx
  · rw [winRo_val hL h.unch hn (by simp [winRo])]; exact hF.zero

/-- `R = R + E`, for `R` representing `PR` and `E` `PQ`. -/
theorem sumStep_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    {Rp : Fe C → Fe C → Fe C → Point C → Prop}
    {s₀ s : State} (hF : WinFixed K C base s₀ P k) (hS : WinStR K C base size Rp P s₀ s)
    {PR PQ : Point C} (hPR : onCurve C PR = true) (hPQ : onCurve C PQ = true)
    (hltR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hltq : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : Rep C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z) PR)
    (hQ : Rep C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z) PQ) :
    WP isa (Code.seq (fprogB K.M (rcb3 K.S K.R K.E K.D)) (.block (copyPt K.M.n K.R K.D))).inline s fun s' =>
      WinStR K C base size Rp P s₀ s' ∧ s'.gpr .rbx = s.gpr .rbx ∧
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
  refine WP.mono (winAdd_ok hL hp hS.scr hS.mod hlt) fun s' S => ?_
  have hV := S.val
  rw [tb] at hV
  exact ⟨hS.next hL S.scr (S.keep.mono clob_powClob) S.unch, S.keep.gpr _ (rbx_not_clob _), S.lt,
    hC.add3 hM3 hPR hPQ hR hQ hV.symm⟩

/-- The loop's invariant at `rbx = j`: `R` represents `[winE k J j]P`. -/
structure WinInv (K : WinCfg) (C : Curve) (base : Addr) (size k : Nat) (P : Point C) (s₀ s : State)
    (j : Nat) : Prop where
  st : WinSt K C base size P s₀ s
  rbx : s.gpr .rbx = BitVec.ofNat 64 j
  lt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p
  rep : Rep C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
    (mul (winE k K.J j) P)

/-! ## Four doublings in Jacobian coordinates -/

/-- A field program on numbered slots, writing slots of `winOther`: the loop's frame. -/
theorem winN_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {N : List FOp} (hN : NumOk N) {p q o : Pt}
    (hAp : RcbApart K.S p q o) (hSl : ∀ x ∈ rcbW K.S o ++ rcbR K.S p q, x ∈ winSlots K)
    (hW : ∀ x ∈ rcbW K.S o, x ∈ winOther K) {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (· ∈ winSlots K) V E s) (hV : ∀ x ∈ rcbR K.S p q, x ∈ V) :
    WP isa (fprogB K.M (ofN N K.S p q o)).inline s fun s' => KeepRegs (clob K.M.n) s s' ∧
      Unch base (loopW K) s.mem s'.mem ∧ ∃ E' : Nat → Fe C,
      Inv K.M base size C.p (· ∈ winSlots K) ([o.x, o.y, o.z] ++ V) E' s' ∧
      (∀ x, x ∉ rcbW K.S o → E' x = E x) ∧
      (E' o.x, E' o.y, E' o.z) = (runOps N (fun y => E (rcbσ K.S p q o y)) 6,
        runOps N (fun y => E (rcbσ K.S p q o y)) 7, runOps N (fun y => E (rcbσ K.S p q o y)) 8) := by
  refine (WP.mono (ofN_ok hL.lay hp hN hAp hSl hI hV)
    fun s' ⟨k, I, v⟩ => ⟨⟨k.gpr, k.rd, k.wr⟩, k.unch.mono fun w hw => ?_, _, I,
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

/-- Changing only the public loop counter preserves the field environment. -/
theorem Inv.rbxKeeps {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
    {V : List Nat} {E : Nat → Fin m} {s s' : State} (h : Inv M base size m Sl V E s)
    (hk : Keeps [.rbx] s s') : Inv M base size m Sl V E s' :=
  ⟨h.scr.of_keeps hk (by decide), by rw [hk.2.1]; exact h.mod, h.sl,
    by rw [hk.2.1]; exact h.lt, by rw [hk.2.1]; exact h.val⟩

/-- The public counter is among the registers the window loop may change. -/
theorem WinStR.rbxKeeps {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    {Rp : Fe C → Fe C → Fe C → Point C → Prop}
    {P : Point C} {s₀ s s' : State} (h : WinStR K C base size Rp P s₀ s)
    (hk : Keeps [.rbx] s s') : WinStR K C base size Rp P s₀ s' :=
  h.next hL (h.scr.of_keeps hk (by decide)) ((Keeps.regs hk).mono (by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [powClob]))
    (by rw [hk.2.1]; exact Unch.refl _ _ _)

/-- `R = 16 R` in Jacobian coordinates, but `Y`: the triple `(X : Y : Z)` stands for
`[16 e]P` (or `Z = 0`), `R` is `(XZ : Y : Z³)` and `E.z` is `Z`. -/
theorem jac_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) {s₀ s : State} (hF : WinFixed K C base s₀ P k)
    (hS : WinSt K C base size P s₀ s) {i : Nat} (hi : i < 4096)
    (hb : s.gpr .rbx = BitVec.ofNat 64 i) {e : Nat}
    (hlt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : Rep C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
      (mul e P)) :
    WP isa (WinCfg.jac K).inline s fun s' =>
      WinSt K C base size P s₀ s' ∧ s'.gpr .rbx = s.gpr .rbx ∧
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
  simp only [WinCfg.jac, toJ_eq, fromJ_eq]
  -- Into Jacobian coordinates, in `E`.
  refine WP.seq (WP.mono (winN_ok hL hp toJN_ok a1 w1.1 w1.2 I₀ (by rcb_sub))
    fun s₁ ⟨k₁, U₁, E₁, I₁, _, v₁⟩ => ?_)
  have S₁ := hS.next hL I₁.scr (k₁.mono clob_powClob) U₁
  have J₁ : InvJ C (E₁ K.E.x) (E₁ K.E.y) (E₁ K.E.z) (mul e P) :=
    InvJ.of_toJ (z := tmv C K.M.n base s K.zero) hC hR (show toM _ _ _ = 0 by rw [hz]; exact toM_zero _ _)
      (v₁.trans (toJN_run _))
  -- Two iterations of the same pair of doublings.
  let V := [K.E.x, K.E.y, K.E.z, K.S.a, K.S.b3, K.zero]
  have I₁' : Inv K.M base size C.p (· ∈ winSlots K) V E₁ s₁ :=
    I₁.sub (by intro x hx; simp only [V, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
               rcases hx with h | h | h | h | h | h <;> simp [h])
  refine WP.seq (WP.mono (quadStart_ok s₁ ((k₁.gpr _ (rbx_not_clob _)).trans hb))
    fun s₂ ⟨b₂, kc₂⟩ => ?_)
  let LI := fun j st => WinSt K C base size P s₀ st ∧
    st.gpr .rbx = BitVec.ofNat 64 (i + 4096 * j) ∧ ∃ E : Nat → Fe C,
    Inv K.M base size C.p (· ∈ winSlots K) V E st ∧
    InvJ C (E K.E.x) (E K.E.y) (E K.E.z) (mul (4 ^ (2 - j) * e) P)
  have start : LI 2 s₂ := ⟨S₁.rbxKeeps hL kc₂, b₂, E₁, I₁'.rbxKeeps kc₂, by simpa using J₁⟩
  have body : ∀ j st, 1 ≤ j → j ≤ 2 → LI j st →
      WP isa (WinCfg.jacPair K).inline st fun st' => LI (j - 1) st' ∧ st'.cf = some (decide (j - 1 = 0)) := by
    intro j st hj hj' ⟨S, b, E, I, J⟩
    simp only [WinCfg.jacPair, WinCfg.double, dblJSChoice_eq]
    refine WP.seq (WP.mono (winN_ok hL hp (dblJSChoiceN_ok (K.M.n ≤ 6 : Bool)) a2 w2.1 w2.2 I (by
      dsimp [V]; rcb_sub)) fun st₁ ⟨k₁', U₁', E₁', I₁', _, v₁'⟩ => ?_)
    have S₁' := S.next hL I₁'.scr (k₁'.mono clob_powClob) U₁'
    have J₁' := InvJ.dbl' hC hM3 (hQ _) J (v₁'.trans (dblJSChoiceN_run (K.M.n ≤ 6 : Bool) _))
    rw [hC.double hP] at J₁'
    refine WP.seq (WP.mono (winN_ok hL hp (dblJSChoiceN_ok (K.M.n ≤ 6 : Bool)) a3 w3.1 w3.2 I₁' (by
      dsimp [V]; rcb_sub)) fun st₂ ⟨k₂', U₂', E₂', I₂', _, v₂'⟩ => ?_)
    have S₂' := S₁'.next hL I₂'.scr (k₂'.mono clob_powClob) U₂'
    have J₂' := InvJ.dbl' hC hM3 (hQ _) J₁' (v₂'.trans (dblJSChoiceN_run (K.M.n ≤ 6 : Bool) _))
    rw [hC.double hP] at J₂'
    have ar : 2 * (2 * (4 ^ (2 - j) * e)) = 4 ^ (2 - (j - 1)) * e := by
      have hj12 : j = 1 ∨ j = 2 := by omega
      rcases hj12 with rfl | rfl <;> simp <;> omega
    rw [ar] at J₂'
    have b' : st₂.gpr .rbx = BitVec.ofNat 64 (i + 4096 * j) := by
      rw [k₂'.gpr _ (rbx_not_clob _), k₁'.gpr _ (rbx_not_clob _), b]
    refine WP.mono (quadCount_ok st₂ hi hj hj' b') fun st₃ ⟨b₃, c₃, kc₃⟩ => ?_
    have I₂'' : Inv K.M base size C.p (· ∈ winSlots K) V E₂' st₂ :=
      I₂'.sub (by
        intro x hx
        simp only [V, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx ⊢
        rcases hx with h | h | h | h | h | h <;> simp [h])
    exact ⟨⟨S₂'.rbxKeeps hL kc₃, b₃, E₂', I₂''.rbxKeeps kc₃, J₂'⟩, c₃⟩
  refine WP.seq (WP.mono (quadLoop_ok body (fun _ h => h) start)
    fun s₅ ⟨S₅, b₅, E₅, I₅, J₅⟩ => ?_)
  have rb₅ : s₅.gpr .rbx = s.gpr .rbx := by simpa only [Nat.mul_zero, Nat.add_zero, hb] using b₅
  have J₅ : InvJ C (E₅ K.E.x) (E₅ K.E.y) (E₅ K.E.z) (mul (16 * e) P) := by simpa using J₅
  -- Back to projective coordinates, in `R`.
  refine WP.mono (winN_ok hL hp fromJN_ok a4 w4.1 w4.2 I₅ (by dsimp [V]; rcb_sub))
    fun s₆ ⟨k₆, U₆, E₆, I₆, o₆, v₆⟩ => ?_
  have S₆ := S₅.next hL I₆.scr (k₆.mono clob_powClob) U₆
  obtain ⟨-, -, -, hz₅⟩ := S₅.ro_tmv hL hF
  have z₅ : E₅ K.zero = 0 := by
    rw [← I₅.val _ (by simp [V]), hz₅]; exact toM_zero _ _
  have r₆ : (E₆ K.R.x, E₆ K.R.y, E₆ K.R.z) = (E₅ K.E.x * E₅ K.E.z, E₅ K.E.y + E₅ K.zero,
      E₅ K.E.z * E₅ K.E.z * E₅ K.E.z) := v₆.trans (fromJN_run _)
  simp only [z₅, Prod.mk.injEq] at r₆
  have ez : E₆ K.E.z = E₅ K.E.z := o₆ _ (a4.apart _ (by simp [rcbR]))
  refine ⟨S₆, by
      rw [k₆.gpr _ (rbx_not_clob _), rb₅],
    fun x hx => I₆.lt x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with
      h | h | h | h <;> simp [V, h]),
    E₅ K.E.x, E₅ K.E.y, E₅ K.E.z, J₅, ?_, ?_, ?_, ?_⟩
  · exact (I₆.val _ (by simp)).trans r₆.1
  · exact (I₆.val _ (by simp)).trans (r₆.2.1.trans (by grind))
  · exact (I₆.val _ (by simp)).trans r₆.2.2
  · exact (I₆.val _ (by simp [V])).trans ez

/-! ## `Y = 1` where `Z = 0` -/

/-- `rdx = -CF`. -/
theorem zmSbb_ok (s : State) {b : Bool} (hb : s.cf = some b) :
    WP isa (.block [.alu .sbb .rdx (.reg .rdx)]) s fun s' =>
      s'.gpr .rdx = (if b then BitVec.allOnes 64 else 0) ∧ Keeps [.rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.map_some, hb, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨by cases b <;> simp, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `cmp rdx, 1` sets `CF` iff `rdx = 0`. -/
theorem zmCmp_ok (s : State) :
    WP isa (.block [.alu .cmp .rdx (.imm 1)]) s fun s' =>
      s'.cf = some (decide (s.gpr .rdx = 0)) ∧ Keeps [] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.cf_arithFlags, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r _ => by simp only [RegUpd.gpr_arithFlags], rfl, rfl, rfl⟩
  have : (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 1 := by decide
  rw [this]
  congr 1
  simp only [Nat.lt_one_iff]
  exact propext ⟨fun h => BitVec.eq_of_toNat_eq h, fun h => by rw [h]; rfl⟩

/-- The mask `rdx` of `[E.z] = 0`. -/
theorem winZeroMask_ok (K : WinCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hn : 0 < K.M.n) (ha : K.E.z + 8 * K.M.n ≤ size) :
    WP isa (.block (WinCfg.zeroMask K)) s fun s' =>
      s'.gpr .rdx = mask (wordsVal s.mem base K.E.z K.M.n = 0) ∧ Keeps [.rdx] s s' := by
  rw [WinCfg.zeroMask, List.append_assoc, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov .rdx (.mem (sc K.E.z))]) s (fun s₁ =>
      s₁.gpr .rdx = word s.mem base K.E.z ∧ Keeps [.rdx] s s₁) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc_sc hs (d := K.E.z) (by omega),
      Option.map_some, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ors_ok hs₁ (a := K.E.z) (K.M.n - 1) (by omega)) fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [e₁, k₁.2.1] at e₂
  have hz : s₂.gpr .rdx = 0 ↔ wordsVal s.mem base K.E.z K.M.n = 0 := by
    rw [e₂, wordsVal_eq_zero_iff]
    constructor
    · intro ⟨h₀, h⟩ j hj
      rcases j with _ | j
      · simpa using h₀
      · exact h j (by omega)
    · intro h
      exact ⟨by simpa using h 0 hn, fun j hj => h (j + 1) (by omega)⟩
  rw [show ([.alu .cmp .rdx (.imm 1), .alu .sbb .rdx (.reg .rdx)] : List Instr) =
    [.alu .cmp .rdx (.imm 1)] ++ [.alu .sbb .rdx (.reg .rdx)] from rfl, WP.block_append_iff]
  refine WP.mono (zmCmp_ok s₂) fun s₃ ⟨c₃, k₃⟩ => ?_
  refine WP.mono (zmSbb_ok s₃ c₃) fun s₄ ⟨e₄, k₄⟩ =>
    ⟨?_, ((k₁.trans k₂).trans (k₃.mono (fun _ h => absurd h List.not_mem_nil))).trans k₄⟩
  rw [e₄]
  simp only [mask, decide_eq_true_eq, hz]

theorem sel_mask (a b : BitVec 64) (p : Prop) [Decidable p] :
    a ^^^ ((b ^^^ a) &&& mask p) = if p then b else a := by
  by_cases h : p
  · simp only [mask, h, ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm b a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · simp [mask, h]

/-- Word `w` of `R.y`: Montgomery's one where `rdx` is the mask of `p`. -/
theorem ySelWord_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (K : WinCfg)
    (p : Prop) [Decidable p] (hdx : s.gpr .rdx = mask p) {w : Nat} (ho : K.R.y + 8 * w + 8 ≤ size) :
    WP isa (.block (WinCfg.ySelWord K w)) s fun t =>
      t.mem = s.mem.writeW (off base (K.R.y + 8 * w))
        (if p then wordOf K.one w else word s.mem base (K.R.y + 8 * w)) ∧
      KeepRegs [.rax, .r8] s t := by
  have hn := hs.nowrap
  apply WP.of_runBlock
  simp only [WinCfg.ySelWord, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.load64, State.store64, ea_sc, hdx, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    RegUpd.mem_arithFlags, reduceCtorEq, ite_true, ite_false, hs.rdi,
    ld_sc hs (d := K.R.y + 8 * w) (by omega), st_sc hs (d := K.R.y + 8 * w) (by omega),
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [sel_mask], ⟨fun r hr => ?_, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]

/-- The first `k` words of `R.y`. -/
theorem ySelWords_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (K : WinCfg)
    (p : Prop) [Decidable p] (hdx : s.gpr .rdx = mask p) :
    ∀ k, K.R.y + 8 * k ≤ size →
    WP isa (.block ((List.range k).flatMap (WinCfg.ySelWord K))) s fun t =>
      (∀ w < k, word t.mem base (K.R.y + 8 * w) =
        if p then wordOf K.one w else word s.mem base (K.R.y + 8 * w)) ∧
      KeepRegs [.rax, .r8] s t ∧ Outside base K.R.y (8 * k) s.mem t.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ySelWords_ok hs K p hdx k (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    refine WP.mono (ySelWord_ok hs₁ K p ((k₁.gpr _ (by decide)).trans hdx) (w := k) (by omega))
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
theorem ySel_ok {K : WinCfg} {base : Addr} {size : Nat} (hL : WinLay K size)
    {s : State} (hs : Scr s base size) (h1 : K.one < 2 ^ (64 * K.M.n)) :
    WP isa (.block (WinCfg.ySel K)) s fun t =>
      wordsVal t.mem base K.R.y K.M.n = (if wordsVal s.mem base K.E.z K.M.n = 0 then K.one
        else wordsVal s.mem base K.R.y K.M.n) ∧
      KeepRegs [.rax, .rdx, .r8] s t ∧
      Unch base [(K.R.y, 8 * K.M.n)] s.mem t.mem := by
  have hn := hs.nowrap
  have hy : K.R.y ∈ winSlots K := by win_mem
  have hz : K.E.z ∈ winSlots K := by win_mem
  rw [WinCfg.ySel, WP.block_append_iff]
  refine WP.mono (winZeroMask_ok K hs hL.n0 (hL.lay.le _ hz)) fun s₁ ⟨m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.mono (ySelWords_ok hs₁ K _ m₁ K.M.n (hL.lay.le _ hy))
    fun t ⟨e, kt, O⟩ => ⟨?_, ?_, ?_⟩
  · by_cases hz0 : wordsVal s.mem base K.E.z K.M.n = 0
    · simp only [hz0, ↓reduceIte]
      exact wordsVal_of_shifts _ _ _ _ _ h1 fun j hj => by simp only [e j hj, hz0, ↓reduceIte]; rfl
    · simp only [hz0, ↓reduceIte]
      rw [← k₁.2.1]
      exact wordsVal_congr₂ _ _ _ fun j hj => by simp only [e j hj, hz0, ↓reduceIte]
  · exact ((Keeps.regs k₁).mono (by decide)).trans (kt.mono (by decide))
  · rw [← k₁.2.1]; exact O.unch.mono (by simp)

/-- `R = 16 R`: `[e]P` to `[16 e]P`. -/
theorem quad_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s₀ s : State} (hF : WinFixed K C base s₀ P k)
    (hS : WinSt K C base size P s₀ s) {i : Nat} (hi : i < 4096)
    (hb : s.gpr .rbx = BitVec.ofNat 64 i) {e : Nat}
    (hlt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : Rep C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
      (mul e P)) :
    WP isa (WinCfg.quad K).inline s fun s' =>
      WinSt K C base size P s₀ s' ∧ s'.gpr .rbx = s.gpr .rbx ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (mul (16 * e) P) := by
  rw [WinCfg.quad]
  refine WP.seq (WP.mono (jac_ok hL hp hC hM3 hP hF hS hi hb hlt hR)
    fun s₁ ⟨S₁, x₁, l₁, X, Y, Z, hJ, ex, ey, ez, eE⟩ => ?_)
  have hn := S₁.scr.nowrap
  refine WP.mono (ySel_ok hL S₁.scr (Nat.lt_trans hone_lt hpn)) fun s₂ ⟨v₂, k₂, U₂⟩ => ?_
  have hRy : K.R.y ∈ winOther K := by win_mem
  have c₂ : ∀ r ∈ [Reg.rax, .rdx, .r8], r ∈ powClob K.M.n := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp [powClob, clob]
    · simp [powClob, clob]
    · exact List.mem_cons_of_mem _ (r8_mem_clob _)
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

end VG.Proof.Weierstrass.X86_64
