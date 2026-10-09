import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase

/-!
# The window method on AArch64: `R = 16 R`

Four doublings in Jacobian coordinates (`jac_ok`), and `Y = 1` where the result is `O`
(`ySel_ok`): `quad_ok`.
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-! ## Four doublings in Jacobian coordinates -/

/-- A field program on numbered slots, writing slots of `winOther`: the loop's frame. -/
theorem winN_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {N : List FOp} (hN : NumOk N) {p q o : Pt}
    (hAp : RcbApart K.S p q o) (hSl : ∀ x ∈ rcbW K.S o ++ rcbR K.S p q, x ∈ winSlots K)
    (hW : ∀ x ∈ rcbW K.S o, x ∈ winOther K) (hLo : ∀ x ∈ rcbW K.S o ++ rcbR K.S p q, x ∈ winRo K ++ winOther K)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (· ∈ winSlots K) V E s) (hV : ∀ x ∈ rcbR K.S p q, x ∈ V) :
    WP isa (fprogB K.M (ofN N K.S p q o)) s fun s' => KeepRegs (clob K.M.n) s s' ∧
      Unch base (loopW K) s.mem s'.mem ∧ ∃ E' : Nat → Fe C,
      Inv K.M base size C.p (· ∈ winSlots K) ([o.x, o.y, o.z] ++ V) E' s' ∧
      (∀ x, x ∉ rcbW K.S o → E' x = E x) ∧
      (E' o.x, E' o.y, E' o.z) = (runOps N (fun y => E (rcbσ K.S p q o y)) 6,
        runOps N (fun y => E (rcbσ K.S p q o y)) 7, runOps N (fun y => E (rcbσ K.S p q o y)) 8) := by
  refine (WP.mono (ofN_ok hL.lay hA.al hp hN hAp hSl (hA.low hLo) hI hV)
    fun s' ⟨k, I, v⟩ => ⟨⟨k.gpr, k.rd, k.wr, k.sp⟩, k.unch.mono fun w hw => ?_, _, I,
      fun x hx => runOps_of_not_out _ _ fun op hop h => hx (h ▸ ofN_out hN op hop), v⟩)
  simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw ⊢
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · exact Or.inl ⟨y, hW y hy, rfl⟩
  · exact Or.inr rfl

/-- The slots of a numbered program from `p` and `q` into `o`, a point written. -/
theorem winJ_sl {K : WinCfg} {o p q : Pt} (ho : ∀ x ∈ [o.x, o.y, o.z], x ∈ winOther K)
    (hp : ∀ x ∈ [p.x, p.y, p.z], x ∈ winRo K ++ winOther K)
    (hq : ∀ x ∈ [q.x, q.y, q.z], x ∈ winRo K ++ winOther K) :
    (∀ x ∈ rcbW K.S o ++ rcbR K.S p q, x ∈ winSlots K) ∧ (∀ x ∈ rcbW K.S o, x ∈ winOther K) ∧
      ∀ x ∈ rcbW K.S o ++ rcbR K.S p q, x ∈ winRo K ++ winOther K := by
  have hW : ∀ x ∈ rcbW K.S o, x ∈ winOther K := by
    intro x hx
    simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h | h | h | h <;> subst h
    · win_in
    · win_in
    · win_in
    · win_in
    · win_in
    · win_in
    · exact ho _ (by simp)
    · exact ho _ (by simp)
    · exact ho _ (by simp)
  have hL : ∀ x ∈ rcbW K.S o ++ rcbR K.S p q, x ∈ winRo K ++ winOther K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_right _ (hW x hx)
    · simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h | h | h | h | h | h <;> subst h
      · win_in
      · win_in
      · exact hp _ (by simp)
      · exact hp _ (by simp)
      · exact hp _ (by simp)
      · exact hq _ (by simp)
      · exact hq _ (by simp)
      · exact hq _ (by simp)
  refine ⟨fun x hx => ?_, hW, hL⟩
  have := hL x hx
  simp only [winSlots, List.mem_append] at this ⊢
  exact Or.inl this

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
    rcases hx with rfl | rfl | rfl <;> win_in
  have oE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∈ winOther K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> win_in
  have oD : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ winOther K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> win_in
  have sZ : ∀ x ∈ [(WinCfg.zeroPt K).x, (WinCfg.zeroPt K).y, (WinCfg.zeroPt K).z], x ∈ winRo K ++ winOther K := by
    intro x hx
    simp only [WinCfg.zeroPt, List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
    subst hx; win_in
  have sl := fun (P : Pt) (h : ∀ x ∈ [P.x, P.y, P.z], x ∈ winOther K) x (hx : x ∈ [P.x, P.y, P.z]) =>
    List.mem_append_right (winRo K) (h x hx)
  have w1 := winJ_sl oE (sl _ oR) sZ
  have w2 := winJ_sl oD (sl _ oE) (sl _ oE)
  have w3 := winJ_sl oE (sl _ oD) (sl _ oD)
  have w4 := winJ_sl oR (sl _ oE) sZ
  have V0 : ∀ x ∈ [K.S.a, K.S.b3, K.zero, K.R.x, K.R.y, K.R.z],
      x ∈ winSlots K ∧ wordsVal s.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | h | h | h
    · exact ⟨by win_in, ro_lt _ (by simp [winRo])⟩
    · exact ⟨by win_in, ro_lt _ (by simp [winRo])⟩
    · exact ⟨by win_in, ro_lt _ (by simp [winRo])⟩
    all_goals exact ⟨winOther_mem (oR _ (by simp [h])), hlt _ (by simp [h])⟩
  have I₀ : Inv K.M base size C.p (· ∈ winSlots K) [K.S.a, K.S.b3, K.zero, K.R.x, K.R.y, K.R.z]
      (tmv C K.M.n base s) s :=
    ⟨hS.scr, hS.mod, fun x hx => (V0 x hx).1, fun x hx => (V0 x hx).2, fun _ _ => rfl⟩
  have hQ := fun (a : Nat) => hC.onCurve_mul hP a
  simp only [WinCfg.jac, toJ_eq, WinCfg.double, dblJChoice_eq, fromJ_eq]
  -- Into Jacobian coordinates, in `E`.
  refine WP.seq (WP.mono (winN_ok hL hA hp toJN_ok a1 w1.1 w1.2.1 w1.2.2 I₀ (by rcb_sub))
    fun s₁ ⟨k₁, U₁, E₁, I₁, _, v₁⟩ => ?_)
  have S₁ := hS.next hL I₁.scr (k₁.mono clob_combClob) U₁
  have J₁ : InvJ C (E₁ K.E.x) (E₁ K.E.y) (E₁ K.E.z) (mul e P) :=
    InvJ.of_toJ (z := tmv C K.M.n base s K.zero) hC hR (show toM _ _ _ = 0 by rw [hz]; exact toM_zero _ _)
      (v₁.trans (toJN_run _))
  -- Four doublings.
  refine WP.seq (WP.mono (winN_ok hL hA hp (dblJChoiceN_ok (K.M.n == 4)) a2 w2.1 w2.2.1 w2.2.2 I₁ (by rcb_sub))
    fun s₂ ⟨k₂, U₂, E₂, I₂, _, v₂⟩ => ?_)
  have S₂ := S₁.next hL I₂.scr (k₂.mono clob_combClob) U₂
  have J₂ := InvJ.dbl' hC hM3 (hQ e) J₁ (v₂.trans (dblJChoiceN_run (K.M.n == 4) _))
  rw [hC.double hP] at J₂
  refine WP.seq (WP.mono (winN_ok hL hA hp (dblJChoiceN_ok (K.M.n == 4)) a3 w3.1 w3.2.1 w3.2.2 I₂ (by rcb_sub))
    fun s₃ ⟨k₃, U₃, E₃, I₃, _, v₃⟩ => ?_)
  have S₃ := S₂.next hL I₃.scr (k₃.mono clob_combClob) U₃
  have J₃ := InvJ.dbl' hC hM3 (hQ _) J₂ (v₃.trans (dblJChoiceN_run (K.M.n == 4) _))
  rw [hC.double hP] at J₃
  refine WP.seq (WP.mono (winN_ok hL hA hp (dblJChoiceN_ok (K.M.n == 4)) a2 w2.1 w2.2.1 w2.2.2 I₃ (by rcb_sub))
    fun s₄ ⟨k₄, U₄, E₄, I₄, _, v₄⟩ => ?_)
  have S₄ := S₃.next hL I₄.scr (k₄.mono clob_combClob) U₄
  have J₄ := InvJ.dbl' hC hM3 (hQ _) J₃ (v₄.trans (dblJChoiceN_run (K.M.n == 4) _))
  rw [hC.double hP] at J₄
  refine WP.seq (WP.mono (winN_ok hL hA hp (dblJChoiceN_ok (K.M.n == 4)) a3 w3.1 w3.2.1 w3.2.2 I₄ (by rcb_sub))
    fun s₅ ⟨k₅, U₅, E₅, I₅, _, v₅⟩ => ?_)
  have S₅ := S₄.next hL I₅.scr (k₅.mono clob_combClob) U₅
  have J₅ := InvJ.dbl' hC hM3 (hQ _) J₄ (v₅.trans (dblJChoiceN_run (K.M.n == 4) _))
  rw [hC.double hP, show 2 * (2 * (2 * (2 * e))) = 16 * e by omega_using []] at J₅
  -- Back to projective coordinates, in `R`.
  refine WP.mono (winN_ok hL hA hp fromJN_ok a4 w4.1 w4.2.1 w4.2.2 I₅ (by rcb_sub))
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
  refine WP.mono (ld_ok hs (d := K.R.y + 8 * w) ho (by omega_using [ho8]) .x9) fun s₁ ⟨e₁, k₁, _⟩ => ?_
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
  refine WP.mono (st_out hs₄ (o := K.R.y + 8 * w) ho (by omega_using [ho8]) .x4) fun t ⟨m, kt, _⟩ => ⟨?_, ?_⟩
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
    refine WP.mono (ySelWords_ok hs K p hx2 ho8 k (by omega_using [hk])) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    refine WP.mono (ySelWord_ok hs₁ K p ((k₁.gpr _ (by decide)).trans hx2) (w := k) (by omega_using [hk]) ho8)
      fun s₂ ⟨m₂, k₂⟩ => ?_
    have O₂ : Outside base (K.R.y + 8 * k) 8 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega_using [hk, hn])
    refine ⟨fun j hj => ?_, k₁.trans k₂,
      (O₁.mono (Nat.le_refl _) (by omega_using [])).trans (O₂.mono (by omega_using []) (by omega_using []))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.word (by omega_using [h]) (by omega_using [hk, hn, h]), e₁ j h]
    · obtain rfl : j = k := by omega_using [hj, h]
      rw [m₂, word_writeW_self, O₁.word (by omega_using []) (by omega_using [hn, hk])]

/-- `R.y` = Montgomery's one where `E.z` is zero. -/
theorem ySel_ok {K : WinCfg} {base : Addr} {size : Nat} (hL : WinLay K size) (hA : WinA K)
    {s : State} (hs : Scr s base size) (h1 : K.one < 2 ^ (64 * K.M.n)) :
    WP isa (.block (WinCfg.ySel K)) s fun t =>
      wordsVal t.mem base K.R.y K.M.n = (if wordsVal s.mem base K.E.z K.M.n = 0 then K.one
        else wordsVal s.mem base K.R.y K.M.n) ∧
      KeepRegs [.x1, .x2, .x4, .x5, .x7, .x9, .x16] s t ∧
      Unch base [(K.R.y, 8 * K.M.n)] s.mem t.mem := by
  have hn := hs.nowrap
  have hy : K.R.y ∈ winSlots K := by win_in
  have hz : K.E.z ∈ winSlots K := by win_in
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
  have hRy : K.R.y ∈ winOther K := by win_in
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
    rcases hx with rfl | rfl | rfl <;> win_in)
  have eR : ∀ x ∈ [K.R.x, K.R.z], x ≠ K.R.y →
      wordsVal s₂.mem base x K.M.n = wordsVal s₁.mem base x K.M.n := by
    intro x hx hne
    have hxw : x ∈ winWs K := hws x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h <;> simp [h])
    refine U₂.wordsVal (fun w hw => ?_) (by have := hL.lay.le x (winWs_slots K x hxw); omega_using [hn, this])
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

end VG.Proof.Weierstrass.AArch64
