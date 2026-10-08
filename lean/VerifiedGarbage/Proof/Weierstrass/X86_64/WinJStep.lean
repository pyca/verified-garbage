import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJNorm

/-!
# Windows in Jacobian coordinates on x86-64: an iteration

`R = 16 R` in place in Jacobian coordinates (`quadJ_ok`: two pairs of
doublings between `R` and `D`), the masks of a point's `Z` being zero
(`zmask_ok`), and the mixed addition of the affine entry `E` into `D` with
the selection of `E`, `R` or `D` (`sumJ_ok`), for an iteration but the last
(`winStepJ_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

/-- `R = 16 R` in Jacobian coordinates, in place: from `(X : Y : Z)` standing
for `[e]P` (or with `Z = 0`) to a triple standing for `[16 e]P`. -/
theorem quadJ_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) {Rp : Fe C → Fe C → Fe C → Point C → Prop} {s₀ s : State}
    (hF : WinFixed K C base s₀ P k) (hS : WinStR K C base size Rp P s₀ s) {i : Nat} (hi : i < 4096)
    (hb : s.gpr .rbx = BitVec.ofNat 64 i) {e : Nat}
    (hlt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
      (mul e P)) :
    WP isa (WinCfg.quadJ K).inline s fun s' =>
      WinStR K C base size Rp P s₀ s' ∧ s'.gpr .rbx = s.gpr .rbx ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      InvJ C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (mul (16 * e) P) := by
  obtain ⟨-, -, ro_lt, -⟩ := hS.ro_tmv hL hF
  obtain ⟨aRD, aDR, -⟩ := hL.rcbApart_winJ
  have oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  have oD := pt_other (K := K) (p := K.D) (Or.inr (Or.inr rfl))
  have sl := fun (P : Pt) (h : ∀ x ∈ [P.x, P.y, P.z], x ∈ winOther K) x (hx : x ∈ [P.x, P.y, P.z]) =>
    winOther_mem (h x hx)
  have w2 := winJ_sl oD (sl _ oR) (sl _ oR)
  have w3 := winJ_sl oR (sl _ oD) (sl _ oD)
  let V := [K.R.x, K.R.y, K.R.z, K.S.a, K.S.b3, K.zero]
  have V0 : ∀ x ∈ V, x ∈ winSlots K ∧ wordsVal s.mem base x K.M.n < C.p := by
    intro x hx
    simp only [V, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨winOther_mem (oR _ (by simp)), hlt _ (by simp)⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hlt _ (by simp)⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hlt _ (by simp)⟩
    all_goals exact ⟨by win_mem, ro_lt _ (by simp [winRo])⟩
  have I₀ : Inv K.M base size C.p (· ∈ winSlots K) V (tmv C K.M.n base s) s :=
    ⟨hS.scr, hS.mod, fun x hx => (V0 x hx).1, fun x hx => (V0 x hx).2, fun _ _ => rfl⟩
  have hQ := fun (a : Nat) => hC.onCurve_mul hP a
  rw [WinCfg.quadJ]
  simp only [Code.inline]
  refine WP.seq (WP.mono (quadStart_ok s hb) fun s₂ ⟨b₂, kc₂⟩ => ?_)
  let LI := fun j st => WinStR K C base size Rp P s₀ st ∧
    st.gpr .rbx = BitVec.ofNat 64 (i + 4096 * j) ∧ ∃ E : Nat → Fe C,
    Inv K.M base size C.p (· ∈ winSlots K) V E st ∧
    InvJ C (E K.R.x) (E K.R.y) (E K.R.z) (mul (4 ^ (2 - j) * e) P)
  have start : LI 2 s₂ := ⟨hS.rbxKeeps hL kc₂, b₂, _, I₀.rbxKeeps kc₂, by simpa using hR⟩
  have body : ∀ j st, 1 ≤ j → j ≤ 2 → LI j st →
      WP isa (WinCfg.jacPairOn K K.R K.D).inline st fun st' => LI (j - 1) st' ∧ st'.cf = some (decide (j - 1 = 0)) := by
    intro j st hj hj' ⟨S, b, E, I, J⟩
    simp only [WinCfg.jacPairOn, WinCfg.double, dblJSChoice_eq]
    refine WP.seq (WP.mono (winN_ok hL hp (dblJSChoiceN_ok (K.M.n ≤ 6 : Bool)) aRD w2.1 w2.2 I (by
      intro x hx
      simp only [rcbR, V, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h | h | h | h | h | h <;> simp only [h, true_or, or_true]))
      fun st₁ ⟨k₁', U₁', E₁', I₁', _, v₁'⟩ => ?_)
    have S₁' := S.next hL I₁'.scr (k₁'.mono clob_powClob) U₁'
    have J₁' := InvJ.dbl' hC hM3 (hQ _) J (v₁'.trans (dblJSChoiceN_run (K.M.n ≤ 6 : Bool) _))
    rw [hC.double hP] at J₁'
    refine WP.seq (WP.mono (winN_ok hL hp (dblJSChoiceN_ok (K.M.n ≤ 6 : Bool)) aDR w3.1 w3.2 I₁' (by
      intro x hx
      simp only [rcbR, V, List.mem_cons, List.not_mem_nil, or_false, List.cons_append,
        List.nil_append] at hx ⊢
      rcases hx with h | h | h | h | h | h | h | h <;> simp only [h, true_or, or_true]))
      fun st₂ ⟨k₂', U₂', E₂', I₂', _, v₂'⟩ => ?_)
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
  refine WP.mono (quadLoop_ok body (fun _ h => h) start) fun s₅ ⟨S₅, b₅, E₅, I₅, J₅⟩ => ?_
  have rb₅ : s₅.gpr .rbx = s.gpr .rbx := by simpa only [Nat.mul_zero, Nat.add_zero, hb] using b₅
  have J₅ : InvJ C (E₅ K.R.x) (E₅ K.R.y) (E₅ K.R.z) (mul (16 * e) P) := by simpa using J₅
  have hRV : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ V := by
    intro x hx; simp only [V, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with h | h | h <;> simp [h]
  refine ⟨S₅, rb₅, fun x hx => I₅.lt x (hRV x hx), ?_⟩
  show InvJ C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
  rw [I₅.val _ (hRV _ (by simp)), I₅.val _ (hRV _ (by simp)), I₅.val _ (hRV _ (by simp))]
  exact J₅

/-! ## The mask of `Z = 0` -/

/-- The mask `rdx` of `[z] = 0`. -/
theorem zmask_ok (K : WinCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hn : 0 < K.M.n) {z : Nat} (ha : z + 8 * K.M.n ≤ size) :
    WP isa (.block (WinCfg.zmask K z)) s fun s' =>
      s'.gpr .rdx = mask (wordsVal s.mem base z K.M.n = 0) ∧ Keeps [.rdx] s s' := by
  rw [WinCfg.zmask, List.append_assoc, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov .rdx (.mem (sc z))]) s (fun s₁ =>
      s₁.gpr .rdx = word s.mem base z ∧ Keeps [.rdx] s s₁) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc_sc hs (d := z) (by omega),
      Option.map_some, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ors_ok hs₁ (a := z) (K.M.n - 1) (by omega)) fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [e₁, k₁.2.1] at e₂
  have hz : s₂.gpr .rdx = 0 ↔ wordsVal s.mem base z K.M.n = 0 := by
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

/-- `o = b` if `c`, in place: `selPt n o o b`, for `o`'s words apart from
each other and from `b`'s. -/
theorem selPtA_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (c : Bool)
    (hc : s.gpr .rcx = (if c then BitVec.allOnes 64 else 0)) {n : Nat} {o b : Pt}
    (hin : ∀ d ∈ [o.x, o.y, o.z, b.x, b.y, b.z], d + 8 * n ≤ size)
    (hoo : (o.x + 8 * n ≤ o.y ∨ o.y + 8 * n ≤ o.x) ∧ (o.x + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.x) ∧
      (o.y + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.y))
    (hab : ∀ d ∈ [o.x, o.y, o.z], ∀ e ∈ [b.x, b.y, b.z], d + 8 * n ≤ e ∨ e + 8 * n ≤ d) :
    WP isa (.block (selPt n o o b)) s fun s' =>
      wordsVal s'.mem base o.x n = (if c then wordsVal s.mem base b.x n else wordsVal s.mem base o.x n) ∧
      wordsVal s'.mem base o.y n = (if c then wordsVal s.mem base b.y n else wordsVal s.mem base o.y n) ∧
      wordsVal s'.mem base o.z n = (if c then wordsVal s.mem base b.z n else wordsVal s.mem base o.z n) ∧
      KeepRegs [.rax, .rdx] s s' ∧
      Unch base [(o.x, 8 * n), (o.y, 8 * n), (o.z, 8 * n)] s.mem s'.mem := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin hab
  obtain ⟨iox, ioy, ioz, iax, iay, iaz⟩ := hin
  obtain ⟨⟨xax, xay, xaz⟩, ⟨yax, yay, yaz⟩, ⟨zax, zay, zaz⟩⟩ := hab
  obtain ⟨xy, xz, yz⟩ := hoo
  rw [selPt, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sel_ok c n hs hc iox iox iax (Or.inl (Nat.le_refl _)) (by omega_using [xax]))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sel_ok c n hs₁ (by rw [k₁.gpr _ (by decide), hc]) ioy ioy iay (Or.inl (Nat.le_refl _))
    (by omega_using [yay])) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (sel_ok c n hs₂ (by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), hc]) ioz ioz iaz
    (Or.inl (Nat.le_refl _)) (by omega_using [zaz])) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  refine ⟨?_, ?_, ?_, (k₁.trans k₂).trans k₃, fun x hx => ?_⟩
  · rw [O₃.wordsVal (d := o.x) (by omega_using [xz]) (by omega_using [iox, hn]),
      O₂.wordsVal (d := o.x) (by omega_using [xy]) (by omega_using [iox, hn]), e₁]
  · rw [O₃.wordsVal (d := o.y) (by omega_using [yz]) (by omega_using [ioy, hn]), e₂,
      O₁.wordsVal (d := o.y) (by omega_using [xy]) (by omega_using [ioy, hn]),
      O₁.wordsVal (d := b.y) (by omega_using [xay]) (by omega_using [iay, hn])]
  · rw [e₃, O₂.wordsVal (d := o.z) (by omega_using [yz]) (by omega_using [ioz, hn]),
      O₂.wordsVal (d := b.z) (by omega_using [yaz]) (by omega_using [iaz, hn]),
      O₁.wordsVal (d := o.z) (by omega_using [xz]) (by omega_using [ioz, hn]),
      O₁.wordsVal (d := b.z) (by omega_using [xaz]) (by omega_using [iaz, hn])]
  · have h₁ := hx _ (List.mem_cons_self ..)
    have h₂ := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have h₃ := hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    rw [O₃ x h₃, O₂ x h₂, O₁ x h₁]

/-! ## The Jacobian sum, selected -/

/-- `rcx = rdx`. -/
theorem movRcxRdx_ok (s : State) :
    WP isa (.block [.mov .rcx (.reg .rdx)]) s fun t => t.gpr .rcx = s.gpr .rdx ∧ Keeps [.rcx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
    RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem toM_ite {m R : Nat} [NeZero m] (p : Prop) [Decidable p] (a b : Nat) :
    toM m R (if p then a else b) = if p then toM m R a else toM m R b := by
  split <;> rfl

/-- `R`, `E` and `D`: in the working space and apart, as the selection after
the sum needs. -/
theorem winRED_lay {K : WinCfg} {size : Nat} (hL : WinLay K size) :
    (∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z], x + 8 * K.M.n ≤ size) ∧
    ((K.D.x + 8 * K.M.n ≤ K.D.y ∨ K.D.y + 8 * K.M.n ≤ K.D.x) ∧
      (K.D.x + 8 * K.M.n ≤ K.D.z ∨ K.D.z + 8 * K.M.n ≤ K.D.x) ∧
      (K.D.y + 8 * K.M.n ≤ K.D.z ∨ K.D.z + 8 * K.M.n ≤ K.D.y)) ∧
    ((K.R.x + 8 * K.M.n ≤ K.R.y ∨ K.R.y + 8 * K.M.n ≤ K.R.x) ∧
      (K.R.x + 8 * K.M.n ≤ K.R.z ∨ K.R.z + 8 * K.M.n ≤ K.R.x) ∧
      (K.R.y + 8 * K.M.n ≤ K.R.z ∨ K.R.z + 8 * K.M.n ≤ K.R.y)) ∧
    (∀ d ∈ [K.D.x, K.D.y, K.D.z], ∀ e ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z],
      d + 8 * K.M.n ≤ e ∨ e + 8 * K.M.n ≤ d) ∧
    (∀ d ∈ [K.R.x, K.R.y, K.R.z], ∀ e ∈ [K.E.x, K.E.y, K.E.z], d + 8 * K.M.n ≤ e ∨ e + 8 * K.M.n ≤ d) := by
  have hnd := hL.nodup
  have hw : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z], x ∈ winWs K := by
    intro x hx
    refine winOther_ws K x ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h | h | h | h <;> subst h <;> win_mem
  have A : ∀ {x y}, x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z] →
      y ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z] → x ≠ y →
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := fun hx hy h => hL.apart₂ (hw _ hx) (hw _ hy) h
  simp only [winOther, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  have ne : ∀ {x y : Nat}, x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z] → x = y →
      (¬ x = y → False) := fun _ h h' => h' h
  clear ne
  refine ⟨fun x hx => hL.lay.le _ (winWs_slots K _ (hw _ hx)), ⟨A (by simp) (by simp) ?_,
    A (by simp) (by simp) ?_, A (by simp) (by simp) ?_⟩, ⟨A (by simp) (by simp) ?_,
    A (by simp) (by simp) ?_, A (by simp) (by simp) ?_⟩, ?_, ?_⟩
  rotate_left 6
  · intro d hd e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd he
    rcases hd with rfl | rfl | rfl <;> rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact A (by simp) (by simp) (by intro h; rw [h] at hnd; simp at hnd)
  · intro d hd e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd he
    rcases hd with rfl | rfl | rfl <;> rcases he with rfl | rfl | rfl <;>
      exact A (by simp) (by simp) (by intro h; rw [h] at hnd; simp at hnd)
  all_goals intro h; rw [h] at hnd; simp at hnd

/-- The value `selSum` leaves in a coordinate of `R`: `E`'s where `R` is
`O` (`Z = 0`), else `R`'s where `E` is `O`, else `D`'s. -/
def selVal (m : Mem) (base : Addr) (K : WinCfg) (r e d : Nat) : Nat :=
  if wordsVal m base K.R.z K.M.n = 0 then wordsVal m base e K.M.n
  else if wordsVal m base K.E.z K.M.n = 0 then wordsVal m base r K.M.n else wordsVal m base d K.M.n

/-- `D = R` where `E` is `O`, then `R = E` where `R` is `O`, else `D`. -/
theorem selSum_ok {K : WinCfg} {size : Nat} (hL : WinLay K size) {s : State} {base : Addr}
    (hs : Scr s base size) :
    WP isa (.block (WinCfg.selSum K)) s fun s' =>
      wordsVal s'.mem base K.R.x K.M.n = selVal s.mem base K K.R.x K.E.x K.D.x ∧
      wordsVal s'.mem base K.R.y K.M.n = selVal s.mem base K K.R.y K.E.y K.D.y ∧
      wordsVal s'.mem base K.R.z K.M.n = selVal s.mem base K K.R.z K.E.z K.D.z ∧
      KeepRegs [.rax, .rcx, .rdx] s s' ∧ Unch base (loopW K) s.mem s'.mem := by
  have hn := hs.nowrap
  obtain ⟨le, aD, aR, dRE, rE⟩ := winRED_lay hL
  have oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  have oD := pt_other (K := K) (p := K.D) (Or.inr (Or.inr rfl))
  rw [WinCfg.selSum]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zmask_ok K hs hL.n0 (le K.E.z (by simp))) fun s₂ ⟨m₂, k₂⟩ => ?_
  have hs₂ := hs.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (movRcxRdx_ok s₂) fun s₃ ⟨c₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have m₃ : s₃.mem = s.mem := by rw [k₃.2.1, k₂.2.1]
  rw [WP.block_append_iff]
  refine WP.mono (selPtA_ok hs₃ (decide (wordsVal s.mem base K.E.z K.M.n = 0))
    (by rw [c₃, m₂]; simp only [mask, decide_eq_true_eq]) (o := K.D) (b := K.R)
    (fun d hd => le d (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢; omega_using [hd]))
    aD (fun d hd e he => dRE d hd e (by simp only [List.mem_cons, List.not_mem_nil, or_false] at he ⊢; omega_using [he])))
    fun s₄ ⟨d4x, d4y, d4z, k₄, U₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  rw [m₃] at d4x d4y d4z U₄
  have keepD : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z],
      wordsVal s₄.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
    intro x hx
    refine U₄.wordsVal (fun w hw => ?_) (by have := le x (by simp at hx ⊢; omega_using [hx]); omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> dsimp only <;> exact (dRE _ (by simp) x hx).symm
  rw [WP.block_append_iff]
  refine WP.mono (zmask_ok K hs₄ hL.n0 (le K.R.z (by simp))) fun s₅ ⟨m₅, k₅⟩ => ?_
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (movRcxRdx_ok s₅) fun s₆ ⟨c₆, k₆⟩ => ?_
  have hs₆ := hs₅.of_keeps k₆ (by decide)
  have m₆ : s₆.mem = s₄.mem := by rw [k₆.2.1, k₅.2.1]
  refine WP.mono (selPt_ok hs₆ (decide (wordsVal s₄.mem base K.R.z K.M.n = 0))
    (by rw [c₆, m₅]; simp only [mask, decide_eq_true_eq]) (o := K.R) (a := K.D) (b := K.E)
    (fun d hd => le d (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢; omega_using [hd]))
    aR (fun d hd e he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (dRE _ (by simp) d (by simp at hd ⊢; omega_using [hd])).symm
      · exact (dRE _ (by simp) d (by simp at hd ⊢; omega_using [hd])).symm
      · exact (dRE _ (by simp) d (by simp at hd ⊢; omega_using [hd])).symm
      · exact rE d hd _ (by simp)
      · exact rE d hd _ (by simp)
      · exact rE d hd _ (by simp)))
    fun s₇ ⟨r7x, r7y, r7z, k₇, F₇⟩ => ?_
  rw [m₆] at r7x r7y r7z F₇
  have U₇ : Unch base [(K.R.x, 8 * K.M.n), (K.R.y, 8 * K.M.n), (K.R.z, 8 * K.M.n)] s₄.mem s₇.mem :=
    fun x hx => F₇ x (hx _ (List.mem_cons_self ..)) (hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
  have inL : ∀ {P : Pt}, (∀ x ∈ [P.x, P.y, P.z], x ∈ winOther K) →
      ∀ w ∈ [(P.x, 8 * K.M.n), (P.y, 8 * K.M.n), (P.z, 8 * K.M.n)], w ∈ loopW K := by
    intro P hP w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton]
    rcases hw with rfl | rfl | rfl
    · exact Or.inl ⟨_, hP _ (by simp), rfl⟩
    · exact Or.inl ⟨_, hP _ (by simp), rfl⟩
    · exact Or.inl ⟨_, hP _ (by simp), rfl⟩
  have rz : wordsVal s₄.mem base K.R.z K.M.n = wordsVal s.mem base K.R.z K.M.n := keepD _ (by simp)
  refine ⟨?_, ?_, ?_, ?_, (U₄.trans U₇).mono fun w hw => ?_⟩
  · rw [r7x, d4x, rz, keepD K.E.x (by simp), selVal]
    by_cases h1 : wordsVal s.mem base K.R.z K.M.n = 0 <;> simp [h1]
  · rw [r7y, d4y, rz, keepD K.E.y (by simp), selVal]
    by_cases h1 : wordsVal s.mem base K.R.z K.M.n = 0 <;> simp [h1]
  · rw [r7z, d4z, rz, keepD K.E.z (by simp), selVal]
    by_cases h1 : wordsVal s.mem base K.R.z K.M.n = 0 <;> simp [h1]
  · exact ((Keeps.regs k₂).mono (by decide)).trans (((Keeps.regs k₃).mono (by decide)).trans
      ((k₄.mono (by decide)).trans (((Keeps.regs k₅).mono (by decide)).trans
      (((Keeps.regs k₆).mono (by decide)).trans (k₇.mono (by decide))))))
  · rcases List.mem_append.mp hw with h | h
    · exact inL oD w h
    · exact inL oR w h

/-- `selVal` in the field. -/
theorem toM_selVal {C : Curve} {K : WinCfg} {m : Mem} {base : Addr} (hp : UnitMod C.p (2 ^ (64 * K.M.n)))
    {r e d : Nat} {Z1 Z2 a b c : Fe C}
    (hz1 : toM C.p (2 ^ (64 * K.M.n)) (wordsVal m base K.R.z K.M.n) = Z1)
    (hl1 : wordsVal m base K.R.z K.M.n < C.p)
    (hz2 : toM C.p (2 ^ (64 * K.M.n)) (wordsVal m base K.E.z K.M.n) = Z2)
    (hl2 : wordsVal m base K.E.z K.M.n < C.p)
    (ha : toM C.p (2 ^ (64 * K.M.n)) (wordsVal m base r K.M.n) = a)
    (hb : toM C.p (2 ^ (64 * K.M.n)) (wordsVal m base e K.M.n) = b)
    (hc : toM C.p (2 ^ (64 * K.M.n)) (wordsVal m base d K.M.n) = c) :
    toM C.p (2 ^ (64 * K.M.n)) (selVal m base K r e d) = if Z1 = 0 then b else if Z2 = 0 then a else c := by
  have i1 : wordsVal m base K.R.z K.M.n = 0 ↔ Z1 = 0 := by rw [← hz1]; exact (toM_eq_zero_iff hp hl1).symm
  have i2 : wordsVal m base K.E.z K.M.n = 0 ↔ Z2 = 0 := by rw [← hz2]; exact (toM_eq_zero_iff hp hl2).symm
  unfold selVal
  rw [toM_ite, toM_ite, ha, hb, hc]
  simp only [i1, i2]

/-- `R = R + E` for `R` in Jacobian coordinates and `E` affine (or `O`), by
the mixed addition into `D`, with `R = E` where `R` is `O` and `R` kept where
`E` is `O`: for `R` and `E` standing for points not equal unless one is `O`. -/
theorem sumJ_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    {Rp : Fe C → Fe C → Fe C → Point C → Prop} {s₀ s : State} (hF : WinFixed K C base s₀ P k)
    (hS : WinStR K C base size Rp P s₀ s) {QR QE : Point C} (hQR : onCurve C QR = true)
    (hQE : onCurve C QE = true)
    (hltR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hltE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z) QR)
    (hE : RepA C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z) QE)
    (hsep : QR ≠ .infinity → QE ≠ .infinity → QR ≠ QE) :
    WP isa (WinCfg.sumJ K).inline s fun s' =>
      WinStR K C base size Rp P s₀ s' ∧ s'.gpr .rbx = s.gpr .rbx ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      InvJ C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (Spec.Weierstrass.add QR QE) := by
  obtain ⟨-, -, ro_lt, -⟩ := hS.ro_tmv hL hF
  have oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  have oE := pt_other (K := K) (p := K.E) (Or.inr (Or.inl rfl))
  have oD := pt_other (K := K) (p := K.D) (Or.inr (Or.inr rfl))
  have sl := fun (P : Pt) (h : ∀ x ∈ [P.x, P.y, P.z], x ∈ winOther K) x (hx : x ∈ [P.x, P.y, P.z]) =>
    winOther_mem (h x hx)
  have w1 := winJ_sl oD (sl _ oR) (sl _ oE)
  have V0 : ∀ x ∈ rcbR K.S K.R K.E, x ∈ winSlots K ∧ wordsVal s.mem base x K.M.n < C.p := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by win_mem, ro_lt _ (by simp [winRo])⟩
    · exact ⟨by win_mem, ro_lt _ (by simp [winRo])⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hltR _ (by simp)⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hltR _ (by simp)⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hltR _ (by simp)⟩
    · exact ⟨winOther_mem (oE _ (by simp)), hltE _ (by simp)⟩
    · exact ⟨winOther_mem (oE _ (by simp)), hltE _ (by simp)⟩
    · exact ⟨winOther_mem (oE _ (by simp)), hltE _ (by simp)⟩
  have I₀ : Inv K.M base size C.p (· ∈ winSlots K) (rcbR K.S K.R K.E) (tmv C K.M.n base s) s :=
    ⟨hS.scr, hS.mod, fun x hx => (V0 x hx).1, fun x hx => (V0 x hx).2, fun _ _ => rfl⟩
  rw [WinCfg.sumJ, maddJ_eq]
  simp only [Code.inline]
  refine WP.seq (WP.mono (winN_ok hL hp maddJN_ok (hL.rcbApart_D (Or.inr rfl)) w1.1 w1.2 I₀
    (fun x hx => hx)) fun s₁ ⟨k₁, U₁, E₁, I₁, o₁, v₁⟩ => ?_)
  have S₁ := hS.next hL I₁.scr (k₁.mono clob_powClob) U₁
  -- `R` and `E` kept, `D` the sum.
  obtain ⟨-, -, -, hRo, -, -, -, hEo, -, -⟩ := hL.other_ne
  have nD : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z], x ∉ rcbW K.S K.D := by
    intro x hx h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    have h1 : ∀ y ∈ [K.R.x, K.R.y, K.R.z], y ∉ rcbW K.S K.D := fun y hy h =>
      hRo y hy (List.mem_append_right _ h)
    have h2 : ∀ y ∈ [K.E.x, K.E.y, K.E.z], y ∉ rcbW K.S K.D := fun y hy h =>
      hEo y hy (List.mem_cons_of_mem _ h)
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1 _ (by simp) h
    · exact h1 _ (by simp) h
    · exact h1 _ (by simp) h
    · exact h2 _ (by simp) h
    · exact h2 _ (by simp) h
    · exact h2 _ (by simp) h
  have inV : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z],
      x ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.R K.E := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append] at hx ⊢
    rcases hx with h | h | h | h | h | h | h | h | h <;> simp [h]
  have v₁' : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z],
      toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₁.mem base x K.M.n) = tmv C K.M.n base s x := fun x hx => by
    rw [I₁.val x (inV x (by simp at hx ⊢; omega_using [hx])), o₁ x (nD x hx)]
  have lt₁ : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z],
      wordsVal s₁.mem base x K.M.n < C.p := fun x hx => I₁.lt x (inV x hx)
  have vD : (toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₁.mem base K.D.x K.M.n),
      toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₁.mem base K.D.y K.M.n),
      toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₁.mem base K.D.z K.M.n)) =
      maddJF (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
        (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) := by
    refine Eq.trans ?_ (v₁.trans (maddJN_run _))
    rw [I₁.val _ (inV _ (by simp)), I₁.val _ (inV _ (by simp)), I₁.val _ (inV _ (by simp))]
  have jx := congrArg Prod.fst vD
  have jy := congrArg (fun t => t.2.1) vD
  have jz := congrArg (fun t => t.2.2) vD
  dsimp only at jx jy jz
  refine WP.mono (selSum_ok hL I₁.scr) fun s₂ ⟨r2x, r2y, r2z, k₂, U₂⟩ => ?_
  have c : ∀ r ∈ [Reg.rax, .rcx, .rdx], r ∈ powClob K.M.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [powClob, clob]
  have S₂ := S₁.next hL (I₁.scr.of_keepRegs k₂ (by decide)) (k₂.mono c) U₂
  have tz1 := v₁' K.R.z (by simp)
  have tz2 := v₁' K.E.z (by simp)
  have l1 := lt₁ K.R.z (by simp)
  have l2 := lt₁ K.E.z (by simp)
  refine ⟨S₂, by rw [k₂.gpr _ (by decide), k₁.gpr _ (rbx_not_clob _)], fun x hx => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [r2x, selVal]; split
      · exact lt₁ _ (by simp)
      · split <;> exact lt₁ _ (by simp)
    · rw [r2y, selVal]; split
      · exact lt₁ _ (by simp)
      · split <;> exact lt₁ _ (by simp)
    · rw [r2z, selVal]; split
      · exact lt₁ _ (by simp)
      · split <;> exact lt₁ _ (by simp)
  · show InvJ C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [r2x, r2y, r2z, toM_selVal hp tz1 l1 tz2 l2 (v₁' _ (by simp)) (v₁' _ (by simp)) jx,
      toM_selVal hp tz1 l1 tz2 l2 (v₁' _ (by simp)) (v₁' _ (by simp)) jy,
      toM_selVal hp tz1 l1 tz2 l2 (v₁' _ (by simp)) (v₁' _ (by simp)) jz]
    exact InvJ.sumSelM hC hM3 hQR hQE hR hE hsep

/-! ## An iteration but the last -/

/-- The Jacobian loop's invariant at `rbx = j`: `R` stands for `[winE k J j]P`
in Jacobian coordinates, the table affine. -/
structure WinInvJ (K : WinCfg) (C : Curve) (base : Addr) (size k : Nat) (P : Point C) (s₀ s : State)
    (j : Nat) : Prop where
  st : WinStR K C base size (RepA C) P s₀ s
  rbx : s.gpr .rbx = BitVec.ofNat 64 j
  lt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p
  rep : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
    (mul (winE k K.J j) P)

/-- What the entry's selection writes is in `loopW`. -/
theorem entryW_loopW (K : WinCfg) : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n),
    (K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)], w ∈ loopW K := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton]
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨_, winE_mem _ (by simp), rfl⟩
  · exact Or.inl ⟨_, winE_mem _ (by simp), rfl⟩
  · exact Or.inl ⟨_, winE_mem _ (by simp), rfl⟩
  · exact Or.inl ⟨_, winE_mem _ (by simp), rfl⟩
  · exact Or.inr rfl

/-- `R` is apart from what the entry's selection writes. -/
theorem R_apart_entry {K : WinCfg} {size : Nat} (hL : WinLay K size) {x : Nat}
    (hx : x ∈ [K.R.x, K.R.y, K.R.z]) :
    ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n), (K.neg, 8 * K.M.n),
      (K.M.tmp, 8 * K.M.n)], x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  obtain ⟨-, -, -, hRo, -⟩ := hL.other_ne
  have hxw : x ∈ winWs K := winOther_ws K x (pt_other (K := K) (p := K.R) (Or.inl rfl) x hx)
  intro w hw
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

/-- An iteration but the last, `rbx = j ≥ 2` to `j - 1`: adds digit `j - 1`. -/
theorem winStepJ_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hX : WinX K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true) (hP0 : P ≠ .infinity)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s₀ : State} (hF : WinFixed K C base s₀ P k)
    (hk8 : 8 * geom K.J ≤ k) {j : Nat} (hj : 2 ≤ j) (hjn : j ≤ K.J)
    (hb : 16 * winE k K.J j + 8 < C.n) {s : State} (hI : WinInvJ K C base size k P s₀ s j) :
    WP isa (WinCfg.stepJ K).inline s fun s' =>
      WinInvJ K C base size k P s₀ s' (j - 1) ∧ s'.zf = some (decide (j - 1 = 1)) := by
  have hJ := hL.J
  rw [WinCfg.stepJ]
  simp only [Code.inline]
  refine WP.seq (WP.mono (decRbx_ok s (by omega) (by omega) hI.rbx) fun s₁ ⟨b₁, k₁⟩ => ?_)
  have hS₁ := hI.st.rbxKeeps hL k₁
  have lt₁ : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₁.mem base x K.M.n < C.p := by
    rw [k₁.2.1]; exact hI.lt
  have rep₁ : InvJ C (tmv C K.M.n base s₁ K.R.x) (tmv C K.M.n base s₁ K.R.y)
      (tmv C K.M.n base s₁ K.R.z) (mul (winE k K.J j) P) := by
    have e : ∀ x, tmv C K.M.n base s₁ x = tmv C K.M.n base s x := fun x => by
      show toM _ _ _ = toM _ _ _; rw [k₁.2.1]
    rw [e, e, e]; exact hI.rep
  refine WP.seq (WP.mono (quadJ_ok hL hp hC hM3 hP hF hS₁ (i := j - 1) (by omega) b₁ lt₁ rep₁)
    fun s₅ ⟨S₅, x₅, l₅, r₅⟩ => ?_)
  have hx₅ : s₅.gpr .rbx = BitVec.ofNat 64 (j - 1) := by rw [x₅, b₁]
  obtain ⟨-, -, -, hz₅⟩ := S₅.ro_tmv hL hF
  have hbits₅ : ∀ t < 4 * K.J, s₅.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by
      have := hL.bits
      rw [S₅.unch.byte (fun w hw => by have := hL.bits_w w hw; omega) (by have := S₅.scr.nowrap; omega)]
      exact hF.bits t ht
  refine WP.seq (WP.mono (winEntryR_ok hL hX (RepA.infinity hC) RepA.negY (P := P) hpn hone_lt hone
    S₅.scr S₅.mod (i := j - 1) (by omega) hx₅ hbits₅ hz₅ S₅.tbl) fun s₆ h₆ => WP.seq (WP.mono h₆
      fun s₇ E₇ => ?_))
  have hn := S₅.scr.nowrap
  have S₇ := S₅.next hL E₇.scr (E₇.keep.mono clob_powClob) (E₇.unch.mono (entryW_loopW K))
  have eR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₇.mem base x K.M.n = wordsVal s₅.mem base x K.M.n :=
    fun x hx => E₇.unch.wordsVal (R_apart_entry hL hx) (by
      have := hL.lay.le x (winOther_mem (pt_other (K := K) (p := K.R) (Or.inl rfl) x hx)); omega)
  have lt₇ : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₇.mem base x K.M.n < C.p := fun x hx => by
    rw [eR x hx]; exact l₅ x hx
  have rep₇ : InvJ C (tmv C K.M.n base s₇ K.R.x) (tmv C K.M.n base s₇ K.R.y)
      (tmv C K.M.n base s₇ K.R.z) (mul (16 * winE k K.J j) P) := by
    have e : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base s₇ x = tmv C K.M.n base s₅ x := fun x hx => by
      show toM _ _ _ = toM _ _ _; rw [eR x hx]
    rw [e _ (by simp), e _ (by simp), e _ (by simp)]; exact r₅
  have hsep := win_sep hC hO hP hP0 (k := k) (J := K.J) (j := j - 1)
    (by rw [Nat.sub_add_cancel (by omega : 1 ≤ j)]; exact hb)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ j)] at hsep
  refine WP.seq (WP.mono (sumJ_ok hL hp hC hM3 hF S₇ (hC.onCurve_mul hP _)
    (onCurve_winPt hC hP k (j - 1)) lt₇ E₇.lt rep₇ E₇.rep (fun h1 _ => (hsep h1).1))
    fun s₈ ⟨S₈, x₈, l₈, r₈⟩ => ?_)
  have hadd := win_add hC hP (k := k) (J := K.J) (j := j - 1) hk8 (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ j)] at hadd
  rw [hadd] at r₈
  have hx₇ : s₇.gpr .rbx = BitVec.ofNat 64 (j - 1) := by rw [E₇.keep.gpr _ (rbx_not_clob _), hx₅]
  have hx₈ : s₈.gpr .rbx = BitVec.ofNat 64 (j - 1) := by rw [x₈, hx₇]
  refine WP.mono (cmpRbx_ok s₈ (j := j - 1) (i := 1) (by decide) (by omega) hx₈) fun s₉ ⟨z₉, k₉⟩ => ⟨?_, z₉⟩
  refine ⟨S₈.rbxKeeps hL ((Keeps.mono k₉ (fun _ h => absurd h List.not_mem_nil))), by rw [k₉.1 _ (by simp), hx₈],
    by rw [k₉.2.1]; exact l₈, ?_⟩
  have e : ∀ x, tmv C K.M.n base s₉ x = tmv C K.M.n base s₈ x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [k₉.2.1]
  rw [e, e, e]; exact r₈

end VG.Proof.Weierstrass.X86_64
