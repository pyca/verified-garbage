import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState

/-! Zero tests for canonical field elements used by public Jacobian branches. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64
open VG.Impl.Weierstrass VG.Proof.Mont.X86_64 VG.Proof.Mont
open VG.Proof.X25519.X86_64 (Keeps)

theorem zeroTest_ok {s : State} {base : Addr} {size n a : Nat}
    (hs : Scr s base size) (hn : 0 < n) (ha : a + 8*n ≤ size) :
    WP isa (.block (Jacobian.zeroTest n a)) s fun t =>
      t.zf = some (decide (wordsVal s.mem base a n = 0)) ∧ Keeps [.rdx] s t := by
  rw [Jacobian.zeroTest, List.append_assoc, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov .rdx (.mem (sc a))]) s (fun t =>
      t.gpr .rdx = word s.mem base a ∧ Keeps [.rdx] s t) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc_sc hs (d := a) (by omega),
      Option.map_some, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ors_ok hs₁ (a := a) (n-1) (by omega)) fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [e₁, k₁.2.1] at e₂
  have hz : s₂.gpr .rdx = 0 ↔ wordsVal s.mem base a n = 0 := by
    rw [e₂, wordsVal_eq_zero_iff]
    constructor
    · intro ⟨h₀,h⟩ j hj
      cases j with
      | zero => simpa using h₀
      | succ j => exact h j (by omega)
    · intro h
      exact ⟨by simpa using h 0 hn, fun j hj => h (j+1) (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, BitVec.and_self, RegUpd.zf_arithFlags, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [Bool.eq_iff_iff]
    simpa only [beq_iff_eq, decide_eq_true_eq] using hz
  · rw [RegUpd.gpr_arithFlags, k₂.1 r hr, k₁.1 r hr]
  · rw [RegUpd.mem_arithFlags, k₂.2.1, k₁.2.1]
  · rw [RegUpd.rd_arithFlags, k₂.2.2.1, k₁.2.2.1]
  · rw [RegUpd.wr_arithFlags, k₂.2.2.2, k₁.2.2.2]

theorem Inv.of_keeps {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m} {s t : State} {rs : List Reg}
    (h : Inv M base size m Sl V E s) (hk : Keeps rs s t) (h0 : Reg.rdi ∉ rs) :
    Inv M base size m Sl V E t :=
  ⟨h.scr.of_keeps hk h0,hk.2.1 ▸ h.mod,h.sl,hk.2.1 ▸ h.lt,hk.2.1 ▸ h.val⟩

theorem zeroField_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2^(64*M.n))) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {a : Nat} (ha : a ∈ V) :
    WP isa (.block (Jacobian.zeroTest M.n a)) s fun t =>
      t.zf = some (decide (E a = 0)) ∧ Inv M base size m Sl V E t ∧
      ProgKeep M base [] s t := by
  refine WP.mono (zeroTest_ok hI.scr hI.mod.n0 (hL.le a (hI.sl a ha)))
    fun t ⟨hz,hk⟩ => ⟨?_,hI.of_keeps hk (by decide),?_⟩
  · have he := toM_eq_zero_iff hm (hI.lt a ha)
    rw [hI.val a ha] at he
    rw [hz]
    simp only [he]
  · refine ⟨fun r hr => hk.1 r ?_,hk.2.2.1,hk.2.2.2,fun _ _ _ => congrFun hk.2.1 _⟩
    intro h
    rw [List.mem_singleton] at h
    subst r
    exact hr (by simp [clob])

theorem fieldBranch_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2^(64*M.n))) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {a : Nat} (ha : a ∈ V)
    {yes no : Prog isa} {Q : State → Prop}
    (hy : ∀ t, Inv M base size m Sl V E t → ProgKeep M base [] s t → E a = 0 → WP isa yes t Q)
    (hn : ∀ t, Inv M base size m Sl V E t → ProgKeep M base [] s t → E a ≠ 0 → WP isa no t Q) :
    WP isa (.seq (.block (Jacobian.zeroTest M.n a)) (.ite .e yes no)) s Q := by
  refine WP.seq (WP.mono (zeroField_ok hL hm hI ha) fun t ⟨he,hi,hk⟩ => ?_)
  exact WP.ite (decide (E a = 0)) he
    (fun hz => hy t hi hk (of_decide_eq_true hz))
    (fun hz => hn t hi hk (of_decide_eq_false hz))
end VG.Proof.Weierstrass.X86_64
