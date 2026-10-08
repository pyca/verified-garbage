import VerifiedGarbage.Proof.Weierstrass.X86.JacState
import VerifiedGarbage.Proof.Weierstrass.X86.WinFlags

/-! Zero tests for canonical field elements used by public Jacobian branches. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86
open VG.Impl.Weierstrass VG.Proof.Mont.X86 VG.Proof.Mont

theorem zeroTest_ok {s : State} {base : Addr} {size n a : Nat}
    (hs : Scr s base size) (hn : 0 < n) (ha : a + 8*n ≤ size) :
    WP isa (.block (Jacobian.zeroTest n a)) s fun t =>
      t.zf = some (decide (wordsVal s.mem base a n = 0)) ∧ CKeeps [.edx] s t := by
  simp only [Jacobian.zeroTest, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc hs (d := a) (by omega)) fun s₁ u₁ _ => ?_
  refine WP.block_append (WP.mono (winOrs_ok (hs.of_keeps u₁.keeps (by decide)) (2*n-1) (by omega))
    fun s₂ ⟨e₂,k₂,m₂⟩ => ?_)
  rw [u₁.gpr, u₁.mem] at e₂
  have hz : s₂.gpr .edx = 0 ↔ wordsVal s.mem base a n = 0 := by
    rw [e₂, wordsVal_eq_val32, val32_eq_zero_iff]
    have hw : s.mem.readW (off base a) 32 = 0 ↔ w32 s.mem base a = 0 :=
      ⟨fun h => by simp [w32,h], fun h => BitVec.eq_of_toNat_eq h⟩
    rw [hw]
    constructor
    · intro ⟨h₀,h⟩ j hj
      cases j with
      | zero => simpa using h₀
      | succ j => exact h j (by omega)
    · intro h
      exact ⟨by simpa using h 0 (by omega), fun j hj => h (j+1) (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, BitVec.and_self, RegUpd.zf_arithFlags, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [Bool.eq_iff_iff]
    simpa only [beq_iff_eq, decide_eq_true_eq] using hz
  · rw [RegUpd.gpr_arithFlags, k₂.1 r hr, u₁.other r (by simpa using hr)]
  · rw [RegUpd.mem_arithFlags, m₂, u₁.mem]
  · rw [RegUpd.rd_arithFlags, k₂.2.1, u₁.rd]
  · rw [RegUpd.wr_arithFlags, k₂.2.2, u₁.wr]

theorem Inv.of_keeps {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m} {s t : State} {rs : List Reg}
    (h : Inv M base size m Sl V E s) (hk : CKeeps rs s t) (h0 : Reg.edi ∉ rs) (hsp : Reg.esp∉rs := by decide) :
    Inv M base size m Sl V E t :=
  ⟨h.scr.of_keeps hk.keeps h0 hsp,hk.2.1 ▸ h.mod,h.sl,hk.2.1 ▸ h.lt,hk.2.1 ▸ h.val⟩

theorem zeroField_ok {M : Mod} {base : Addr} {size m wk : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2^(64*M.n))) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {a : Nat} (ha : a ∈ V) :
    WP isa (.block (Jacobian.zeroTest M.n a)) s fun t =>
      t.zf = some (decide (E a = 0)) ∧ Inv M base size m Sl V E t ∧
      ProgKeep M base wk [] s t := by
  refine WP.mono (zeroTest_ok hI.scr hI.mod.n0 (hL.le a (hI.sl a ha)))
    fun t ⟨hz,hk⟩ => ⟨?_,hI.of_keeps hk (by decide),?_⟩
  · have he := toM_eq_zero_iff hm (hI.lt a ha)
    rw [hI.val a ha] at he
    rw [hz]
    simp only [he]
  · refine ⟨fun r hr => hk.1 r ?_,hk.2.2.1,hk.2.2.2,fun _ _ => congrFun hk.2.1 _⟩
    intro h
    rw [List.mem_singleton] at h
    subst r
    exact hr (by simp [clob])

theorem fieldBranch_ok {M : Mod} {base : Addr} {size m wk : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2^(64*M.n))) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {a : Nat} (ha : a ∈ V)
    {yes no : Prog isa} {Q : State → Prop}
    (hy : ∀ t, Inv M base size m Sl V E t → ProgKeep M base wk [] s t → E a = 0 → WP isa yes t Q)
    (hn : ∀ t, Inv M base size m Sl V E t → ProgKeep M base wk [] s t → E a ≠ 0 → WP isa no t Q) :
    WP isa (.seq (.block (Jacobian.zeroTest M.n a)) (.ite .e yes no)) s Q := by
  refine WP.seq (WP.mono (zeroField_ok (wk := wk) hL hm hI ha) fun t ⟨he,hi,hk⟩ => ?_)
  exact WP.ite (decide (E a = 0)) he
    (fun hz => hy t hi hk (of_decide_eq_true hz))
    (fun hz => hn t hi hk (of_decide_eq_false hz))
end VG.Proof.Weierstrass.X86
