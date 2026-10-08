import VerifiedGarbage.Proof.P256.EcdhJac.Frame
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJDigit

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

/-- The high counter counts doublings, independently of the low window index. -/
theorem doubleCounter_ok (s : State) {q j : Nat} (hq : 1≤q) (hq5 : q≤5) (hj : j<52)
    (h19 : s.gpr .x19=BitVec.ofNat 64 (2048*q+j)) :
    WP isa (.block [.subImm .x .x19 .x19 2048,.lsr .x .x4 .x19 11]) s fun t =>
      t.gpr .x19=BitVec.ofNat 64 (2048*(q-1)+j) ∧ t.gpr .x4=BitVec.ofNat 64 (q-1) ∧
      Keeps [.x4,.x19] s t := by
  have he : BitVec.ofNat 64 (2048*q+j)-2048=BitVec.ofNat 64 (2048*(q-1)+j) := by
    have hn : 2048*q+j=2048*(q-1)+j+2048 := by omega
    change BitVec.ofNat 64 (2048*q+j)-BitVec.ofNat 64 2048=_
    rw [hn,←BitVec.ofNat_add_ofNat]
    exact BitVec.add_sub_cancel _ _
  have hs : (BitVec.ofNat 64 (2048*(q-1)+j) >>> 11)=BitVec.ofNat 64 (q-1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
    omega
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    show 2048<4096 by decide,show 11<64 by decide,ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,
    reduceCtorEq,ite_false,h19,Option.some.injEq,exists_eq_left']
  refine ⟨he,?_,fun r hr => ?_,rfl,rfl,rfl,rfl⟩
  · exact (congrArg (fun x : BitVec 64 => x >>> 11) he).trans hs
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]

theorem doubleCounter_start (s : State) {j : Nat} (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (.block [.movz .x .x4 10240 0,.add .x .x19 .x19 .x4]) s fun t =>
      t.gpr .x19=BitVec.ofNat 64 (2048*5+j) ∧ Keeps [.x4,.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    show 16*0<64 by decide,ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,
    reduceCtorEq,ite_false,h19,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl,rfl⟩
  · change BitVec.ofNat 64 j+BitVec.ofNat 64 10240=BitVec.ofNat 64 (2048*5+j)
    rw [BitVec.ofNat_add_ofNat,Nat.add_comm]
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]

theorem countRegLoop_ok (r : Reg) {body : Prog isa} {Inv : Nat → State → Prop} {Q : State → Prop} {n : Nat}
    (hn64 : n < 2 ^ 64)
    (hstep : ∀ j s, 1 ≤ j → j ≤ n → Inv j s →
      WP isa body s fun s' => Inv (j - 1) s' ∧ s'.gpr r = BitVec.ofNat 64 (j - 1))
    (hQ : ∀ s, Inv 0 s → Q s) (hn : 1 ≤ n) {s : State} (hs : Inv n s) :
    WP isa (.loop body (.nonzero .x r)) s Q := by
  refine WP.loop (M := isa) (fun j s => 1 ≤ j ∧ j ≤ n ∧ Inv j s) (fun j s ⟨h1, h2, hi⟩ => ?_) n s
    ⟨hn, Nat.le_refl _, hs⟩
  refine WP.mono (hstep j s h1 h2 hi) fun s' ⟨hi', hz⟩ => ?_
  have hx : (s'.read .x r != 0) = decide (j - 1 ≠ 0) := by
    rw [read_x, hz]
    by_cases hj : j - 1 = 0
    · rw [hj]; rfl
    · rw [decide_eq_true hj, bne_iff_ne, ne_eq]
      intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact hj this
  by_cases hj : j - 1 = 0
  · refine Or.inl ⟨?_, hQ s' (by rw [hj] at hi'; exact hi')⟩
    show some (s'.read .x r != 0) = some false
    rw [hx, hj]; rfl
  · refine Or.inr ⟨?_, j - 1, by omega, by omega, by omega, hi'⟩
    show some (s'.read .x r != 0) = some true
    rw [hx, decide_eq_true hj]

theorem RState.of_keeps {base : Addr} {P Q : Spec.Weierstrass.Point C} {k : Nat} {s t : State}
    {rs : List Reg} (h : RState base P Q k s) (hk : Keeps rs s t) (h0 : Reg.x0∉rs) :
    RState base P Q k t := by
  have hm : t.mem=s.mem := hk.mem
  refine ⟨?_,?_,?_,?_⟩
  · refine ⟨?_,?_,?_,?_,?_⟩
    · exact ⟨h.fixed.field.scr.of_keeps hk h0,hm ▸ h.fixed.field.mod,h.fixed.field.sl,
        by simpa only [hm] using h.fixed.field.lt,fun _ _ => rfl⟩
    · simpa only [hm] using h.fixed.zero
    · simpa only [tmv,hm] using h.fixed.peer
    · simpa only [tmv,hm] using h.fixed.one
    · simpa only [hm] using h.fixed.bits
  · intro a ha hb
    apply (h.table a ha hb).congr
    intro i hi
    rw [hm]
  · exact ⟨h.field.scr.of_keeps hk h0,hm ▸ h.field.mod,h.field.sl,
      by simpa only [hm] using h.field.lt,fun _ _ => rfl⟩
  · simpa only [tmv,hm] using h.point

end VG.Proof.P256.EcdhJac
