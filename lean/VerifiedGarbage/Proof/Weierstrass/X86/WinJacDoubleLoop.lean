import VerifiedGarbage.Proof.Weierstrass.X86.WinJacAccum

/-! Five doublings, with their public counter in the high bits of ESI. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem double_counter_ok {s : State} {j n : Nat} (hj : j<52) (h1 : 1≤n) (h5 : n≤5)
    (hc : s.gpr .esi=BitVec.ofNat 32 (j+4096*n)) :
    WP isa (.block [.alu .sub .esi (.imm 4096),.alu .cmp .esi (.imm 4096)]) s fun t =>
      t.gpr .esi=BitVec.ofNat 32 (j+4096*(n-1)) ∧ t.cf=some (decide (n=1)) ∧ CKeeps [.esi] s t := by
  have he : BitVec.ofNat 32 (j+4096*n)-(4096 : BitVec 32)=BitVec.ofNat 32 (j+4096*(n-1)) := by
    change BitVec.ofNat 32 (j+4096*n)-BitVec.ofNat 32 4096=_
    rw [BitVec.ofNat_sub_ofNat_of_le (j+4096*n) 4096 (by decide) (by omega)]
    exact congrArg (BitVec.ofNat 32) (show j+4096*n-4096=j+4096*(n-1) by omega)
  crun [hc,he,RegUpd.cf_arithFlags]
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · congr 1
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show j+4096*(n-1)<2^32 by omega)]
    have heq : j+4096*(n-1)<4096 ↔ n=1 := by omega
    change (j+4096*(n-1)<4096)=(n=1)
    exact propext heq
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]

theorem double_step_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k e j n : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    {P : Point C} (hP : onCurve C P=true) {s₀ s : State} (h : Accum K C base size wk P k s₀ e s)
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p)
    (hj : j<52) (h1 : 1≤n) (h5 : n≤5) (hc : s.gpr .esi=BitVec.ofNat 32 (j+4096*n)) :
    WP isa K.dblStep s fun t => Accum K C base size wk P k s₀ (2*e) t ∧
      t.gpr .esi=BitVec.ofNat 32 (j+4096*(n-1)) ∧ t.cf=some (decide (n=1)) := by
  unfold JacWinCfg.dblStep
  apply WP.seq
  refine WP.mono (double_accum_ok hL hW hm hC ha hP h hro) fun a ⟨ha,ka⟩ => ?_
  refine WP.mono (double_counter_ok hj h1 h5 ((ka.gpr _ (by decide)).trans hc))
    fun t ⟨ct,ft,kt⟩ => ⟨ha.keeps kt,ct,ft⟩

theorem double_init_counter_ok {s : State} {j : Nat} (hc : s.gpr .esi=BitVec.ofNat 32 j) :
    WP isa (.block [.alu .add .esi (.imm 20480)]) s fun t =>
      t.gpr .esi=BitVec.ofNat 32 (j+4096*5) ∧ CKeeps [.esi] s t := by
  have he : BitVec.ofNat 32 j+(20480 : BitVec 32)=BitVec.ofNat 32 (j+4096*5) := by
    rw [BitVec.ofNat_add]; rfl
  crun [hc,he]
  refine ⟨fun r hr => ?_,rfl,rfl,rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]

theorem doubles_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k e j : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    {P : Point C} (hP : onCurve C P=true) {s₀ s : State} (h : Accum K C base size wk P k s₀ e s)
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p)
    (hj : j<52) (hc : s.gpr .esi=BitVec.ofNat 32 j) :
    WP isa K.dbls s fun t => Accum K C base size wk P k s₀ (32*e) t ∧ t.gpr .esi=BitVec.ofNat 32 j := by
  unfold JacWinCfg.dbls
  apply WP.seq
  refine WP.mono (double_init_counter_ok hc) fun a ⟨ca,ka⟩ => ?_
  refine WP.loop (M:=isa)
    (fun n t => 1≤n ∧ n≤5 ∧ Accum K C base size wk P k s₀ (2^(5-n)*e) t ∧
      t.gpr .esi=BitVec.ofNat 32 (j+4096*n)) (fun n u ⟨h1,h5,hu,cu⟩ => ?_) 5 a
    ⟨by decide,by decide,by simpa using h.keeps ka,ca⟩
  refine WP.mono (double_step_ok hL hW hm hC ha hP hu hro hj h1 h5 cu) fun t ⟨ht,ct,ft⟩ => ?_
  by_cases he : n=1
  · subst n
    refine Or.inl ⟨?_,?_,?_⟩
    · change Option.map Bool.not t.cf=some false
      rw [ft]; rfl
    · simpa only [Nat.reduceSub,Nat.reducePow,←Nat.mul_assoc,Nat.reduceMul] using ht
    · simpa only [Nat.sub_self,Nat.mul_zero,Nat.add_zero] using ct
  · refine Or.inr ⟨?_,n-1,by omega,by omega,by omega,?_,ct⟩
    · change Option.map Bool.not t.cf=some true
      rw [ft,decide_eq_false he]; rfl
    · have hp : 5-(n-1)=(5-n)+1 := by omega
      simpa only [hp,Nat.pow_succ,Nat.mul_assoc,Nat.mul_left_comm] using ht

end VG.Proof.Weierstrass.X86.JWin
