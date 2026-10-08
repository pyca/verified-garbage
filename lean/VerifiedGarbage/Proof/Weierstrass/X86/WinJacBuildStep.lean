import VerifiedGarbage.Proof.Weierstrass.X86.WinJacBuildArith
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! The public counter and repeated table-construction step. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem inc_counter_ok {s : State} {m : Nat} (hc : s.gpr .esi=BitVec.ofNat 32 m) :
    WP isa (.block [.alu .add .esi (.imm 1)]) s fun t =>
      t.gpr .esi=BitVec.ofNat 32 (m+1) ∧ CKeeps [.esi] s t := by
  have he : BitVec.ofNat 32 m+(1 : BitVec 32)=BitVec.ofNat 32 (m+1) := by
    change BitVec.ofNat 32 m+BitVec.ofNat 32 1=_
    rw [BitVec.ofNat_add]
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    ite_true,hc,he,Option.some.injEq,exists_eq_left']
  refine ⟨trivial,fun r hr => ?_,rfl,rfl,rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]

theorem cmp_counter_ok {s : State} {m : Nat} (hm : m≤16) (hc : s.gpr .esi=BitVec.ofNat 32 m) :
    WP isa (.block [.alu .cmp .esi (.imm 16)]) s fun t =>
      t.zf=some (decide (m=16)) ∧ CKeeps [.esi] s t ∧ t.gpr .esi=BitVec.ofNat 32 m := by
  have he : (BitVec.ofNat 32 m-(16 : BitVec 32)==0)=decide (m=16) := by
    by_cases h : m=16
    · subst m; rfl
    · rw [decide_eq_false h,beq_eq_false_iff_ne]
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_sub,BitVec.toNat_ofNat] at this
      have h16 : (16 : BitVec 32).toNat=16 := rfl
      have h0 : (0 : BitVec 32).toNat=0 := rfl
      omega
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.bind_some,RegUpd.gpr_arithFlags,RegUpd.zf_arithFlags,hc,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun _ _ => rfl,rfl,rfl,rfl⟩,trivial⟩
  exact he

theorem build_step_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk m : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    (hn : 17≤C.n) {P : Point C} (hP : onCurve C P=true) (hP0 : P≠.infinity)
    (h2 : 2≤m) (h15 : m≤15) {s₀ s : State} (h : BuildInv K C base size wk P s₀ m s)
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p)
    (hJP : InvJ C (tmv C K.M.n base s₀ K.P.x) (tmv C K.M.n base s₀ K.P.y) 1 P) :
    WP isa K.buildStep s fun t => BuildInv K C base size wk P s₀ (m+1) t ∧
      t.zf=some (decide (m+1=16)) := by
  unfold JacWinCfg.buildStep
  apply WP.seq
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (inc_counter_ok h.counter) fun a ⟨ca,ka⟩ => ?_
  apply WP.mono (WP.seq_iff.mp (build_arith_ok hL hW hm hC ha hO hn hP hP0 h2 h15
    (h.frame.keeps ka) (fun m h1 hm => (h.table m h1 hm).congr fun _ _ => by rw [ka.2.1])
    (h.point.congr fun _ _ => by rw [ka.2.1]) hro hJP))
  intro b hb
  apply WP.seq
  apply WP.mono hb
  intro c ⟨pc,fc,tc,kc⟩
  rw [WP.block_append_iff]
  refine WP.mono (build_store_ok hL hW fc (by omega) ((kc.gpr _ (by decide)).trans ca) tc pc)
    fun d hd => ?_
  refine WP.mono (cmp_counter_ok (by omega) hd.counter) fun t ⟨zt,kt,ct⟩ => ?_
  refine ⟨⟨hd.frame.keeps kt,?_,?_,ct⟩,zt⟩
  · intro m h1 hm
    exact (hd.table m h1 hm).congr fun _ _ => by rw [kt.2.1]
  · exact hd.point.congr fun _ _ => by rw [kt.2.1]

end VG.Proof.Weierstrass.X86.JWin
