import VerifiedGarbage.Proof.Weierstrass.X86.WinJacAddStep
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacNeg
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacDoubleLoop

/-! One full signed-window iteration. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem dec_counter_ok {s : State} {j : Nat} (hc : s.gpr .esi=BitVec.ofNat 32 (j+1)) :
    WP isa (.block [.alu .sub .esi (.imm 1)]) s fun t =>
      t.gpr .esi=BitVec.ofNat 32 j ∧ CKeeps [.esi] s t := by
  have he : BitVec.ofNat 32 (j+1)-(1 : BitVec 32)=BitVec.ofNat 32 j := by
    rw [BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  crun [hc,he]
  refine ⟨fun r hr => ?_,rfl,rfl,rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]

theorem test_counter_ok {s : State} {j : Nat} (hj : j<52) (hc : s.gpr .esi=BitVec.ofNat 32 j) :
    WP isa (.block [.alu .test .esi (.reg .esi)]) s fun t =>
      t.zf=some (decide (j=0)) ∧ CKeeps [.esi] s t ∧ t.gpr .esi=BitVec.ofNat 32 j := by
  have he : (BitVec.ofNat 32 j==(0 : BitVec 32))=decide (j=0) := by
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq,decide_eq_true_eq]
    constructor
    · intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this
      have hz : (0 : BitVec 32).toNat=0 := rfl
      omega
    · intro h; subst j; rfl
  crun [hc,BitVec.and_self,RegUpd.zf_arithFlags,he]
  exact ⟨fun _ _ => rfl,rfl,rfl,rfl⟩

theorem step_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk k j : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {P : Point C} (hP : onCurve C P=true) (hP0 : P≠.infinity) (hn17 : C.n%32=17) (hn64 : 64≤C.n)
    {s₀ s : State} (h : Accum K C base size wk P k s₀
      (Window5.winE (k+16*Window5.geom K.J) K.J (j+1)) s)
    (hro : ∀ x∈ro K,wordsVal s₀.mem base x K.M.n<C.p)
    (hz : tmv C K.M.n base s₀ K.zero=0) (hj : j<K.J)
    (hc : s.gpr .esi=BitVec.ofNat 32 (j+1))
    (hb : ∀ i<260,s₀.mem (off base (K.bits+i))=if (k+16*Window5.geom K.J).testBit i then 1 else 0) :
    WP isa K.step s fun t => Accum K C base size wk P k s₀ (Window5.winE (k+16*Window5.geom K.J) K.J j) t ∧
      t.gpr .esi=BitVec.ofNat 32 j ∧ t.zf=some (decide (j=0)) := by
  have hj52 : j<52 := by have := hL.J; omega
  unfold JacWinCfg.step
  apply WP.seq
  refine WP.mono (dec_counter_ok hc) fun a ⟨ca,ka⟩ => ?_
  apply WP.seq
  refine WP.mono (doubles_ok hL hW hm hC ha hP (h.keeps ka) hro hj52 ca) fun b ⟨ab,cb⟩ => ?_
  apply WP.seq
  refine WP.mono (read_fields_ok hL hW ab.frame ab.table hj52 cb hb) fun c ⟨pc,kc,cc⟩ => ?_
  have ac := ab.preserve hL hW kc (coords_work K) (fun x hx hy => entry_apart_R hL x hx (List.mem_append_left _ hy))
  apply WP.seq
  refine WP.mono (neg_fields_ok hL hW hm ac.frame pc hro hz hj52 cc hb) fun d ⟨pd,kd,cd⟩ => ?_
  have nw : ∀ x∈[K.neg,K.E.y],x∈work K := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl <;> simp [work]
  have nr : ∀ x∈[K.R.x,K.R.y,K.R.z],x∉[K.neg,K.E.y] := by
    intro x hx hy
    apply entry_apart_R hL x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl|rfl <;> simp [coords]
  have ad := ac.preserve hL hW kd nw nr
  have pd : Entry K C base (Window5.winPt C P (k+16*Window5.geom K.J) j) d := by
    have ep := Window5.winPt_mag P (k+16*Window5.geom K.J) j
    simpa only [ep,decide_eq_true_eq] using pd
  apply WP.seq
  refine WP.mono (WP.seq_iff.mp (add_step_ok hL hW hm hC ha hO hP hP0 hn17 hn64 ad pd hro hj cd hb))
    fun u hu => ?_
  rw [WP.block_append_iff]
  refine WP.mono hu fun t ⟨acc_t,ct⟩ => ?_
  refine WP.mono (test_counter_ok hj52 ct) fun z ⟨fz,kz,cz⟩ => ⟨acc_t.keeps kz,cz,fz⟩

end VG.Proof.Weierstrass.X86.JWin
