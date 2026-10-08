import VerifiedGarbage.Proof.Weierstrass.X86.WinJacFrame
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! Public counters used by the cached-point table loop. -/
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

end VG.Proof.Weierstrass.X86.JWin
