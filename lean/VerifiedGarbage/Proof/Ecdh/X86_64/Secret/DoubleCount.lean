import VerifiedGarbage.Impl.Ecdh.P256.X86_64.Window5
import VerifiedGarbage.Proof.Weierstrass.X86_64.CounterKeep
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacZero

/-! The doubling loop borrows the upper bits of the public digit index for five iterations. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass.X86_64
open VG.Proof.X25519.X86_64

theorem doubles_start_ok (s : State) {j : Nat} (hc : s.gpr .rbx=BitVec.ofNat 64 j) :
    WP isa (.block [.alu .add .rbx (.imm (BitVec.ofNat 32 20480))]) s fun t =>
      t.gpr .rbx=BitVec.ofNat 64 (j+4096*5) ∧ Keeps [.rbx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,hc,ite_true,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · change BitVec.ofNat 64 j+BitVec.ofNat 64 20480=BitVec.ofNat 64 (j+20480)
    rw [BitVec.ofNat_add]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,hr,ite_false]

theorem doubles_tick_ok (s : State) {j m : Nat} (hj : j<4096) (hm1 : 1≤m) (hm5 : m≤5)
    (hc : s.gpr .rbx=BitVec.ofNat 64 (j+4096*m)) :
    WP isa (.block [.alu .sub .rbx (.imm 4096),.alu .cmp .rbx (.imm 4096)]) s fun t =>
      t.gpr .rbx=BitVec.ofNat 64 (j+4096*(m-1)) ∧
      t.cf=some (decide (m=1)) ∧ Keeps [.rbx] s t := by
  have he : BitVec.ofNat 64 (j+4096*m)-(4096 : BitVec 32).signExtend 64=
      BitVec.ofNat 64 (j+4096*(m-1)) := by
    change BitVec.ofNat 64 (j+4096*m)-BitVec.ofNat 64 4096=_
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.cf_arithFlags,
    hc,he,ite_true,Option.some.injEq,exists_eq_left']
  refine ⟨trivial,?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · change decide ((BitVec.ofNat 64 (j+4096*(m-1))).toNat<4096)=decide (m=1)
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq,BitVec.toNat_ofNat]
    omega
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,hr,ite_false]

end VG.Proof.Ecdh.X86_64.Secret
