import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.TableControl

/-! The scalar loop's public descending counter and zero flag. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Proof.Mont.X86_64 VG.Proof.Weierstrass.X86_64
open VG.Proof.X25519.X86_64

theorem scalar_prev_ok (s : State) {j : Nat} (hj : 1≤j)
    (hc : s.gpr .rbx=BitVec.ofNat 64 j) :
    WP isa (.block [.alu .sub .rbx (.imm 1)]) s fun t =>
      t.gpr .rbx=BitVec.ofNat 64 (j-1) ∧ Keeps [.rbx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,hc,ite_true,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · change BitVec.ofNat 64 j-BitVec.ofNat 64 1=BitVec.ofNat 64 (j-1)
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) hj]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,hr,ite_false]

theorem scalar_test_ok (s : State) {j : Nat} (hj : j<4096)
    (hc : s.gpr .rbx=BitVec.ofNat 64 j) :
    WP isa (.block [.alu .test .rbx (.reg .rbx)]) s fun t =>
      t.zf=some (decide (j=0)) ∧ Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.bind_some,RegUpd.zf_arithFlags,hc,BitVec.and_self,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r _ => congrFun (RegUpd.gpr_arithFlags ..) r,rfl,rfl,rfl⟩
  change decide (BitVec.ofNat 64 j=0)=decide (j=0)
  have he : BitVec.ofNat 64 j=0 ↔ j=0 := by
    rw [←BitVec.toNat_inj]
    change j%2^64=0 ↔ j=0
    omega
  simp only [he]

end VG.Proof.Ecdh.X86_64.Secret
