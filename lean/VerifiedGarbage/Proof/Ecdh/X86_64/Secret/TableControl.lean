import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.TableIndex

/-! The public parity flag and bounded counter of peer-table construction. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Proof.Mont.X86_64 VG.Proof.Weierstrass.X86_64
open VG.Proof.X25519.X86_64

theorem table_test_ok (s : State) {j : Nat} (hj : s.gpr .rbx=BitVec.ofNat 64 j) (h16 : j≤16) :
    WP isa (.block [.alu .test .rbx (.imm 1)]) s fun t =>
      t.zf=some (decide (j%2=0)) ∧ Keeps [] s t := by
  have he : (BitVec.ofNat 64 j &&& 1=0) ↔ j%2=0 := by
    rw [←BitVec.toNat_inj]
    change (BitVec.ofNat 64 j).toNat &&& 1=0 ↔ j%2=0
    rw [Nat.and_one_is_mod,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : j<2^64)]
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.bind_some,RegUpd.zf_arithFlags,hj,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r _ => congrFun (RegUpd.gpr_arithFlags ..) r,rfl,rfl,rfl⟩
  change decide (BitVec.ofNat 64 j &&& 1=0)=_
  simp only [he]

theorem table_advance_ok (s : State) {j : Nat} (hj : j≤16)
    (hc : s.gpr .rbx=BitVec.ofNat 64 j) :
    WP isa (.block [.alu .add .rbx (.imm 1),.alu .cmp .rbx (.imm 17)]) s fun t =>
      t.gpr .rbx=BitVec.ofNat 64 (j+1) ∧
      t.zf=some (decide (j+1=17)) ∧ Keeps [.rbx] s t := by
  have he : BitVec.ofNat 64 j+(1 : BitVec 32).signExtend 64=BitVec.ofNat 64 (j+1) := by
    change BitVec.ofNat 64 j+BitVec.ofNat 64 1=_
    rw [BitVec.ofNat_add]
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.zf_arithFlags,
    hc,he,ite_true,Option.some.injEq,exists_eq_left']
  refine ⟨trivial,?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · change decide (BitVec.ofNat 64 (j+1)-BitVec.ofNat 64 17=0)=decide (j+1=17)
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq,BitVec.sub_eq_iff_eq_add]
    change (BitVec.ofNat 64 (j+1)=BitVec.ofNat 64 17) ↔ j+1=17
    rw [←BitVec.toNat_inj]
    simp only [BitVec.toNat_ofNat]
    omega
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,hr,ite_false]

end VG.Proof.Ecdh.X86_64.Secret
