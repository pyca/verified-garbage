import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.TableAddress

/-! The public table loop doubles entry j/2 or adds the peer to entry j-1. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Proof.Mont.X86_64 VG.Proof.Weierstrass.X86_64
open VG.Proof.X25519.X86_64

def tableParent (j : Nat) : Nat := if j%2=0 then j/2 else j-1

theorem tableParent_bounds {j : Nat} (h2 : 2≤j) (h16 : j≤16) :
    1≤tableParent j ∧ tableParent j<j := by
  unfold tableParent
  split <;> omega

theorem tableParity_ok (s : State) {j : Nat} (hj : s.gpr .rbx=BitVec.ofNat 64 j) (h16 : j≤16) :
    WP isa (.block [.mov .rax (.reg .rbx),.alu .test .rbx (.imm 1)]) s fun t =>
      t.gpr .rax=BitVec.ofNat 64 j ∧ t.zf=some (decide (j%2=0)) ∧ Keeps [.rax] s t := by
  have he : (BitVec.ofNat 64 j &&& 1=0) ↔ j%2=0 := by
    rw [←BitVec.toNat_inj]
    change (BitVec.ofNat 64 j).toNat &&& 1=0 ↔ j%2=0
    rw [Nat.and_one_is_mod,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : j<2^64)]
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.map_some,Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    RegUpd.zf_arithFlags,ite_true,ite_false,reduceCtorEq,hj,Option.some.injEq,exists_eq_left']
  refine ⟨trivial,?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · change decide (BitVec.ofNat 64 j &&& 1=0)=_
    simp only [he]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]

theorem tableParent_ok (s : State) {j : Nat} (h2 : 2≤j) (h16 : j≤16)
    (hj : s.gpr .rax=BitVec.ofNat 64 j) (hz : s.zf=some (decide (j%2=0))) :
    WP isa (.ite .e (.block [.shift .shr .rax 1]) (.block [.alu .sub .rax (.imm 1)])) s fun t =>
      t.gpr .rax=BitVec.ofNat 64 (tableParent j) ∧ Keeps [.rax] s t := by
  refine WP.ite (decide (j%2=0)) hz (fun hb => ?_) (fun hb => ?_)
  · have he := of_decide_eq_true hb
    simp only [tableParent,he,ite_true]
    apply WP.of_runBlock
    simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execShift,hj,
      RegUpd.gpr_setReg,RegUpd.gpr_setFlags,
      show 1≤1 ∧ 1≤63 from by decide,and_self,ite_true,Option.some.injEq,exists_eq_left']
    refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat]
      omega
    · simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_setReg,RegUpd.gpr_setFlags,hr,ite_false]
  · have he := of_decide_eq_false hb
    simp only [tableParent,he,ite_false]
    apply WP.of_runBlock
    simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,hj,
      Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
      ite_true,Option.some.injEq,exists_eq_left']
    refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
    · exact BitVec.ofNat_sub_ofNat_of_le j 1 (by decide) (by omega)
    · simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,hr,ite_false]

end VG.Proof.Ecdh.X86_64.Secret
