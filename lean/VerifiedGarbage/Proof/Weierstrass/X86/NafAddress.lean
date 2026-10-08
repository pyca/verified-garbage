import VerifiedGarbage.Proof.Weierstrass.X86.NafCopy
import VerifiedGarbage.Proof.Weierstrass.X86.TCombDigit

/-! Public addresses of the eight odd-multiple Jacobian table entries. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem nafAddress_ok {s : State} {base : Addr} {size tbl j : Nat}
    (hs : Scr s base size) (hj : s.gpr .eax=BitVec.ofNat 32 j)
    (ht : tbl+96*j<size) :
    WP isa (.block (Naf.tableAddress tbl)) s fun t =>
      (t.gpr .edx).setWidth 64=off base (tbl+96*j) ∧ CKeeps [.eax,.ecx,.edx] s t := by
  apply WP.of_runBlock
  simp only [Naf.tableAddress,runBlock_cons,runStep_some,runBlock_nil,exec,readSrc,
    execAlu,execMul,hj,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    RegUpd.gpr_setFlags,Option.map_some,Option.bind_some,ite_true,ite_false,reduceCtorEq,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · have hm : BitVec.ofNat 32 ((BitVec.ofNat 32 j).toNat*96)=BitVec.ofNat 32 (96*j) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_mul_mod,Nat.mul_comm j]
    change ((s.gpr .edi+BitVec.ofNat 32 tbl+
      BitVec.ofNat 32 ((BitVec.ofNat 32 j).toNat*96)).setWidth 64)=_
    rw [hm,Offset.add_add]
    exact hs.ea ht
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.gpr_setFlags,
      hr.1,hr.2.1,hr.2.2,ite_false]

theorem nafIndex_ok (s : State) {a : Nat} (ha : 1≤a) (ha' : a≤15)
    (hr : s.gpr .ebx=BitVec.ofNat 32 a) :
    WP isa (.block [.mov .eax (.reg .ebx),.alu .sub .eax (.imm 1),.shift .shr .eax 1]) s fun t =>
      t.gpr .eax=BitVec.ofNat 32 ((a-1)/2) ∧ CKeeps [.eax] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,readSrc,execAlu,execShift,
    Option.map_some,Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    RegUpd.gpr_setFlags,hr,ite_true,and_self,
    show 1≤1 ∧ 1≤31 from by decide,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r h => ?_,rfl,rfl,rfl⟩
  · change ((BitVec.ofNat 32 a-BitVec.ofNat 32 1)>>>1)=_
    rw [BitVec.ofNat_sub_ofNat_of_le a 1 (by decide) ha]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat]
    omega
  · simp only [List.mem_singleton] at h
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.gpr_setFlags,h,ite_false]

end VG.Proof.Weierstrass.X86
