import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCopy
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafDigitRead

/-! Bounds and addresses of the eight public odd-multiple table entries. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.X25519.X86_64

theorem nafAddress_ok (s : State) {base : Addr} {n tbl j : Nat}
    (hb : s.gpr .rdi=base) (hj : s.gpr .rax=BitVec.ofNat 64 j) (ht : tbl<2^31) (hn : 24*n<2^32) :
    WP isa (.block (Naf.tableAddress n tbl)) s fun t =>
      t.gpr .rdx=off base (tbl+24*n*j) ∧ Keeps [.rax,.rcx,.rdx] s t := by
  apply WP.of_runBlock
  simp only [Naf.tableAddress,runBlock_cons,runStep_some,runBlock_nil,exec,readSrc,readSrc32,
    execAlu,execMul,State.setReg32,imm32_sext ht,hj,hb,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    RegUpd.gpr_setFlags,Option.map_some,Option.bind_some,ite_true,ite_false,reduceCtorEq,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · have hm : BitVec.ofNat 64 ((BitVec.ofNat 64 j).toNat*((BitVec.ofNat 32 (24*n)).setWidth 64).toNat)=
        BitVec.ofNat 64 (24*n*j) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat,BitVec.toNat_setWidth,Nat.mod_eq_of_lt hn]
      rw [Nat.mod_mul_mod,Nat.mul_comm j,Nat.mod_eq_of_lt (show 24*n<2^64 by omega)]
    change base+BitVec.ofNat 64 tbl+BitVec.ofNat 64 ((BitVec.ofNat 64 j).toNat*
      ((BitVec.ofNat 32 (24*n)).setWidth 64).toNat)=_
    rw [hm,Offset.add_add]
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.gpr_setFlags,
      hr.1,hr.2.1,hr.2.2,ite_false]

theorem nafIndex_ok (s : State) {a : Nat} (ha : 1≤a) (ha' : a≤15)
    (hr : s.gpr .r8=BitVec.ofNat 64 a) :
    WP isa (.block [.mov .rax (.reg .r8),.alu .sub .rax (.imm 1),.shift .shr .rax 1]) s fun t =>
      t.gpr .rax=BitVec.ofNat 64 ((a-1)/2) ∧ Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,readSrc,execAlu,execShift,
    Option.map_some,Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    RegUpd.gpr_setFlags,hr,ite_true,and_self,
    show 1≤1 ∧ 1≤63 from by decide,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r h => ?_,rfl,rfl,rfl⟩
  · rw [show (1 : BitVec 32).signExtend 64=BitVec.ofNat 64 1 from by decide,
      BitVec.ofNat_sub_ofNat_of_le a 1 (by decide) ha]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat]
    omega
  · simp only [List.mem_singleton] at h
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.gpr_setFlags,h,ite_false]

end VG.Proof.Weierstrass.X86_64
