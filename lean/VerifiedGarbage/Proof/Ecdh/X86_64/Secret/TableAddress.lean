import VerifiedGarbage.Impl.Ecdh.P256.X86_64.Window5
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafAddress

/-! Public addresses for the sixteen 160-byte entries of the secret peer table. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64
open VG.Proof.X25519.X86_64

theorem tableAddress_ok (s : State) {base : Addr} {tbl j : Nat}
    (hb : s.gpr .rdi=base) (hj : s.gpr .rax=BitVec.ofNat 64 j)
    (hj1 : 1≤j) (ht : tbl<2^31) :
    WP isa (.block (Impl.Ecdh.X86_64.Window5.tableAddress tbl)) s fun t =>
      t.gpr .rdx=off base (tbl+160*(j-1)) ∧ Keeps [.rax,.rcx,.rdx] s t := by
  apply WP.of_runBlock
  simp only [Impl.Ecdh.X86_64.Window5.tableAddress,runBlock_cons,runStep_some,runBlock_nil,
    exec,readSrc,readSrc32,execAlu,execMul,State.setReg32,imm32_sext ht,hj,hb,
    RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.gpr_setFlags,Option.map_some,Option.bind_some,
    ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · rw [show (1 : BitVec 32).signExtend 64=BitVec.ofNat 64 1 from rfl,
      BitVec.ofNat_sub_ofNat_of_le j 1 (by decide) hj1]
    have hm : BitVec.ofNat 64 ((BitVec.ofNat 64 (j-1)).toNat*160)=BitVec.ofNat 64 (160*(j-1)) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_mul_mod,Nat.mul_comm (j-1)]
    change base+BitVec.ofNat 64 tbl+BitVec.ofNat 64 ((BitVec.ofNat 64 (j-1)).toNat*160)=_
    rw [hm,Offset.add_add]
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.gpr_setFlags,
      hr.1,hr.2.1,hr.2.2,ite_false]

theorem tableCounter_ok (s : State) {j : Nat} (hj : s.gpr .rbx=BitVec.ofNat 64 j) :
    WP isa (.block [.mov .rax (.reg .rbx)]) s fun t =>
      t.gpr .rax=BitVec.ofNat 64 j ∧ Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,readSrc,Option.map_some,
    RegUpd.gpr_setReg,ite_true,hj,Option.some.injEq,exists_eq_left']
  refine ⟨trivial,fun r hr => ?_,rfl,rfl,rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg,hr,ite_false]

end VG.Proof.Ecdh.X86_64.Secret
