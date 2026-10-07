import VerifiedGarbage.Impl.Weierstrass.X86_64.FastNaf
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafSubtract

/-! Adjacent-word shifts by one, five or seven bits retain every scalar bit. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.X25519.X86_64

theorem fastJoin_value (lo hi : BitVec 64) {w : Nat} (hw : w=1 ∨ w=5 ∨ w=7) :
    ((lo>>>w)|||(hi<<<(64-w))).toNat=lo.toNat/2^w+2^(64-w)*(hi.toNat%2^w) := by
  have hlo : (lo>>>w).toNat<2^(64-w) := BitVec.toNat_ushiftRight_lt lo w (by omega)
  have hhi : (hi<<<(64-w)).toNat=(hi.toNat%2^w)<<<(64-w) := by
    rcases hw with rfl|rfl|rfl <;> simp only [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq] <;> omega
  rw [BitVec.toNat_or,hhi,Nat.or_comm,←Nat.shiftLeft_add_eq_or_of_lt hlo]
  simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,Nat.shiftLeft_eq]
  rw [Nat.mul_comm]
  omega

theorem fastShift5_value (a b c d e : BitVec 64) {w : Nat} (hw : w=1 ∨ w=5 ∨ w=7) :
    nafVal5 ((a>>>w)|||(b<<<(64-w))) ((b>>>w)|||(c<<<(64-w)))
      ((c>>>w)|||(d<<<(64-w))) ((d>>>w)|||(e<<<(64-w))) (e>>>w)=nafVal5 a b c d e/2^w := by
  simp only [nafVal5,fastJoin_value _ _ hw,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  rcases hw with rfl|rfl|rfl <;> omega

theorem fastShift_ok (s : State) {w : Nat} (hw : w=1 ∨ w=5 ∨ w=7) :
    WP isa (.block (FastNaf.shift w)) s fun t =>
      nafVal5 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) (t.gpr .r12)=
        nafVal5 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12)/2^w ∧
      Keeps [.rax,.r8,.r9,.r10,.r11,.r12] s t := by
  have hw0 : 1≤w ∧ w≤63 := by omega
  have hw1 : 1≤64-w ∧ 64-w≤63 := by omega
  have hw2 : ¬(64-w=1) := by omega
  apply WP.of_runBlock
  simp only [FastNaf.shift,runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,execShift,
    readSrc,Option.map_some,Option.bind_some,
    RegUpd.gpr_setReg,RegUpd.gpr_setFlags,RegUpd.gpr_arithFlags,
    ite_true,ite_false,and_self,reduceCtorEq,hw0,hw1,hw2,Option.some.injEq,exists_eq_left']
  refine ⟨fastShift5_value _ _ _ _ _ hw,fun r hr => ?_,rfl,rfl,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [RegUpd.gpr_setReg,RegUpd.gpr_setFlags,RegUpd.gpr_arithFlags,
    hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2.1,hr.2.2.2.2.2,ite_false]

end VG.Proof.Weierstrass.X86_64
