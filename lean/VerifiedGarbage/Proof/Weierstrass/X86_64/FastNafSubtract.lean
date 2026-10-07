import VerifiedGarbage.Proof.Weierstrass.X86_64.NafSubtract
import VerifiedGarbage.Proof.Weierstrass.FastNaf

/-! Signed-digit subtraction shares the same five-word x86-64 implementation at both widths. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.X25519.X86_64

theorem fastMagnitude_bound (w k j : Nat) : FastNaf.magnitude w k j≤63 := by
  by_cases h : w=7
  · simpa only [FastNaf.magnitude,h,ite_true] using FastNaf7.magnitude_le k j
  · have hb := Naf5.magnitude_le k j
    simp only [FastNaf.magnitude,h,ite_false]
    omega

theorem fastDigit_eq (w k j : Nat) : FastNaf.digit w k j=
    if FastNaf.negative w k j then -(FastNaf.magnitude w k j:Int) else (FastNaf.magnitude w k j:Int) := by
  by_cases h : w=7 <;> simp only [FastNaf.digit,FastNaf.negative,FastNaf.magnitude,h,
    ite_true,ite_false,FastNaf7.digit,Naf5.digit]

theorem fastWord_toNat (w k j : Nat) :
    (BitVec.ofInt 64 (FastNaf.digit w k j)).toNat =
      if FastNaf.negative w k j then 2^64-FastNaf.magnitude w k j else FastNaf.magnitude w k j := by
  have hb := fastMagnitude_bound w k j
  rw [fastDigit_eq]
  simp only [BitVec.toNat_ofInt]
  cases hn : FastNaf.negative w k j
  · simp only [Bool.false_eq_true,ite_false]
    change ((FastNaf.magnitude w k j:Int)%18446744073709551616).toNat=_
    omega
  · have hp := FastNaf.negative_magnitude_pos w k j hn
    simp only [ite_true]
    change ((-(FastNaf.magnitude w k j:Int))%18446744073709551616).toNat=_
    omega

theorem fastSign_toNat (w k j : Nat) :
    (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63)).toNat =
      if FastNaf.negative w k j then 2^64-1 else 0 := by
  have hb := fastMagnitude_bound w k j
  have hp := FastNaf.negative_magnitude_pos w k j
  simp only [BitVec.toNat_sub,BitVec.toNat_zero,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,fastWord_toNat]
  cases hn : FastNaf.negative w k j
  · simp only [Bool.false_eq_true,ite_false]; omega
  · have hp := hp hn
    simp only [ite_true]; omega

theorem fastSub5_next (a b c d e : BitVec 64) (w k j : Nat)
    (hv : nafVal5 a b c d e=FastNaf.residual w k j) (hb : FastNaf.residual w k j≤2^256) :
    let x := BitVec.ofInt 64 (FastNaf.digit w k j)
    let out := nafSub5 a b c d e x (0#64-(x>>>63))
    nafVal5 out.1 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2 = 2*FastNaf.residual w k (j+1) := by
  have hs := nafSub5_value a b c d e (BitVec.ofInt 64 (FastNaf.digit w k j))
    (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63))
  have hlt := nafVal5_lt (nafSub5 a b c d e (BitVec.ofInt 64 (FastNaf.digit w k j))
    (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63))).1
    (nafSub5 a b c d e (BitVec.ofInt 64 (FastNaf.digit w k j)) (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63))).2.1
    (nafSub5 a b c d e (BitVec.ofInt 64 (FastNaf.digit w k j)) (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63))).2.2.1
    (nafSub5 a b c d e (BitVec.ofInt 64 (FastNaf.digit w k j)) (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63))).2.2.2.1
    (nafSub5 a b c d e (BitVec.ofInt 64 (FastNaf.digit w k j)) (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63))).2.2.2.2
  dsimp only at hs ⊢
  rw [hv] at hs
  have he : nafVal5 (BitVec.ofInt 64 (FastNaf.digit w k j))
      (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63))
      (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63))
      (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63))
      (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63)) =
      if FastNaf.negative w k j then 2^320-FastNaf.magnitude w k j else FastNaf.magnitude w k j := by
    simp only [nafVal5,fastWord_toNat,fastSign_toNat]
    cases hn : FastNaf.negative w k j <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · omega
    · have := fastMagnitude_bound w k j; omega
  rw [he] at hs
  have hr := FastNaf.recurrence w k j
  have hm := fastMagnitude_bound w k j
  cases hn : FastNaf.negative w k j <;> simp only [hn,Bool.false_eq_true,ite_false,ite_true] at hs hr <;> omega


theorem fastSubtract_ok (s : State) (w k j : Nat)
    (hx : s.gpr .rcx=BitVec.ofInt 64 (FastNaf.digit w k j))
    (hv : nafVal5 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12)=FastNaf.residual w k j)
    (hb : FastNaf.residual w k j≤2^256) :
    WP isa (.block Naf.subtractDigit) s fun t =>
      nafVal5 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) (t.gpr .r12)=2*FastNaf.residual w k (j+1) ∧
      Keeps [.rax,.rdx,.r8,.r9,.r10,.r11,.r12] s t := by
  have hs := fastSub5_next (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12) w k j hv hb
  apply WP.of_runBlock
  simp only [Naf.subtractDigit,runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,execShift,
    readSrc,readSrc32,State.setReg32,Option.map_some,Option.bind_some,
    RegUpd.gpr_setReg,RegUpd.gpr_setFlags,RegUpd.gpr_arithFlags,
    RegUpd.cf_arithFlags,RegUpd.cf_setReg,ite_true,ite_false,and_self,reduceCtorEq,hx,
    show 1≤63 ∧ 63≤63 from by decide,show ¬(63=1) from by decide,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · exact hs
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_setFlags,RegUpd.gpr_arithFlags,
      hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2.1,hr.2.2.2.2.2.1,hr.2.2.2.2.2.2,ite_false]

end VG.Proof.Weierstrass.X86_64
