import VerifiedGarbage.Proof.Weierstrass.X86_64.NafSubtract
import VerifiedGarbage.Proof.Weierstrass.FastNaf

/-! Signed-digit subtraction shares the same x86-64 implementation at both widths, for scalars of
four words (five registers), six words (seven registers) and nine words (ten registers). -/
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

/-- The step's arithmetic at any width `M`: the registers' value after subtracting the digit's
`M`-bit two's complement. -/
theorem sub_next_of {M o r m r' : Nat} {neg : Bool}
    (hs : (o+(if neg then M-m else m))%M=r) (hlt : o<M) (hm : m≤63) (hpos : neg=true → 0<m)
    (hrM : r+64≤M) (hr : if neg then r+m=2*r' else r=2*r'+m) : o=2*r' := by
  cases neg
  · simp only [Bool.false_eq_true,ite_false] at hs hr
    by_cases h : o+m<M
    · rw [Nat.mod_eq_of_lt h] at hs; omega
    · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)] at hs; omega
  · have hp := hpos rfl
    simp only [ite_true] at hs hr
    by_cases h : m≤o
    · rw [show o+(M-m)=(o-m)+M by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)] at hs; omega
    · rw [Nat.mod_eq_of_lt (by omega)] at hs; omega

theorem fastSub5_next (a b c d e : BitVec 64) (w k j : Nat)
    (hv : nafVal5 a b c d e=FastNaf.residual w k j) (hb : FastNaf.residual w k j≤2^256) :
    let x := BitVec.ofInt 64 (FastNaf.digit w k j)
    let out := nafSub5 a b c d e x (0#64-(x>>>63))
    nafVal5 out.1 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2 = 2*FastNaf.residual w k (j+1) := by
  have hs := nafSub5_value a b c d e (BitVec.ofInt 64 (FastNaf.digit w k j))
    (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63))
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
  exact sub_next_of hs (nafVal5_lt _ _ _ _ _) (fastMagnitude_bound w k j)
    (FastNaf.negative_magnitude_pos w k j) (by omega) (FastNaf.recurrence w k j)


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

theorem fastSub7_next (a b c d e f g : BitVec 64) (w k j : Nat)
    (hv : nafVal7 a b c d e f g=FastNaf.residual w k j) (hb : FastNaf.residual w k j≤(2^64)^6) :
    let x := BitVec.ofInt 64 (FastNaf.digit w k j)
    let out := nafSub7 a b c d e f g x (0#64-(x>>>63))
    nafVal7 out.1 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 out.2.2.2.2.2.1 out.2.2.2.2.2.2 =
      2*FastNaf.residual w k (j+1) := by
  have hs := nafSub7_value a b c d e f g (BitVec.ofInt 64 (FastNaf.digit w k j))
    (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63))
  dsimp only at hs ⊢
  rw [hv] at hs
  have he : nafVal7 (BitVec.ofInt 64 (FastNaf.digit w k j)) (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63)) (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63)) (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63)) (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63)) (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63)) (0#64-(BitVec.ofInt 64 (FastNaf.digit w k j)>>>63)) =
      if FastNaf.negative w k j then 2^256*2^192-FastNaf.magnitude w k j else FastNaf.magnitude w k j := by
    simp only [nafVal7,fastWord_toNat,fastSign_toNat]
    cases hn : FastNaf.negative w k j <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · omega
    · have := fastMagnitude_bound w k j; omega
  rw [he] at hs
  exact sub_next_of hs (nafVal7_lt _ _ _ _ _ _ _) (fastMagnitude_bound w k j)
    (FastNaf.negative_magnitude_pos w k j) (by omega) (FastNaf.recurrence w k j)

theorem subtractDigitN_four : Naf.subtractDigitN 4=Naf.subtractDigit := rfl

theorem subtractDigitN_six : Naf.subtractDigitN 6=
    [.mov .rax (.reg .rcx),.shift .shr .rax 63,.mov32 .rdx (.imm 0),.alu .sub .rdx (.reg .rax),
     .alu .sub .r8 (.reg .rcx),.alu .sbb .r9 (.reg .rdx),.alu .sbb .r10 (.reg .rdx),
     .alu .sbb .r11 (.reg .rdx),.alu .sbb .r12 (.reg .rdx),.alu .sbb .r13 (.reg .rdx),
     .alu .sbb .r14 (.reg .rdx)] := rfl

theorem fastSubtract7_ok (s : State) (w k j : Nat)
    (hx : s.gpr .rcx=BitVec.ofInt 64 (FastNaf.digit w k j))
    (hv : nafVal7 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12) (s.gpr .r13)
      (s.gpr .r14)=FastNaf.residual w k j)
    (hb : FastNaf.residual w k j≤(2^64)^6) :
    WP isa (.block (Naf.subtractDigitN 6)) s fun t =>
      nafVal7 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) (t.gpr .r12) (t.gpr .r13)
        (t.gpr .r14)=2*FastNaf.residual w k (j+1) ∧
      Keeps [.rax,.rdx,.r8,.r9,.r10,.r11,.r12,.r13,.r14] s t := by
  have hs := fastSub7_next (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12)
    (s.gpr .r13) (s.gpr .r14) w k j hv hb
  apply WP.of_runBlock
  simp only [subtractDigitN_six,runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,execShift,
    readSrc,readSrc32,State.setReg32,Option.map_some,Option.bind_some,
    RegUpd.gpr_setReg,RegUpd.gpr_setFlags,RegUpd.gpr_arithFlags,
    RegUpd.cf_arithFlags,RegUpd.cf_setReg,ite_true,ite_false,and_self,reduceCtorEq,hx,
    show 1≤63 ∧ 63≤63 from by decide,show ¬(63=1) from by decide,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · exact hs
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_setFlags,RegUpd.gpr_arithFlags,
      hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2.1,hr.2.2.2.2.2.1,hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1,hr.2.2.2.2.2.2.2.2,ite_false]

theorem fastSub10_next (a b c d e f g h i l : BitVec 64) (w k j : Nat)
    (hv : nafVal10 a b c d e f g h i l=FastNaf.residual w k j) (hb : FastNaf.residual w k j≤(2^64)^9) :
    let x := BitVec.ofInt 64 (FastNaf.digit w k j)
    let out := nafSub10 a b c d e f g h i l x (0#64-(x>>>63))
    nafVal10 out.1 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 out.2.2.2.2.2.1 out.2.2.2.2.2.2.1 out.2.2.2.2.2.2.2.1 out.2.2.2.2.2.2.2.2.1 out.2.2.2.2.2.2.2.2.2 =
      2*FastNaf.residual w k (j+1) := by
  have hs := nafSub10_value a b c d e f g h i l (BitVec.ofInt 64 (FastNaf.digit w k j))
    (0#64-((BitVec.ofInt 64 (FastNaf.digit w k j))>>>63))
  dsimp only at hs ⊢
  rw [hv] at hs
  have he : nafVal10 (BitVec.ofInt 64 (FastNaf.digit w k j)) (0#64-((BitVec.ofInt 64 (FastNaf.digit w k j))>>>63)) (0#64-((BitVec.ofInt 64 (FastNaf.digit w k j))>>>63)) (0#64-((BitVec.ofInt 64 (FastNaf.digit w k j))>>>63)) (0#64-((BitVec.ofInt 64 (FastNaf.digit w k j))>>>63)) (0#64-((BitVec.ofInt 64 (FastNaf.digit w k j))>>>63)) (0#64-((BitVec.ofInt 64 (FastNaf.digit w k j))>>>63)) (0#64-((BitVec.ofInt 64 (FastNaf.digit w k j))>>>63)) (0#64-((BitVec.ofInt 64 (FastNaf.digit w k j))>>>63)) (0#64-((BitVec.ofInt 64 (FastNaf.digit w k j))>>>63)) =
      if FastNaf.negative w k j then 2^256*2^256*2^128-FastNaf.magnitude w k j else FastNaf.magnitude w k j := by
    simp only [nafVal10_unfold,fastWord_toNat,fastSign_toNat]
    cases hn : FastNaf.negative w k j <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · omega
    · have := fastMagnitude_bound w k j; omega
  rw [he] at hs
  exact sub_next_of hs (nafVal10_lt _ _ _ _ _ _ _ _ _ _) (fastMagnitude_bound w k j)
    (FastNaf.negative_magnitude_pos w k j) (by omega) (FastNaf.recurrence w k j)

theorem subtractDigitN_nine : Naf.subtractDigitN 9=
    [.mov .rax (.reg .rcx),.shift .shr .rax 63,.mov32 .rdx (.imm 0),.alu .sub .rdx (.reg .rax),
     .alu .sub .r8 (.reg .rcx),.alu .sbb .r9 (.reg .rdx),.alu .sbb .r10 (.reg .rdx),.alu .sbb .r11 (.reg .rdx),.alu .sbb .r12 (.reg .rdx),.alu .sbb .r13 (.reg .rdx),.alu .sbb .r14 (.reg .rdx),.alu .sbb .r15 (.reg .rdx),.alu .sbb .rbp (.reg .rdx),.alu .sbb .rsi (.reg .rdx)] := rfl

theorem fastSubtract10_ok (s : State) (w k j : Nat)
    (hx : s.gpr .rcx=BitVec.ofInt 64 (FastNaf.digit w k j))
    (hv : nafVal10 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15) (s.gpr .rbp) (s.gpr .rsi)=FastNaf.residual w k j)
    (hb : FastNaf.residual w k j≤(2^64)^9) :
    WP isa (.block (Naf.subtractDigitN 9)) s fun t =>
      nafVal10 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) (t.gpr .r12) (t.gpr .r13) (t.gpr .r14) (t.gpr .r15) (t.gpr .rbp) (t.gpr .rsi)=2*FastNaf.residual w k (j+1) ∧
      Keeps [.rax,.rdx,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15,.rbp,.rsi] s t := by
  have hs := fastSub10_next (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15) (s.gpr .rbp) (s.gpr .rsi) w k j hv hb
  apply WP.of_runBlock
  simp only [subtractDigitN_nine,runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,execShift,
    readSrc,readSrc32,State.setReg32,Option.map_some,Option.bind_some,
    RegUpd.gpr_setReg,RegUpd.gpr_setFlags,RegUpd.gpr_arithFlags,
    RegUpd.cf_arithFlags,RegUpd.cf_setReg,ite_true,ite_false,and_self,reduceCtorEq,hx,
    show 1≤63 ∧ 63≤63 from by decide,show ¬(63=1) from by decide,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · exact hs
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_setFlags,RegUpd.gpr_arithFlags,
      hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2.1,hr.2.2.2.2.2.1,hr.2.2.2.2.2.2.1,hr.2.2.2.2.2.2.2.1,hr.2.2.2.2.2.2.2.2.1,hr.2.2.2.2.2.2.2.2.2.1,hr.2.2.2.2.2.2.2.2.2.2.1,hr.2.2.2.2.2.2.2.2.2.2.2,ite_false]

/-- `r8 … = r8 … - digit` for a scalar of `n` words and its top word. -/
theorem fastSubtractN_ok (s : State) {n : Nat} (hn : n=4 ∨ n=6 ∨ n=9) (w k j : Nat)
    (hx : s.gpr .rcx=BitVec.ofInt 64 (FastNaf.digit w k j))
    (hv : nafValN n s=FastNaf.residual w k j)
    (hb : FastNaf.residual w k j≤2^(64*n)) :
    WP isa (.block (Naf.subtractDigitN n)) s fun t =>
      nafValN n t=2*FastNaf.residual w k (j+1) ∧ Keeps (.rax::.rdx::Naf.sregs n) s t := by
  rcases hn with rfl|rfl|rfl
  · rw [nafValN_four] at hv
    exact WP.mono (fastSubtract_ok s w k j hx hv hb) fun t ⟨vt,kt⟩ => ⟨(nafValN_four t).trans vt,kt⟩
  · rw [nafValN_six] at hv
    exact WP.mono (fastSubtract7_ok s w k j hx hv (Nat.le_trans hb (Nat.le_of_eq (Nat.pow_mul 2 64 6)))) fun t ⟨vt,kt⟩ => ⟨(nafValN_six t).trans vt,kt⟩
  · rw [nafValN_nine] at hv
    exact WP.mono (fastSubtract10_ok s w k j hx hv (Nat.le_trans hb (Nat.le_of_eq (Nat.pow_mul 2 64 9))))
      fun t ⟨vt,kt⟩ => ⟨(nafValN_nine t).trans vt,kt⟩

end VG.Proof.Weierstrass.X86_64
