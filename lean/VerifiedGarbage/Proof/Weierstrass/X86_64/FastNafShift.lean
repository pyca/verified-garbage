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

theorem fastShift7_value (a b c d e f g : BitVec 64) {w : Nat} (hw : w=1 ∨ w=5 ∨ w=7) :
    nafVal7 ((a>>>w)|||(b<<<(64-w))) ((b>>>w)|||(c<<<(64-w)))
      ((c>>>w)|||(d<<<(64-w))) ((d>>>w)|||(e<<<(64-w))) ((e>>>w)|||(f<<<(64-w)))
      ((f>>>w)|||(g<<<(64-w))) (g>>>w)=nafVal7 a b c d e f g/2^w := by
  simp only [nafVal7,fastJoin_value _ _ hw,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  rcases hw with rfl|rfl|rfl <;> omega

theorem shiftN_four (w : Nat) : FastNaf.shiftN 4 w=FastNaf.shift w := rfl

theorem shiftN_six (w : Nat) : FastNaf.shiftN 6 w=
    [.shift .shr .r8 w,.mov .rax (.reg .r9),.shift .shl .rax (64-w),.alu .or .r8 (.reg .rax),
     .shift .shr .r9 w,.mov .rax (.reg .r10),.shift .shl .rax (64-w),.alu .or .r9 (.reg .rax),
     .shift .shr .r10 w,.mov .rax (.reg .r11),.shift .shl .rax (64-w),.alu .or .r10 (.reg .rax),
     .shift .shr .r11 w,.mov .rax (.reg .r12),.shift .shl .rax (64-w),.alu .or .r11 (.reg .rax),
     .shift .shr .r12 w,.mov .rax (.reg .r13),.shift .shl .rax (64-w),.alu .or .r12 (.reg .rax),
     .shift .shr .r13 w,.mov .rax (.reg .r14),.shift .shl .rax (64-w),.alu .or .r13 (.reg .rax),
     .shift .shr .r14 w] := rfl

theorem fastShift7_ok (s : State) {w : Nat} (hw : w=1 ∨ w=5 ∨ w=7) :
    WP isa (.block (FastNaf.shiftN 6 w)) s fun t =>
      nafVal7 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) (t.gpr .r12) (t.gpr .r13) (t.gpr .r14)=
        nafVal7 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12) (s.gpr .r13)
          (s.gpr .r14)/2^w ∧
      Keeps [.rax,.r8,.r9,.r10,.r11,.r12,.r13,.r14] s t := by
  have hw0 : 1≤w ∧ w≤63 := by omega
  have hw1 : 1≤64-w ∧ 64-w≤63 := by omega
  have hw2 : ¬(64-w=1) := by omega
  apply WP.of_runBlock
  simp only [shiftN_six,runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,execShift,
    readSrc,Option.map_some,Option.bind_some,
    RegUpd.gpr_setReg,RegUpd.gpr_setFlags,RegUpd.gpr_arithFlags,
    ite_true,ite_false,and_self,reduceCtorEq,hw0,hw1,hw2,Option.some.injEq,exists_eq_left']
  refine ⟨fastShift7_value _ _ _ _ _ _ _ hw,fun r hr => ?_,rfl,rfl,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [RegUpd.gpr_setReg,RegUpd.gpr_setFlags,RegUpd.gpr_arithFlags,
    hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2.1,hr.2.2.2.2.2.1,hr.2.2.2.2.2.2.1,
    hr.2.2.2.2.2.2.2,ite_false]

theorem fastShift10_value (a b c d e f g h i l : BitVec 64) {w : Nat} (hw : w=1 ∨ w=5 ∨ w=7) :
    nafVal10 ((a>>>w)|||(b<<<(64-w))) ((b>>>w)|||(c<<<(64-w))) ((c>>>w)|||(d<<<(64-w))) ((d>>>w)|||(e<<<(64-w))) ((e>>>w)|||(f<<<(64-w))) ((f>>>w)|||(g<<<(64-w))) ((g>>>w)|||(h<<<(64-w))) ((h>>>w)|||(i<<<(64-w))) ((i>>>w)|||(l<<<(64-w))) (l>>>w)=nafVal10 a b c d e f g h i l/2^w := by
  simp only [nafVal10,fastJoin_value _ _ hw,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  rcases hw with rfl|rfl|rfl <;> omega

theorem shiftN_nine (w : Nat) : FastNaf.shiftN 9 w=
    [.shift .shr .r8 w,.mov .rax (.reg .r9),.shift .shl .rax (64-w),.alu .or .r8 (.reg .rax),
     .shift .shr .r9 w,.mov .rax (.reg .r10),.shift .shl .rax (64-w),.alu .or .r9 (.reg .rax),
     .shift .shr .r10 w,.mov .rax (.reg .r11),.shift .shl .rax (64-w),.alu .or .r10 (.reg .rax),
     .shift .shr .r11 w,.mov .rax (.reg .r12),.shift .shl .rax (64-w),.alu .or .r11 (.reg .rax),
     .shift .shr .r12 w,.mov .rax (.reg .r13),.shift .shl .rax (64-w),.alu .or .r12 (.reg .rax),
     .shift .shr .r13 w,.mov .rax (.reg .r14),.shift .shl .rax (64-w),.alu .or .r13 (.reg .rax),
     .shift .shr .r14 w,.mov .rax (.reg .r15),.shift .shl .rax (64-w),.alu .or .r14 (.reg .rax),
     .shift .shr .r15 w,.mov .rax (.reg .rbp),.shift .shl .rax (64-w),.alu .or .r15 (.reg .rax),
     .shift .shr .rbp w,.mov .rax (.reg .rsi),.shift .shl .rax (64-w),.alu .or .rbp (.reg .rax),
     .shift .shr .rsi w] := rfl

theorem fastShift10_ok (s : State) {w : Nat} (hw : w=1 ∨ w=5 ∨ w=7) :
    WP isa (.block (FastNaf.shiftN 9 w)) s fun t =>
      nafVal10 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) (t.gpr .r12) (t.gpr .r13) (t.gpr .r14) (t.gpr .r15) (t.gpr .rbp) (t.gpr .rsi)=
        nafVal10 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15) (s.gpr .rbp) (s.gpr .rsi)/2^w ∧
      Keeps [.rax,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15,.rbp,.rsi] s t := by
  have hw0 : 1≤w ∧ w≤63 := by omega
  have hw1 : 1≤64-w ∧ 64-w≤63 := by omega
  have hw2 : ¬(64-w=1) := by omega
  apply WP.of_runBlock
  simp only [shiftN_nine,runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,execShift,
    readSrc,Option.map_some,Option.bind_some,
    RegUpd.gpr_setReg,RegUpd.gpr_setFlags,RegUpd.gpr_arithFlags,
    ite_true,ite_false,and_self,reduceCtorEq,hw0,hw1,hw2,Option.some.injEq,exists_eq_left']
  refine ⟨fastShift10_value _ _ _ _ _ _ _ _ _ _ hw,fun r hr => ?_,rfl,rfl,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [RegUpd.gpr_setReg,RegUpd.gpr_setFlags,RegUpd.gpr_arithFlags,
    hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2.1,hr.2.2.2.2.2.1,hr.2.2.2.2.2.2.1,hr.2.2.2.2.2.2.2.1,hr.2.2.2.2.2.2.2.2.1,hr.2.2.2.2.2.2.2.2.2.1,hr.2.2.2.2.2.2.2.2.2.2,ite_false]

/-- The scalar's registers shifted right by `w` bits. -/
theorem fastShiftN_ok (s : State) {n w : Nat} (hn : n=4 ∨ n=6 ∨ n=9) (hw : w=1 ∨ w=5 ∨ w=7) :
    WP isa (.block (FastNaf.shiftN n w)) s fun t =>
      nafValN n t=nafValN n s/2^w ∧ Keeps (.rax::Naf.sregs n) s t := by
  rcases hn with rfl|rfl|rfl
  · rw [shiftN_four]
    exact WP.mono (fastShift_ok s hw) fun t ⟨vt,kt⟩ =>
      ⟨by rw [nafValN_four,nafValN_four]; exact vt,kt⟩
  · exact WP.mono (fastShift7_ok s hw) fun t ⟨vt,kt⟩ =>
      ⟨by rw [nafValN_six,nafValN_six]; exact vt,kt⟩
  · exact WP.mono (fastShift10_ok s hw) fun t ⟨vt,kt⟩ =>
      ⟨by rw [nafValN_nine,nafValN_nine]; exact vt,kt⟩

end VG.Proof.Weierstrass.X86_64
