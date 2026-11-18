module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.FastNaf
public import VerifiedGarbage.Proof.Weierstrass.FastNaf
public import VerifiedGarbage.Proof.X25519.X86_64.Step
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Weierstrass.MontContract
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafSubtract

/-! ### `Weierstrass.X86_64.FastNafShift`, which the modules that import this one used -/

section

/-! Adjacent-word shifts by one, five or seven bits retain every scalar bit. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.X25519.X86_64

theorem fastJoin_value (lo hi : BitVec 64) {w : Nat} (hw : w=1 ∨ w=5 ∨ w=7 ∨ w=9) :
    ((lo>>>w)|||(hi<<<(64-w))).toNat=lo.toNat/2^w+2^(64-w)*(hi.toNat%2^w) := by
  have hlo : (lo>>>w).toNat<2^(64-w) := BitVec.toNat_ushiftRight_lt lo w (by omega_using [hw])
  have hhi : (hi<<<(64-w)).toNat=(hi.toNat%2^w)<<<(64-w) := by
    rcases hw with rfl|rfl|rfl|rfl <;> simp only [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq] <;> omega_using []
  rw [BitVec.toNat_or,hhi,Nat.or_comm,←Nat.shiftLeft_add_eq_or_of_lt hlo]
  simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,Nat.shiftLeft_eq]
  rw [Nat.mul_comm]
  omega_using []

/-- A Horner step of a shift: the low word's bits and the low bits of the rest. -/
theorem shift_horner {w : Nat} (hw : w=1 ∨ w=5 ∨ w=7 ∨ w=9) (lo : BitVec 64) (R : Nat) :
    (lo.toNat+2^64*R)/2^w=lo.toNat/2^w+2^(64-w)*(R%2^w)+2^64*(R/2^w) := by
  have := lo.isLt
  rcases hw with rfl|rfl|rfl|rfl <;> omega_using []

theorem mod_horner {w : Nat} (hw : w=1 ∨ w=5 ∨ w=7 ∨ w=9) (hi : BitVec 64) (R : Nat) :
    (hi.toNat+2^64*R)%2^w=hi.toNat%2^w := by
  rcases hw with rfl|rfl|rfl|rfl <;> omega_using []

theorem fastShift5_value (a b c d e : BitVec 64) {w : Nat} (hw : w=1 ∨ w=5 ∨ w=7 ∨ w=9) :
    nafVal5 ((a>>>w)|||(b<<<(64-w))) ((b>>>w)|||(c<<<(64-w)))
      ((c>>>w)|||(d<<<(64-w))) ((d>>>w)|||(e<<<(64-w))) (e>>>w)=nafVal5 a b c d e/2^w := by
  simp only [nafVal5,fastJoin_value _ _ hw,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  rcases hw with rfl|rfl|rfl|rfl <;> omega_using []

theorem fastShift_ok (s : State) {w : Nat} (hw : w=1 ∨ w=5 ∨ w=7 ∨ w=9) :
    WP isa (.block (FastNaf.shift w)) s fun t =>
      nafVal5 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) (t.gpr .r12)=
        nafVal5 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12)/2^w ∧
      Keeps [.rax,.r8,.r9,.r10,.r11,.r12] s t := by
  have hw0 : 1≤w ∧ w≤63 := by omega_using [hw]
  have hw1 : 1≤64-w ∧ 64-w≤63 := by omega_using [hw]
  have hw2 : ¬(64-w=1) := by omega_using [hw]
  apply WP.of_runBlock
  -- `nafVal5` behind a variable: `reduceCtorEq` would evaluate both sides of its equation.
  obtain ⟨N, hN⟩ : ∃ N, N = nafVal5 := ⟨_, rfl⟩
  rw [← hN]
  simp only [FastNaf.shift,runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,execShift,
    readSrc,Option.map_some,Option.bind_some,
    ↓RegUpd.gpr_setReg,↓RegUpd.gpr_setFlags,↓RegUpd.gpr_arithFlags,
    ↓reduceIte,and_self,reduceCtorEq,hw0,hw1,hw2,Option.some.injEq,exists_eq_left']
  subst hN
  refine ⟨fastShift5_value _ _ _ _ _ hw,fun r hr => ?_,rfl,rfl,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [RegUpd.gpr_setReg,RegUpd.gpr_setFlags,RegUpd.gpr_arithFlags,
    hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2.1,hr.2.2.2.2.2,ite_false]

theorem fastShift7_value (a b c d e f g : BitVec 64) {w : Nat} (hw : w=1 ∨ w=5 ∨ w=7 ∨ w=9) :
    nafVal7 ((a>>>w)|||(b<<<(64-w))) ((b>>>w)|||(c<<<(64-w)))
      ((c>>>w)|||(d<<<(64-w))) ((d>>>w)|||(e<<<(64-w))) ((e>>>w)|||(f<<<(64-w)))
      ((f>>>w)|||(g<<<(64-w))) (g>>>w)=nafVal7 a b c d e f g/2^w := by
  simp only [nafVal7,fastJoin_value _ _ hw,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,
    shift_horner hw,mod_horner hw]

theorem shiftN_four (w : Nat) : FastNaf.shiftN 4 w=FastNaf.shift w := rfl

theorem shiftN_six (w : Nat) : FastNaf.shiftN 6 w=
    [.shift .shr .r8 w,.mov .rax (.reg .r9),.shift .shl .rax (64-w),.alu .or .r8 (.reg .rax),
     .shift .shr .r9 w,.mov .rax (.reg .r10),.shift .shl .rax (64-w),.alu .or .r9 (.reg .rax),
     .shift .shr .r10 w,.mov .rax (.reg .r11),.shift .shl .rax (64-w),.alu .or .r10 (.reg .rax),
     .shift .shr .r11 w,.mov .rax (.reg .r12),.shift .shl .rax (64-w),.alu .or .r11 (.reg .rax),
     .shift .shr .r12 w,.mov .rax (.reg .r13),.shift .shl .rax (64-w),.alu .or .r12 (.reg .rax),
     .shift .shr .r13 w,.mov .rax (.reg .r14),.shift .shl .rax (64-w),.alu .or .r13 (.reg .rax),
     .shift .shr .r14 w] := rfl

theorem fastShift7_ok (s : State) {w : Nat} (hw : w=1 ∨ w=5 ∨ w=7 ∨ w=9) :
    WP isa (.block (FastNaf.shiftN 6 w)) s fun t =>
      nafVal7 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) (t.gpr .r12) (t.gpr .r13) (t.gpr .r14)=
        nafVal7 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12) (s.gpr .r13)
          (s.gpr .r14)/2^w ∧
      Keeps [.rax,.r8,.r9,.r10,.r11,.r12,.r13,.r14] s t := by
  have hw0 : 1≤w ∧ w≤63 := by omega_using [hw]
  have hw1 : 1≤64-w ∧ 64-w≤63 := by omega_using [hw]
  have hw2 : ¬(64-w=1) := by omega_using [hw]
  apply WP.of_runBlock
  -- `nafVal7` behind a variable: `reduceCtorEq` would evaluate both sides of its equation.
  obtain ⟨N, hN⟩ : ∃ N, N = nafVal7 := ⟨_, rfl⟩
  rw [← hN]
  simp only [shiftN_six,runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,execShift,
    readSrc,Option.map_some,Option.bind_some,
    ↓RegUpd.gpr_setReg,↓RegUpd.gpr_setFlags,↓RegUpd.gpr_arithFlags,
    ↓reduceIte,and_self,reduceCtorEq,hw0,hw1,hw2,Option.some.injEq,exists_eq_left']
  subst hN
  refine ⟨fastShift7_value _ _ _ _ _ _ _ hw,fun r hr => ?_,rfl,rfl,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [RegUpd.gpr_setReg,RegUpd.gpr_setFlags,RegUpd.gpr_arithFlags,
    hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2.1,hr.2.2.2.2.2.1,hr.2.2.2.2.2.2.1,
    hr.2.2.2.2.2.2.2,ite_false]

theorem fastShift10_value (a b c d e f g h i l : BitVec 64) {w : Nat} (hw : w=1 ∨ w=5 ∨ w=7 ∨ w=9) :
    nafVal10 ((a>>>w)|||(b<<<(64-w))) ((b>>>w)|||(c<<<(64-w))) ((c>>>w)|||(d<<<(64-w))) ((d>>>w)|||(e<<<(64-w))) ((e>>>w)|||(f<<<(64-w))) ((f>>>w)|||(g<<<(64-w))) ((g>>>w)|||(h<<<(64-w))) ((h>>>w)|||(i<<<(64-w))) ((i>>>w)|||(l<<<(64-w))) (l>>>w)=nafVal10 a b c d e f g h i l/2^w := by
  simp only [nafVal10_unfold,fastJoin_value _ _ hw,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,
    shift_horner hw,mod_horner hw]

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

theorem fastShift10_ok (s : State) {w : Nat} (hw : w=1 ∨ w=5 ∨ w=7 ∨ w=9) :
    WP isa (.block (FastNaf.shiftN 9 w)) s fun t =>
      nafVal10 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) (t.gpr .r12) (t.gpr .r13) (t.gpr .r14) (t.gpr .r15) (t.gpr .rbp) (t.gpr .rsi)=
        nafVal10 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15) (s.gpr .rbp) (s.gpr .rsi)/2^w ∧
      Keeps [.rax,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15,.rbp,.rsi] s t := by
  have hw0 : 1≤w ∧ w≤63 := by omega_using [hw]
  have hw1 : 1≤64-w ∧ 64-w≤63 := by omega_using [hw]
  have hw2 : ¬(64-w=1) := by omega_using [hw]
  apply WP.of_runBlock
  -- `nafVal10` behind a variable: `reduceCtorEq` would evaluate both sides of its equation.
  obtain ⟨N, hN⟩ : ∃ N, N = nafVal10 := ⟨_, rfl⟩
  rw [← hN]
  simp only [shiftN_nine,runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,execShift,
    readSrc,Option.map_some,Option.bind_some,
    ↓RegUpd.gpr_setReg,↓RegUpd.gpr_setFlags,↓RegUpd.gpr_arithFlags,
    ↓reduceIte,and_self,reduceCtorEq,hw0,hw1,hw2,Option.some.injEq,exists_eq_left']
  subst hN
  refine ⟨fastShift10_value _ _ _ _ _ _ _ _ _ _ hw,fun r hr => ?_,rfl,rfl,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [RegUpd.gpr_setReg,RegUpd.gpr_setFlags,RegUpd.gpr_arithFlags,
    hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2.1,hr.2.2.2.2.2.1,hr.2.2.2.2.2.2.1,hr.2.2.2.2.2.2.2.1,hr.2.2.2.2.2.2.2.2.1,hr.2.2.2.2.2.2.2.2.2.1,hr.2.2.2.2.2.2.2.2.2.2,ite_false]

/-- The scalar's registers shifted right by `w` bits. -/
theorem fastShiftN_ok (s : State) {n w : Nat} (hn : n=4 ∨ n=6 ∨ n=9) (hw : w=1 ∨ w=5 ∨ w=7 ∨ w=9) :
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

/-! ### By a count in a register -/

theorem shiftV_four : FastNaf.shiftV 4=
    [.shiftx .shrx .r8 .r8 .rdx,.shiftx .shlx .rax .r9 .rcx,.alu .or .r8 (.reg .rax),
     .shiftx .shrx .r9 .r9 .rdx,.shiftx .shlx .rax .r10 .rcx,.alu .or .r9 (.reg .rax),
     .shiftx .shrx .r10 .r10 .rdx,.shiftx .shlx .rax .r11 .rcx,.alu .or .r10 (.reg .rax),
     .shiftx .shrx .r11 .r11 .rdx,.shiftx .shlx .rax .r12 .rcx,.alu .or .r11 (.reg .rax),
     .shiftx .shrx .r12 .r12 .rdx] := rfl

theorem fastShiftV5_ok (s : State) {w : Nat} (hw : w=1 ∨ w=5 ∨ w=7 ∨ w=9)
    (hd : s.gpr .rdx=BitVec.ofNat 64 w) (hc : s.gpr .rcx=BitVec.ofNat 64 (64-w)) :
    WP isa (.block (FastNaf.shiftV 4)) s fun t =>
      nafVal5 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) (t.gpr .r12)=
        nafVal5 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12)/2^w ∧
      Keeps [.rax,.r8,.r9,.r10,.r11,.r12] s t := by
  have e1 : (BitVec.ofNat 64 w).toNat%64=w := by rcases hw with rfl|rfl|rfl|rfl <;> rfl
  have e2 : (BitVec.ofNat 64 (64-w)).toNat%64=64-w := by rcases hw with rfl|rfl|rfl|rfl <;> rfl
  apply WP.of_runBlock
  -- `nafVal5` behind a variable: `reduceCtorEq` would evaluate both sides of its equation.
  obtain ⟨N, hN⟩ : ∃ N, N = nafVal5 := ⟨_, rfl⟩
  rw [← hN]
  simp only [shiftV_four,runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,execShiftx,ShiftxOp.var,
    VarShiftOp.eval,readSrc,Option.bind_some,
    ↓RegUpd.gpr_setReg,↓RegUpd.gpr_arithFlags,
    ↓reduceIte,reduceCtorEq,hd,hc,e1,e2,Option.some.injEq,exists_eq_left']
  subst hN
  refine ⟨fastShift5_value _ _ _ _ _ hw,fun r hr => ?_,rfl,rfl,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2.1,hr.2.2.2.2.2,ite_false]

theorem shiftV_six : FastNaf.shiftV 6=
    [.shiftx .shrx .r8 .r8 .rdx,.shiftx .shlx .rax .r9 .rcx,.alu .or .r8 (.reg .rax),
     .shiftx .shrx .r9 .r9 .rdx,.shiftx .shlx .rax .r10 .rcx,.alu .or .r9 (.reg .rax),
     .shiftx .shrx .r10 .r10 .rdx,.shiftx .shlx .rax .r11 .rcx,.alu .or .r10 (.reg .rax),
     .shiftx .shrx .r11 .r11 .rdx,.shiftx .shlx .rax .r12 .rcx,.alu .or .r11 (.reg .rax),
     .shiftx .shrx .r12 .r12 .rdx,.shiftx .shlx .rax .r13 .rcx,.alu .or .r12 (.reg .rax),
     .shiftx .shrx .r13 .r13 .rdx,.shiftx .shlx .rax .r14 .rcx,.alu .or .r13 (.reg .rax),
     .shiftx .shrx .r14 .r14 .rdx] := rfl

theorem fastShiftV7_ok (s : State) {w : Nat} (hw : w=1 ∨ w=5 ∨ w=7 ∨ w=9)
    (hd : s.gpr .rdx=BitVec.ofNat 64 w) (hc : s.gpr .rcx=BitVec.ofNat 64 (64-w)) :
    WP isa (.block (FastNaf.shiftV 6)) s fun t =>
      nafVal7 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) (t.gpr .r12) (t.gpr .r13) (t.gpr .r14)=
        nafVal7 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)/2^w ∧
      Keeps [.rax,.r8,.r9,.r10,.r11,.r12,.r13,.r14] s t := by
  have e1 : (BitVec.ofNat 64 w).toNat%64=w := by rcases hw with rfl|rfl|rfl|rfl <;> rfl
  have e2 : (BitVec.ofNat 64 (64-w)).toNat%64=64-w := by rcases hw with rfl|rfl|rfl|rfl <;> rfl
  apply WP.of_runBlock
  -- `nafVal7` behind a variable: `reduceCtorEq` would evaluate both sides of its equation.
  obtain ⟨N, hN⟩ : ∃ N, N = nafVal7 := ⟨_, rfl⟩
  rw [← hN]
  simp only [shiftV_six,runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,execShiftx,ShiftxOp.var,
    VarShiftOp.eval,readSrc,Option.bind_some,
    ↓RegUpd.gpr_setReg,↓RegUpd.gpr_arithFlags,
    ↓reduceIte,reduceCtorEq,hd,hc,e1,e2,Option.some.injEq,exists_eq_left']
  subst hN
  refine ⟨fastShift7_value _ _ _ _ _ _ _ hw,fun r hr => ?_,rfl,rfl,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2.1,hr.2.2.2.2.2.1,hr.2.2.2.2.2.2.1,hr.2.2.2.2.2.2.2,ite_false]

theorem shiftV_nine : FastNaf.shiftV 9=
    [.shiftx .shrx .r8 .r8 .rdx,.shiftx .shlx .rax .r9 .rcx,.alu .or .r8 (.reg .rax),
     .shiftx .shrx .r9 .r9 .rdx,.shiftx .shlx .rax .r10 .rcx,.alu .or .r9 (.reg .rax),
     .shiftx .shrx .r10 .r10 .rdx,.shiftx .shlx .rax .r11 .rcx,.alu .or .r10 (.reg .rax),
     .shiftx .shrx .r11 .r11 .rdx,.shiftx .shlx .rax .r12 .rcx,.alu .or .r11 (.reg .rax),
     .shiftx .shrx .r12 .r12 .rdx,.shiftx .shlx .rax .r13 .rcx,.alu .or .r12 (.reg .rax),
     .shiftx .shrx .r13 .r13 .rdx,.shiftx .shlx .rax .r14 .rcx,.alu .or .r13 (.reg .rax),
     .shiftx .shrx .r14 .r14 .rdx,.shiftx .shlx .rax .r15 .rcx,.alu .or .r14 (.reg .rax),
     .shiftx .shrx .r15 .r15 .rdx,.shiftx .shlx .rax .rbp .rcx,.alu .or .r15 (.reg .rax),
     .shiftx .shrx .rbp .rbp .rdx,.shiftx .shlx .rax .rsi .rcx,.alu .or .rbp (.reg .rax),
     .shiftx .shrx .rsi .rsi .rdx] := rfl

theorem fastShiftV10_ok (s : State) {w : Nat} (hw : w=1 ∨ w=5 ∨ w=7 ∨ w=9)
    (hd : s.gpr .rdx=BitVec.ofNat 64 w) (hc : s.gpr .rcx=BitVec.ofNat 64 (64-w)) :
    WP isa (.block (FastNaf.shiftV 9)) s fun t =>
      nafVal10 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) (t.gpr .r12) (t.gpr .r13) (t.gpr .r14) (t.gpr .r15) (t.gpr .rbp) (t.gpr .rsi)=
        nafVal10 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15) (s.gpr .rbp) (s.gpr .rsi)/2^w ∧
      Keeps [.rax,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15,.rbp,.rsi] s t := by
  have e1 : (BitVec.ofNat 64 w).toNat%64=w := by rcases hw with rfl|rfl|rfl|rfl <;> rfl
  have e2 : (BitVec.ofNat 64 (64-w)).toNat%64=64-w := by rcases hw with rfl|rfl|rfl|rfl <;> rfl
  apply WP.of_runBlock
  -- `nafVal10` behind a variable: `reduceCtorEq` would evaluate both sides of its equation.
  obtain ⟨N, hN⟩ : ∃ N, N = nafVal10 := ⟨_, rfl⟩
  rw [← hN]
  simp only [shiftV_nine,runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,execShiftx,ShiftxOp.var,
    VarShiftOp.eval,readSrc,Option.bind_some,
    ↓RegUpd.gpr_setReg,↓RegUpd.gpr_arithFlags,
    ↓reduceIte,reduceCtorEq,hd,hc,e1,e2,Option.some.injEq,exists_eq_left']
  subst hN
  refine ⟨fastShift10_value _ _ _ _ _ _ _ _ _ _ hw,fun r hr => ?_,rfl,rfl,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2.1,hr.2.2.2.2.2.1,hr.2.2.2.2.2.2.1,hr.2.2.2.2.2.2.2.1,hr.2.2.2.2.2.2.2.2.1,hr.2.2.2.2.2.2.2.2.2.1,hr.2.2.2.2.2.2.2.2.2.2,ite_false]

/-- The scalar's registers shifted right by the `w` bits `rdx` has, with `64 - w` in `rcx`. -/
theorem fastShiftV_ok (s : State) {n w : Nat} (hn : n=4 ∨ n=6 ∨ n=9) (hw : w=1 ∨ w=5 ∨ w=7 ∨ w=9)
    (hd : s.gpr .rdx=BitVec.ofNat 64 w) (hc : s.gpr .rcx=BitVec.ofNat 64 (64-w)) :
    WP isa (.block (FastNaf.shiftV n)) s fun t =>
      nafValN n t=nafValN n s/2^w ∧ Keeps (.rax::Naf.sregs n) s t := by
  rcases hn with rfl|rfl|rfl
  · exact WP.mono (fastShiftV5_ok s hw hd hc) fun t ⟨vt,kt⟩ =>
      ⟨by rw [nafValN_four,nafValN_four]; exact vt,kt⟩
  · exact WP.mono (fastShiftV7_ok s hw hd hc) fun t ⟨vt,kt⟩ =>
      ⟨by rw [nafValN_six,nafValN_six]; exact vt,kt⟩
  · exact WP.mono (fastShiftV10_ok s hw hd hc) fun t ⟨vt,kt⟩ =>
      ⟨by rw [nafValN_nine,nafValN_nine]; exact vt,kt⟩

end VG.Proof.Weierstrass.X86_64

end

end

/-! Width-five, -seven and -nine public digit selection on x86-64. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.X25519.X86_64

def fastOdd (w : Nat) (x : BitVec 64) : BitVec 64 :=
  let y := x &&& BitVec.ofNat 64 (2^w-1)
  if y.toNat<2^(w-1) then y else y-BitVec.ofNat 64 (2^w)

theorem fastMask (x : BitVec 64) {w : Nat} (hw : FastNaf.Wide w) :
    x &&& BitVec.ofNat 64 (2^w-1)=BitVec.ofNat 64 (x.toNat%2^w) := by
  have hm : 2^w-1<2^64 := by rcases hw with rfl|rfl|rfl <;> decide
  have hp : 0<2^w := Nat.two_pow_pos w
  have hb : 2^w≤2^64 := by rcases hw with rfl|rfl|rfl <;> decide
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hm]
  rw [Nat.and_two_pow_sub_one_eq_mod,Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hp) hb)]

theorem fastDigit_mod {w : Nat} (hw : FastNaf.Wide w) (k j : Nat) :
    FastNaf.digit w k j =
      if FastNaf.residual w k j%2^w%2=0 then 0
      else if FastNaf.residual w k j%2^w<2^(w-1) then (FastNaf.residual w k j%2^w:Int)
      else (FastNaf.residual w k j%2^w:Int)-(2^w:Int) := by
  rcases hw with rfl|rfl|rfl
  · exact Naf5.digit_mod32 k j
  · exact FastNaf7.digit_mod128 k j
  · exact FastNaf9.digit_mod512 k j

theorem fastOdd_eq {x : BitVec 64} {w k j : Nat} (hw : FastNaf.Wide w)
    (hx : x.toNat%2^w=FastNaf.residual w k j%2^w)
    (ho : FastNaf.residual w k j%2≠0) : fastOdd w x=BitVec.ofInt 64 (FastNaf.digit w k j) := by
  rw [fastOdd,fastMask x hw,fastDigit_mod hw k j]
  rcases hw with rfl|rfl|rfl
  all_goals
    simp only [BitVec.toNat_ofNat,Nat.reducePow,Nat.reduceSub] at hx ⊢
    have hp : x.toNat%2≠0 := by omega_using [hx, ho]
    split <;> split <;> simp_all only []
    all_goals
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat,BitVec.toNat_ofInt,BitVec.toNat_sub]
      omega_arith

theorem fastChoose_ok (s : State) {w : Nat} (hw : FastNaf.Wide w) :
    WP isa (Impl.Weierstrass.X86_64.FastNaf.choose w) s fun t =>
      t.gpr .rcx=fastOdd w (s.gpr .r8) ∧ Keeps [.rcx] s t := by
  have hm : (BitVec.ofNat 32 (2^w-1)).signExtend 64=BitVec.ofNat 64 (2^w-1) := by
    rcases hw with rfl|rfl|rfl <;> rfl
  have ht : (BitVec.ofNat 32 (2^(w-1))).signExtend 64=BitVec.ofNat 64 (2^(w-1)) := by
    rcases hw with rfl|rfl|rfl <;> rfl
  have hp : (BitVec.ofNat 32 (2^w)).signExtend 64=BitVec.ofNat 64 (2^w) := by
    rcases hw with rfl|rfl|rfl <;> rfl
  have hb : 2^(w-1)<2^64 := by rcases hw with rfl|rfl|rfl <;> decide
  rw [Impl.Weierstrass.X86_64.FastNaf.choose]
  refine WP.seq ?_
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.map_some,Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    hm,ht,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hb,
    ite_true,Option.some.injEq,exists_eq_left']
  refine WP.ite (decide ((s.gpr .r8 &&& BitVec.ofNat 64 (2^w-1)).toNat<2^(w-1))) ?_ (fun h => ?_) (fun h => ?_)
  · rfl
  · apply WP.block_nil
    refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
    · simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,ite_true,fastOdd,
        of_decide_eq_true h,ite_true]
    · simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]
  · apply WP.of_runBlock
    simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
      Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,hp,
      ite_true,Option.some.injEq,exists_eq_left']
    refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
    · simp only [fastOdd,of_decide_eq_false h,ite_false]
    · simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]

/-! ### Without the branches -/

/-- `fastOdd` of an odd scalar and zero of an even one, as `digitB` computes it. -/
def fastSel (w : Nat) (x : BitVec 64) : BitVec 64 :=
  (((x &&& BitVec.ofNat 64 (2^w-1)) ^^^ BitVec.ofNat 64 (2^(w-1))) - BitVec.ofNat 64 (2^(w-1))) &&&
    (0 - (x &&& 1))

/-- The window's bits as a signed number, by flipping the top one and subtracting it; and its low
bit, which the window's is. -/
theorem fastXorSub {w : Nat} (hw : w=5 ∨ w=9) (m : Nat) (hm : m<2^w) :
    (BitVec.ofNat 64 m ^^^ BitVec.ofNat 64 (2^(w-1))) - BitVec.ofNat 64 (2^(w-1)) =
        (if m<2^(w-1) then BitVec.ofNat 64 m else BitVec.ofNat 64 m - BitVec.ofNat 64 (2^w)) ∧
      ((BitVec.ofNat 64 m ^^^ BitVec.ofNat 64 (2^(w-1))) - BitVec.ofNat 64 (2^(w-1))) &&& 1 =
        BitVec.ofNat 64 (m%2) := by
  rcases hw with rfl|rfl
  · exact (by decide +kernel : ∀ m, m<2^5 →
      (BitVec.ofNat 64 m ^^^ BitVec.ofNat 64 (2^(5-1))) - BitVec.ofNat 64 (2^(5-1)) =
          (if m<2^(5-1) then BitVec.ofNat 64 m else BitVec.ofNat 64 m - BitVec.ofNat 64 (2^5)) ∧
        ((BitVec.ofNat 64 m ^^^ BitVec.ofNat 64 (2^(5-1))) - BitVec.ofNat 64 (2^(5-1))) &&& 1 =
          BitVec.ofNat 64 (m%2)) m hm
  · exact (by decide +kernel : ∀ m, m<2^9 →
      (BitVec.ofNat 64 m ^^^ BitVec.ofNat 64 (2^(9-1))) - BitVec.ofNat 64 (2^(9-1)) =
          (if m<2^(9-1) then BitVec.ofNat 64 m else BitVec.ofNat 64 m - BitVec.ofNat 64 (2^9)) ∧
        ((BitVec.ofNat 64 m ^^^ BitVec.ofNat 64 (2^(9-1))) - BitVec.ofNat 64 (2^(9-1))) &&& 1 =
          BitVec.ofNat 64 (m%2)) m hm

theorem and_one (x : BitVec 64) : x &&& 1=BitVec.ofNat 64 (x.toNat%2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,BitVec.toNat_ofNat]
  change x.toNat &&& 1=_
  rw [Nat.and_one_is_mod]
  omega_using []

/-- The digit `digitB` leaves is the scalar's, zero when it is even. -/
theorem fastSel_eq {x : BitVec 64} {w k j : Nat} (hw : w=5 ∨ w=9)
    (hx : x.toNat%2^w=FastNaf.residual w k j%2^w) : fastSel w x=BitVec.ofInt 64 (FastNaf.digit w k j) := by
  have hW : FastNaf.Wide w := by
    rcases hw with rfl|rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
  have hm : x.toNat%2^w<2^w := Nat.mod_lt _ (Nat.two_pow_pos w)
  have hx2 : x.toNat%2=FastNaf.residual w k j%2 := by rcases hw with rfl|rfl <;> omega_using [hx]
  by_cases ho : FastNaf.residual w k j%2=0
  · have hd : FastNaf.digit w k j=0 := by
      rw [fastDigit_mod hW k j]
      simp only [show FastNaf.residual w k j%2^w%2=0 from by rcases hw with rfl|rfl <;> omega_using [ho],ite_true]
    rw [fastSel,and_one,hx2,ho,hd,show (0:BitVec 64)-BitVec.ofNat 64 0=0#64 from by decide,BitVec.and_zero]
    rfl
  · have h1 : x.toNat%2=1 := by omega_using [hx2, ho]
    rw [←fastOdd_eq hW hx ho,fastSel,and_one,h1,fastMask x hW,(fastXorSub hw _ hm).1,
      show (0:BitVec 64)-BitVec.ofNat 64 1=BitVec.allOnes 64 from by decide,BitVec.and_allOnes]
    simp only [fastOdd,fastMask x hW,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hm (show 2^w≤2^64 from by rcases hw with rfl|rfl <;> decide))]

/-- The low bit of the digit `digitB` leaves is the scalar's. -/
theorem fastSel_low {w : Nat} (hw : w=5 ∨ w=9) (x : BitVec 64) : fastSel w x &&& 1=x &&& 1 := by
  have hW : FastNaf.Wide w := by
    rcases hw with rfl|rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
  have hm : x.toNat%2^w<2^w := Nat.mod_lt _ (Nat.two_pow_pos w)
  have h2 : x.toNat%2^w%2=x.toNat%2 := by rcases hw with rfl|rfl <;> omega_using []
  rw [fastSel,and_one x]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h|h
  · rw [h,show (0:BitVec 64)-BitVec.ofNat 64 0=0#64 from by decide,BitVec.and_zero]
    rfl
  · rw [h,show (0:BitVec 64)-BitVec.ofNat 64 1=BitVec.allOnes 64 from by decide,BitVec.and_allOnes,
      fastMask x hW,(fastXorSub hw _ hm).2,h2,h]

/-- The digit, or zero for an even scalar, without a branch. -/
theorem digitB_ok (s : State) {w : Nat} (hw : w=5 ∨ w=9) :
    WP isa (.block (Impl.Weierstrass.X86_64.FastNaf.digitB w)) s fun t =>
      t.gpr .rcx=fastSel w (s.gpr .r8) ∧ Keeps [.rax,.rcx,.rdx] s t := by
  have hm : (BitVec.ofNat 32 (2^w-1)).signExtend 64=BitVec.ofNat 64 (2^w-1) := by
    rcases hw with rfl|rfl <;> rfl
  have ht : (BitVec.ofNat 32 (2^(w-1))).signExtend 64=BitVec.ofNat 64 (2^(w-1)) := by
    rcases hw with rfl|rfl <;> rfl
  have h1 : (1:BitVec 32).signExtend 64=1 := by decide
  apply WP.of_runBlock
  simp only [Impl.Weierstrass.X86_64.FastNaf.digitB,runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,
    readSrc,readSrc32,State.setReg32,Option.map_some,Option.bind_some,RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags,hm,ht,h1,ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨rfl,fun r hr => ?_,rfl,rfl,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,hr.1,hr.2.1,hr.2.2,ite_false]

/-- How far the scalar is shifted, from the digit's low bit: `1 + 2^e` after an odd digit and one
after zero, and 64 less that. -/
theorem countB_ok (s : State) {e : Nat} (he : e=2 ∨ e=3) {x : BitVec 64} (hc : s.gpr .rcx &&& 1=x &&& 1) :
    WP isa (.block (Impl.Weierstrass.X86_64.FastNaf.countB e)) s fun t =>
      t.gpr .rdx=BitVec.ofNat 64 (if x.toNat%2=0 then 1 else 1+2^e) ∧
      t.gpr .rcx=BitVec.ofNat 64 (64-(if x.toNat%2=0 then 1 else 1+2^e)) ∧ Keeps [.rcx,.rdx] s t := by
  have h1 : (1:BitVec 32).signExtend 64=1 := by decide
  have he0 : 1≤e ∧ e≤63 := by omega_using [he]
  apply WP.of_runBlock
  simp only [Impl.Weierstrass.X86_64.FastNaf.countB,runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,
    execShift,readSrc,readSrc32,State.setReg32,Option.map_some,Option.bind_some,RegUpd.gpr_setReg,
    RegUpd.gpr_setFlags,RegUpd.gpr_arithFlags,h1,hc,he0,and_self,ite_true,ite_false,reduceCtorEq,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · rw [and_one x]
    rcases Nat.mod_two_eq_zero_or_one x.toNat with h|h <;> rw [h] <;> rcases he with rfl|rfl <;> decide
  · rw [and_one x]
    rcases Nat.mod_two_eq_zero_or_one x.toNat with h|h <;> rw [h] <;> rcases he with rfl|rfl <;> decide
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_setFlags,RegUpd.gpr_arithFlags,hr.1,hr.2,ite_false]

/-- The index moved on by the count in `rdx`. -/
theorem fastAdvanceV_ok (s : State) {j d : Nat} (hc : s.gpr .rbx=BitVec.ofNat 64 j)
    (hd : s.gpr .rdx=BitVec.ofNat 64 d) :
    WP isa (.block [.alu .add .rbx (.reg .rdx)]) s fun t =>
      t.gpr .rbx=BitVec.ofNat 64 (j+d) ∧ Keeps [.rbx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,Option.bind_some,
    RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,hc,hd,ite_true,Option.some.injEq,exists_eq_left']
  refine ⟨(BitVec.ofNat_add ..).symm,fun r hr => ?_,rfl,rfl,rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,hr,ite_false]

end VG.Proof.Weierstrass.X86_64
