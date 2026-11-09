module

-- separate module: The three-coordinate conditional-mux and register-frame replay (mixed_select_x_ok) costs 3.05s of proof versus 0.37s of imports; MixedFinish composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedSelectLoads
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MulFirst
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.StreamMemory

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64

def mixedZR0 : Nat → Reg | 0 => .x0 | 1 => .x2 | 2 => .x4 | _ => .x6
def mixedZR1 : Nat → Reg | 0 => .x1 | 1 => .x3 | 2 => .x5 | _ => .x7
def mixedZZero : Nat → Reg | 0 => .x2 | 1 => .x4 | 2 => .x6 | _ => .x8

def mixedZPairArith (i : Nat) : List Instr :=
  if i=0 then [.movz .x .x20 1 0,.cselc .x .x0 .x0 .x20 .ne,
    .movz .x .x2 0 0,.cselc .x .x1 .x1 .x2 .ne]
  else [.movz .x (mixedZZero i) 0 0,
    .cselc .x (mixedZR0 i) (mixedZR0 i) (mixedZZero i) .ne,
    .cselc .x (mixedZR1 i) (mixedZR1 i) (mixedZZero i) .ne]

def mixedZPairClob (i : Nat) : List Reg := [mixedZR0 i,mixedZR1 i,mixedZZero i,.x20]

theorem mixed_z_pair_arith (s : State) (i : Nat) (hi : i<4) :
    WP isa (.block (mixedZPairArith i)) s fun t =>
      t.gpr (mixedZR0 i)=(if s.zf then (if i=0 then 1 else 0) else s.gpr (mixedZR0 i)) ∧
      t.gpr (mixedZR1 i)=(if s.zf then 0 else s.gpr (mixedZR1 i)) ∧
      t.zf=s.zf ∧ Keeps (mixedZPairClob i) s t := by
  have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega_arith
  rcases hc with rfl|rfl|rfl|rfl <;> apply WP.of_runBlock <;>
    simp only [mixedZPairArith,mixedZR0,mixedZR1,mixedZZero,runBlock_cons,runStep_some,runBlock_nil,
      reduceExec,read_x,RegUpd.gpr_write,RegUpd.zf_write,CondCode.holds,BitVec.setWidth_eq,
      Size.bits,Nat.mul_zero,Nat.reduceLT,BitVec.shiftLeft_zero,reduceCtorEq,ite_true,ite_false,
      Option.some.injEq,exists_eq_left']
  all_goals
    refine ⟨?_,?_,True.intro,⟨?_,?_,?_,?_,?_⟩⟩
    · cases s.zf <;> rfl
    · cases s.zf <;> rfl
    · dsimp only [mixedZPairClob,mixedZR0,mixedZR1,mixedZZero]
      reg_keeps
    · simp only [RegUpd.mem_write]
    · simp only [RegUpd.rd_write]
    · simp only [RegUpd.wr_write]
    · simp only [RegUpd.sp_write]

def mixedZPair (i a : Nat) : List Instr := twoLoads .x30 (mixedZR0 i) (mixedZR1 i) a++mixedZPairArith i

theorem mixed_z_pair_ok {s : State} {p : Addr} {size a : Nat} (i : Nat) (hi : i<4)
    (hp : Ptr s .x30 p size) (ha : a+16≤size) (ha8 : a%8=0) :
    WP isa (.block (mixedZPair i a)) s fun t =>
      t.gpr (mixedZR0 i)=(if s.zf then (if i=0 then 1 else 0) else word s.mem p a) ∧
      t.gpr (mixedZR1 i)=(if s.zf then 0 else word s.mem p (a+8)) ∧
      t.zf=s.zf ∧ Keeps (mixedZPairClob i) s t := by
  have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega_arith
  have hr : Reg.x30≠mixedZR0 i ∧ mixedZR0 i≠mixedZR1 i := by rcases hc with rfl|rfl|rfl|rfl <;> decide
  rw [mixedZPair,WP.block_append_iff]
  refine WP.mono (mixed_two_loads_ok hp ha ha8 hr.1 hr.2) fun u ⟨e0,e1,ku,zu⟩ => ?_
  refine WP.mono (mixed_z_pair_arith u i hi) fun t ⟨a0,a1,zt,kt⟩ => ?_
  rw [zu,e0] at a0
  rw [zu,e1] at a1
  exact ⟨a0,a1,zt.trans zu,(ku.mono (by simp [mixedZPairClob])).trans kt⟩

def mixedZLastArith : List Instr := [.movz .x .x9 0 0,.cselc .x .x8 .x8 .x9 .ne]

theorem mixed_z_last_arith (s : State) :
    WP isa (.block mixedZLastArith) s fun t =>
      t.gpr .x8=(if s.zf then 0 else s.gpr .x8) ∧ t.zf=s.zf ∧ Keeps [.x8,.x9] s t := by
  apply WP.of_runBlock
  simp only [mixedZLastArith,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,
    RegUpd.gpr_write,RegUpd.zf_write,CondCode.holds,BitVec.setWidth_eq,
    Size.bits,Nat.mul_zero,Nat.reduceLT,BitVec.shiftLeft_zero,reduceCtorEq,ite_true,ite_false,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,True.intro,⟨?_,?_,?_,?_,?_⟩⟩
  · cases s.zf <;> rfl
  · reg_keeps
  · simp only [RegUpd.mem_write]
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [RegUpd.sp_write]

def mixedZLast (a : Nat) : List Instr := [.ldr .x .x8 .x30 a]++mixedZLastArith

theorem mixed_z_last_ok {s : State} {p : Addr} {size a : Nat}
    (hp : Ptr s .x30 p size) (ha : a+8≤size) (ha8 : a%8=0) :
    WP isa (.block (mixedZLast a)) s fun t =>
      t.gpr .x8=(if s.zf then 0 else word s.mem p a) ∧ t.zf=s.zf ∧ Keeps [.x8,.x9] s t := by
  rw [mixedZLast,WP.block_append_iff]
  refine WP.mono (mixed_ldR_ok hp ha ha8 .x8) fun u ⟨e,ku,zu⟩ => ?_
  refine WP.mono (mixed_z_last_arith u) fun t ⟨a,zt,kt⟩ => ?_
  rw [zu,e] at a
  exact ⟨a,zt.trans zu,(ku.mono (by simp)).trans kt⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64

def mixedSelectZRegs : List Reg := [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8]
def mixedSelectZ (a : Nat) : List Instr := mixedZPair 0 a++(mixedZPair 1 (a+16)++
  (mixedZPair 2 (a+32)++(mixedZPair 3 (a+48)++mixedZLast (a+64))))

theorem mixed_select_z_ok {s : State} {p : Addr} {size a : Nat}
    (hp : Ptr s .x30 p size) (ha : a+72≤size) (ha8 : a%8=0) :
    WP isa (.block (mixedSelectZ a)) s fun t =>
      mixedSelectZRegs.map t.gpr=(if s.zf then [1,0,0,0,0,0,0,0,0] else readWords s.mem p a 9) ∧
      t.zf=s.zf ∧ Keeps [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x20] s t := by
  rw [mixedSelectZ,WP.block_append_iff]
  refine WP.mono (mixed_z_pair_ok 0 (by decide) hp (by omega_arith) (by omega_arith))
    fun u ⟨e0,e1,z0,k0⟩ => ?_
  simp only [mixedZR0,mixedZR1,ite_true] at e0 e1
  have pre1 : Keeps [.x0,.x1,.x2,.x20] s u := k0
  have flag1 : u.zf=s.zf := z0
  rw [WP.block_append_iff]
  refine WP.mono (mixed_z_pair_ok 1 (by decide) (hp.of_keeps pre1 (by decide)) (by omega_arith) (by omega_arith))
    fun v ⟨e2,e3,z1,k1⟩ => ?_
  simp only [mixedZR0,mixedZR1,ite_false,reduceCtorEq] at e2 e3
  have pre2 : Keeps [.x0,.x1,.x2,.x3,.x4,.x20] s v := (pre1.mono (by decide)).trans (k1.mono (by decide))
  have flag2 : v.zf=s.zf := z1.trans flag1
  rw [WP.block_append_iff]
  refine WP.mono (mixed_z_pair_ok 2 (by decide) (hp.of_keeps pre2 (by decide)) (by omega_arith) (by omega_arith))
    fun w ⟨e4,e5,z2,k2⟩ => ?_
  simp only [mixedZR0,mixedZR1,ite_false,reduceCtorEq] at e4 e5
  have pre3 : Keeps [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x20] s w := (pre2.mono (by decide)).trans (k2.mono (by decide))
  have flag3 : w.zf=s.zf := z2.trans flag2
  rw [WP.block_append_iff]
  refine WP.mono (mixed_z_pair_ok 3 (by decide) (hp.of_keeps pre3 (by decide)) (by omega_arith) (by omega_arith))
    fun x ⟨e6,e7,z3,k3⟩ => ?_
  simp only [mixedZR0,mixedZR1,ite_false,reduceCtorEq] at e6 e7
  have pre4 : Keeps [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x20] s x := (pre3.mono (by decide)).trans (k3.mono (by decide))
  have flag4 : x.zf=s.zf := z3.trans flag3
  refine WP.mono (mixed_z_last_ok (hp.of_keeps pre4 (by decide)) (by omega_arith) (by omega_arith))
    fun t ⟨e8,z4,k4⟩ => ?_
  have tail0 : Keeps [.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x20] u t := (k1.mono (by decide)).trans ((k2.mono (by decide)).trans ((k3.mono (by decide)).trans ((k4.mono (by decide)))))
  rw [←tail0.gpr .x0 (by decide)] at e0
  rw [←tail0.gpr .x1 (by decide)] at e1
  have tail1 : Keeps [.x4,.x5,.x6,.x7,.x8,.x9,.x20] v t := (k2.mono (by decide)).trans ((k3.mono (by decide)).trans ((k4.mono (by decide))))
  rw [flag1,pre1.mem] at e2 e3
  rw [←tail1.gpr .x2 (by decide)] at e2
  rw [←tail1.gpr .x3 (by decide)] at e3
  have tail2 : Keeps [.x6,.x7,.x8,.x9,.x20] w t := (k3.mono (by decide)).trans ((k4.mono (by decide)))
  rw [flag2,pre2.mem] at e4 e5
  rw [←tail2.gpr .x4 (by decide)] at e4
  rw [←tail2.gpr .x5 (by decide)] at e5
  have tail3 : Keeps [.x8,.x9,.x20] x t := (k4.mono (by decide))
  rw [flag3,pre3.mem] at e6 e7
  rw [←tail3.gpr .x6 (by decide)] at e6
  rw [←tail3.gpr .x7 (by decide)] at e7
  rw [flag4,pre4.mem] at e8
  refine ⟨?_,z4.trans flag4,(pre4.mono (by decide)).trans (k4.mono (by decide))⟩
  cases h : s.zf <;> simp only [h,Bool.false_eq_true,ite_false,ite_true] at e0 e1 e2 e3 e4 e5 e6 e7 e8 ⊢
  all_goals simp only [mixedSelectZRegs,List.map_cons,List.map_nil,readWords,Nat.add_assoc,Nat.reduceAdd] at e0 e1 e2 e3 e4 e5 e6 e7 e8 ⊢
  all_goals simp only [e0,e1,e2,e3,e4,e5,e6,e7,e8]

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64

def mixedSelectXRegs : List Reg := [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8]
def mixedSelectX (a b : Nat) : List Instr := mixedSelectPair .x0 .x1 (a+0) (b+0)++(mixedSelectPair .x2 .x3 (a+16) (b+16)++(mixedSelectPair .x4 .x5 (a+32) (b+32)++(mixedSelectPair .x6 .x7 (a+48) (b+48)++mixedSelectWord .x8 (a+64) (b+64))))

theorem mixed_select_x_ok {s : State} {pa pb : Addr} {size cap a b : Nat}
    (hp : Ptr s .x30 pa size) (hq : Ptr s .x28 pb cap)
    (ha : a+72≤size) (hb : b+72≤cap) (ha8 : a%8=0) (hb8 : b%8=0) :
    WP isa (.block (mixedSelectX a b)) s fun t =>
      mixedSelectXRegs.map t.gpr=(if s.zf then readWords s.mem pb b 9 else readWords s.mem pa a 9) ∧
      t.zf=s.zf ∧ Keeps [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x20,.x21] s t := by
  rw [mixedSelectX,WP.block_append_iff]
  refine WP.mono (mixed_select_pair_ok .x0 .x1 hp hq
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by decide) (by decide))
    fun u ⟨e0,e1,z0,k0⟩ => ?_
  have pre1 : Keeps [.x0,.x1,.x20,.x21] s u := k0
  have flag1 : u.zf=s.zf := z0
  rw [WP.block_append_iff]
  refine WP.mono (mixed_select_pair_ok .x2 .x3 (hp.of_keeps pre1 (by decide)) (hq.of_keeps pre1 (by decide))
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by decide) (by decide))
    fun v ⟨e2,e3,z1,k1⟩ => ?_
  have pre2 : Keeps [.x0,.x1,.x2,.x3,.x20,.x21] s v := (pre1.mono (by decide)).trans (k1.mono (by decide))
  have flag2 : v.zf=s.zf := z1.trans flag1
  rw [WP.block_append_iff]
  refine WP.mono (mixed_select_pair_ok .x4 .x5 (hp.of_keeps pre2 (by decide)) (hq.of_keeps pre2 (by decide))
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by decide) (by decide))
    fun w ⟨e4,e5,z2,k2⟩ => ?_
  have pre3 : Keeps [.x0,.x1,.x2,.x3,.x4,.x5,.x20,.x21] s w := (pre2.mono (by decide)).trans (k2.mono (by decide))
  have flag3 : w.zf=s.zf := z2.trans flag2
  rw [WP.block_append_iff]
  refine WP.mono (mixed_select_pair_ok .x6 .x7 (hp.of_keeps pre3 (by decide)) (hq.of_keeps pre3 (by decide))
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by decide) (by decide))
    fun x ⟨e6,e7,z3,k3⟩ => ?_
  have pre4 : Keeps [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x20,.x21] s x := (pre3.mono (by decide)).trans (k3.mono (by decide))
  have flag4 : x.zf=s.zf := z3.trans flag3
  refine WP.mono (mixed_select_word_ok .x8 (hp.of_keeps pre4 (by decide)) (hq.of_keeps pre4 (by decide))
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by decide)) fun t ⟨e8,z4,k4⟩ => ?_
  have tail0 : Keeps [.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x20,.x21] u t := (k1.mono (by decide)).trans ((k2.mono (by decide)).trans ((k3.mono (by decide)).trans ((k4.mono (by decide)))))
  rw [←tail0.gpr .x0 (by decide)] at e0
  rw [←tail0.gpr .x1 (by decide)] at e1
  have tail1 : Keeps [.x4,.x5,.x6,.x7,.x8,.x20,.x21] v t := (k2.mono (by decide)).trans ((k3.mono (by decide)).trans ((k4.mono (by decide))))
  rw [flag1,pre1.mem] at e2 e3
  rw [←tail1.gpr .x2 (by decide)] at e2
  rw [←tail1.gpr .x3 (by decide)] at e3
  have tail2 : Keeps [.x6,.x7,.x8,.x20,.x21] w t := (k3.mono (by decide)).trans ((k4.mono (by decide)))
  rw [flag2,pre2.mem] at e4 e5
  rw [←tail2.gpr .x4 (by decide)] at e4
  rw [←tail2.gpr .x5 (by decide)] at e5
  have tail3 : Keeps [.x8,.x20,.x21] x t := (k4.mono (by decide))
  rw [flag3,pre3.mem] at e6 e7
  rw [←tail3.gpr .x6 (by decide)] at e6
  rw [←tail3.gpr .x7 (by decide)] at e7
  rw [flag4,pre4.mem] at e8
  refine ⟨?_,z4.trans flag4,(pre4.mono (by decide)).trans (k4.mono (by decide))⟩
  cases h : s.zf <;> simp only [h,Bool.false_eq_true,ite_false,ite_true] at e0 e1 e2 e3 e4 e5 e6 e7 e8 ⊢
  all_goals simp only [mixedSelectXRegs,List.map_cons,List.map_nil,readWords,Nat.add_assoc,Nat.reduceAdd] at e0 e1 e2 e3 e4 e5 e6 e7 e8 ⊢
  all_goals simp only [e0,e1,e2,e3,e4,e5,e6,e7,e8,Nat.add_zero]

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64

def mixedSelectYRegs : List Reg := [.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x19]
def mixedSelectY (a b : Nat) : List Instr := mixedSelectPair .x10 .x11 (a+0) (b+0)++(mixedSelectPair .x12 .x13 (a+16) (b+16)++(mixedSelectPair .x14 .x15 (a+32) (b+32)++(mixedSelectPair .x16 .x17 (a+48) (b+48)++mixedSelectWord .x19 (a+64) (b+64))))

theorem mixed_select_y_ok {s : State} {pa pb : Addr} {size cap a b : Nat}
    (hp : Ptr s .x30 pa size) (hq : Ptr s .x28 pb cap)
    (ha : a+72≤size) (hb : b+72≤cap) (ha8 : a%8=0) (hb8 : b%8=0) :
    WP isa (.block (mixedSelectY a b)) s fun t =>
      mixedSelectYRegs.map t.gpr=(if s.zf then readWords s.mem pb b 9 else readWords s.mem pa a 9) ∧
      t.zf=s.zf ∧ Keeps [.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x19,.x20,.x21] s t := by
  rw [mixedSelectY,WP.block_append_iff]
  refine WP.mono (mixed_select_pair_ok .x10 .x11 hp hq
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by decide) (by decide))
    fun u ⟨e0,e1,z0,k0⟩ => ?_
  have pre1 : Keeps [.x10,.x11,.x20,.x21] s u := k0
  have flag1 : u.zf=s.zf := z0
  rw [WP.block_append_iff]
  refine WP.mono (mixed_select_pair_ok .x12 .x13 (hp.of_keeps pre1 (by decide)) (hq.of_keeps pre1 (by decide))
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by decide) (by decide))
    fun v ⟨e2,e3,z1,k1⟩ => ?_
  have pre2 : Keeps [.x10,.x11,.x12,.x13,.x20,.x21] s v := (pre1.mono (by decide)).trans (k1.mono (by decide))
  have flag2 : v.zf=s.zf := z1.trans flag1
  rw [WP.block_append_iff]
  refine WP.mono (mixed_select_pair_ok .x14 .x15 (hp.of_keeps pre2 (by decide)) (hq.of_keeps pre2 (by decide))
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by decide) (by decide))
    fun w ⟨e4,e5,z2,k2⟩ => ?_
  have pre3 : Keeps [.x10,.x11,.x12,.x13,.x14,.x15,.x20,.x21] s w := (pre2.mono (by decide)).trans (k2.mono (by decide))
  have flag3 : w.zf=s.zf := z2.trans flag2
  rw [WP.block_append_iff]
  refine WP.mono (mixed_select_pair_ok .x16 .x17 (hp.of_keeps pre3 (by decide)) (hq.of_keeps pre3 (by decide))
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by decide) (by decide))
    fun x ⟨e6,e7,z3,k3⟩ => ?_
  have pre4 : Keeps [.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x20,.x21] s x := (pre3.mono (by decide)).trans (k3.mono (by decide))
  have flag4 : x.zf=s.zf := z3.trans flag3
  refine WP.mono (mixed_select_word_ok .x19 (hp.of_keeps pre4 (by decide)) (hq.of_keeps pre4 (by decide))
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by decide)) fun t ⟨e8,z4,k4⟩ => ?_
  have tail0 : Keeps [.x12,.x13,.x14,.x15,.x16,.x17,.x19,.x20,.x21] u t := (k1.mono (by decide)).trans ((k2.mono (by decide)).trans ((k3.mono (by decide)).trans ((k4.mono (by decide)))))
  rw [←tail0.gpr .x10 (by decide)] at e0
  rw [←tail0.gpr .x11 (by decide)] at e1
  have tail1 : Keeps [.x14,.x15,.x16,.x17,.x19,.x20,.x21] v t := (k2.mono (by decide)).trans ((k3.mono (by decide)).trans ((k4.mono (by decide))))
  rw [flag1,pre1.mem] at e2 e3
  rw [←tail1.gpr .x12 (by decide)] at e2
  rw [←tail1.gpr .x13 (by decide)] at e3
  have tail2 : Keeps [.x16,.x17,.x19,.x20,.x21] w t := (k3.mono (by decide)).trans ((k4.mono (by decide)))
  rw [flag2,pre2.mem] at e4 e5
  rw [←tail2.gpr .x14 (by decide)] at e4
  rw [←tail2.gpr .x15 (by decide)] at e5
  have tail3 : Keeps [.x19,.x20,.x21] x t := (k4.mono (by decide))
  rw [flag3,pre3.mem] at e6 e7
  rw [←tail3.gpr .x16 (by decide)] at e6
  rw [←tail3.gpr .x17 (by decide)] at e7
  rw [flag4,pre4.mem] at e8
  refine ⟨?_,z4.trans flag4,(pre4.mono (by decide)).trans (k4.mono (by decide))⟩
  cases h : s.zf <;> simp only [h,Bool.false_eq_true,ite_false,ite_true] at e0 e1 e2 e3 e4 e5 e6 e7 e8 ⊢
  all_goals simp only [mixedSelectYRegs,List.map_cons,List.map_nil,readWords,Nat.add_assoc,Nat.reduceAdd] at e0 e1 e2 e3 e4 e5 e6 e7 e8 ⊢
  all_goals simp only [e0,e1,e2,e3,e4,e5,e6,e7,e8,Nat.add_zero]

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Ed25519.AArch64

def mixedSelectXYCode : List Instr := ((mixedFnBlocks.drop 134).flatten.drop 28).take 54

def mixedSelectXYClob : List Reg := [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,
  .x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x19,.x20,.x21]

theorem mixedSelectXY_source : mixedSelectXYCode=(mixedFnBlocks.flatten.drop 4316).take 54 := by
  have h := drop_flatten_prefix mixedFnBlocks 134 4288 28
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 54) h.symm

theorem mixedSelectXY_split : mixedSelectXYCode=mixedSelectX 0 0++mixedSelectY 288 72 := by decide

theorem mixed_select_xy_ok {s : State} {pa pb : Addr} {size cap : Nat}
    (hp : Ptr s .x30 pa size) (hq : Ptr s .x28 pb cap) (ha : 360≤size) (hb : 144≤cap) :
    WP isa (.block mixedSelectXYCode) s fun t =>
      mixedSelectXRegs.map t.gpr=(if s.zf then readWords s.mem pb 0 9 else readWords s.mem pa 0 9) ∧
      mixedSelectYRegs.map t.gpr=(if s.zf then readWords s.mem pb 72 9 else readWords s.mem pa 288 9) ∧
      t.zf=s.zf ∧ Keeps mixedSelectXYClob s t := by
  rw [mixedSelectXY_split,WP.block_append_iff]
  refine WP.mono (mixed_select_x_ok hp hq (by omega_arith) (by omega_arith) (by decide) (by decide))
    fun u ⟨ex,zu,ku⟩ => ?_
  refine WP.mono (mixed_select_y_ok (hp.of_keeps ku (by decide)) (hq.of_keeps ku (by decide))
    ha hb (by decide) (by decide)) fun t ⟨ey,zt,kt⟩ => ?_
  have oldX : mixedSelectXRegs.map t.gpr=mixedSelectXRegs.map u.gpr := List.map_congr_left fun r hr =>
    kt.gpr r ((by decide : ∀r∈mixedSelectXRegs,r∉[Reg.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x19,.x20,.x21]) r hr)
  rw [zu,ku.mem] at ey
  exact ⟨oldX.trans ex,ey,zt.trans zu,(ku.mono (by decide)).trans (kt.mono (by decide))⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 (storesR)

theorem storesR_zf {size : Nat} {rn : Reg} : ∀ (rs : List Reg) {s : State} {p : Addr} {o : Nat},
    PtrW s rn p size → o+8*rs.length≤size → o%8=0 →
    WP isa (.block (storesR rn rs o)) s fun t => t.zf=s.zf
  | [],s,_,_,_,_,_ => WP.block_nil rfl
  | r::rs,s,p,o,hp,ho,ho8 => by
    simp only [List.length_cons] at ho
    rw [storesR,←List.singleton_append,WP.block_append_iff]
    refine WP.mono (stR_ok hp (d:=o) (by omega_arith) ho8 r) fun u e => ?_
    have hpu : PtrW u rn p size := by subst e; exact ⟨hp.reg,hp.st,hp.enc,hp.nowrap⟩
    refine WP.mono (storesR_zf rs hpu (by omega_arith) (by omega_arith)) fun t h => ?_
    rw [h,e]

theorem mixed_storesR_ok {s : State} {p : Addr} {size o : Nat} {rn : Reg} (rs : List Reg)
    (hp : PtrW s rn p size) (ho : o+8*rs.length≤size) (ho8 : o%8=0) (nd : rs.Nodup) :
    WP isa (.block (storesR rn rs o)) s fun t =>
      wordsVal t.mem p o rs.length=regsVal s rs ∧ KeepRegs [] s t ∧
      Outside p o (8*rs.length) s.mem t.mem ∧ t.zf=s.zf := by
  obtain ⟨t,ht,value,k,frame⟩ := VG.AArch64.Interleave.runBlock_of_WP (storesR_ok rs hp ho ho8 nd)
  obtain ⟨u,hu,flag⟩ := VG.AArch64.Interleave.runBlock_of_WP (storesR_zf rs hp ho ho8)
  have eq : u=t := Option.some.inj (hu.symm.trans ht)
  subst u
  exact WP.of_runBlock ⟨t,ht,value,k,frame,flag⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (value)

def mixedMuxCode : List Instr := ((mixedFnBlocks.drop 134).flatten.drop 28).take 105

def mixedMuxClob : List Reg := [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,
  .x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x19,.x20,.x21]

theorem mixedMux_source : mixedMuxCode=(mixedFnBlocks.flatten.drop 4316).take 105 := by
  have h := drop_flatten_prefix mixedFnBlocks 134 4288 28
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 105) h.symm

theorem mixedMux_split : mixedMuxCode=mixedSelectXYCode++(storesR .x26 mixedSelectXRegs 0++
    (storesR .x26 mixedSelectYRegs 72++(mixedSelectZ 360++storesR .x26 mixedSelectZRegs 144))) := by decide

theorem mixed_mux_ok {s : State} {pa pb po : Addr} {size cap room : Nat}
    (hp : Ptr s .x30 pa size) (hq : Ptr s .x28 pb cap) (ho : PtrW s .x26 po room)
    (ha : 432≤size) (hb : 144≤cap) (hout : 216≤room)
    (stableZ : ∀m,Outside po 0 144 s.mem m → wordsVal m pa 360 9=wordsVal s.mem pa 360 9) :
    WP isa (.block mixedMuxCode) s fun t =>
      wordsVal t.mem po 0 9=(if s.zf then wordsVal s.mem pb 0 9 else wordsVal s.mem pa 0 9) ∧
      wordsVal t.mem po 72 9=(if s.zf then wordsVal s.mem pb 72 9 else wordsVal s.mem pa 288 9) ∧
      wordsVal t.mem po 144 9=(if s.zf then 1 else wordsVal s.mem pa 360 9) ∧
      t.zf=s.zf ∧ KeepRegs mixedMuxClob s t ∧ Outside po 0 216 s.mem t.mem := by
  rw [mixedMux_split,WP.block_append_iff]
  refine WP.mono (mixed_select_xy_ok hp hq (by omega_arith) hb) fun u ⟨xm,ym,zu,ku⟩ => ?_
  have valueIf (b : Bool) (xs ys : List VG.Proof.Ed25519.Word64.Word) :
      value (if b then xs else ys)=(if b then value xs else value ys) := by cases b <;> rfl
  have xv := congrArg value xm
  have yv := congrArg value ym
  simp only [value_map_gpr,valueIf,readWords_value] at xv yv
  have hou := ho.of_keepRegs (Keeps.regs ku) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mixed_storesR_ok mixedSelectXRegs hou (by simpa only [show mixedSelectXRegs.length=9 from rfl] using (by omega_arith : 0+8*9≤room))
    (by decide) (by decide)) fun v ⟨xs,kv,ov,zv⟩ => ?_
  simp only [show mixedSelectXRegs.length=9 from rfl,Nat.reduceMul] at xs ov
  have yv' : regsVal v mixedSelectYRegs=regsVal u mixedSelectYRegs := regsVal_congr fun r _ => kv.gpr r (by simp)
  rw [←yv']
    at yv -- retain the selected value without rereading the source buffers
  have hov := hou.of_keepRegs kv (by simp)
  rw [WP.block_append_iff]
  refine WP.mono (mixed_storesR_ok mixedSelectYRegs hov (by simpa only [show mixedSelectYRegs.length=9 from rfl] using (by omega_arith : 72+8*9≤room))
    (by decide) (by decide)) fun w ⟨ys,kw,ow,zw⟩ => ?_
  simp only [show mixedSelectYRegs.length=9 from rfl,Nat.reduceMul] at ys ow
  have frameXY : Outside po 0 144 s.mem w.mem := by
    rw [←ku.mem]
    exact (ov.mono (by decide) (by decide)).trans (ow.mono (by decide) (by decide))
  have kp : KeepRegs mixedSelectXYClob s w := (Keeps.regs ku).trans
    ((kv.mono (by simp)).trans (kw.mono (by simp)))
  have hwZ : wordsVal w.mem pa 360 9=wordsVal s.mem pa 360 9 := stableZ w.mem frameXY
  have wz : w.zf=s.zf := zw.trans (zv.trans zu)
  rw [WP.block_append_iff]
  refine WP.mono (mixed_select_z_ok (hp.of_keepRegs kp (by decide)) ha (by decide)) fun x ⟨zm,zx,kx⟩ => ?_
  have zval := congrArg value zm
  simp only [value_map_gpr,valueIf,readWords_value] at zval
  rw [wz,hwZ] at zval
  have hox := (ho.of_keepRegs kp (by decide)).of_keepRegs (Keeps.regs kx) (by decide)
  refine WP.mono (mixed_storesR_ok mixedSelectZRegs hox (by simpa only [show mixedSelectZRegs.length=9 from rfl] using (by omega_arith : 144+8*9≤room))
    (by decide) (by decide)) fun t ⟨zs,kt,ot,zt⟩ => ?_
  simp only [show mixedSelectZRegs.length=9 from rfl,Nat.reduceMul] at zs ot
  have finalX : wordsVal t.mem po 0 9=wordsVal v.mem po 0 9 := by
    rw [ot.wordsVal (by decide) (by decide),kx.mem,ow.wordsVal (by decide) (by decide)]
  have finalY : wordsVal t.mem po 72 9=wordsVal w.mem po 72 9 := by
    rw [ot.wordsVal (by decide) (by decide),kx.mem]
  refine ⟨finalX.trans (xs.trans xv),finalY.trans (ys.trans yv),?_,zt.trans (zx.trans wz),
    (kp.mono (by decide)).trans (((Keeps.regs kx).mono (by decide)).trans (kt.mono (by simp))),?_⟩
  · rw [zs,zval]
    rfl
  · have oz : Outside po 144 72 w.mem t.mem := by rw [←kx.mem]; exact ot
    exact (frameXY.mono (by decide) (by decide)).trans (oz.mono (by decide) (by decide))

end VG.Proof.Mont.AArch64.P521Field
