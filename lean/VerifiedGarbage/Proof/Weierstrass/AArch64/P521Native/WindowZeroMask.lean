module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowSelectWord
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Ed25519.AArch64

def windowOr (m : Mem) (base : Addr) (z : Nat) : Nat → BitVec 64 → BitVec 64
  | 0,a => a
  | k+1,a => windowOr m base z k a ||| VG.Proof.Mont.word m base (z+8*k)

def windowOrCode (z n : Nat) : List Instr :=
  (List.range n).flatMap fun i => [.ldr .x .x2 .x0 (z+8*i),.logic .orr .x .x1 .x1 .x2]

theorem window_or_step (s : State) :
    WP isa (.block [.logic .orr .x .x1 .x1 .x2]) s fun t =>
      t.gpr .x1=s.gpr .x1|||s.gpr .x2 ∧ Keeps [.x1] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
    RegUpd.gpr_write,BitVec.setWidth_eq,ite_true,Option.some.injEq,exists_eq_left']
  refine ⟨trivial,⟨?_,rfl,rfl,rfl,rfl⟩⟩
  reg_keeps

theorem window_or_ok {s : State} {base : Addr} {size z n : Nat}
    (hs : Scr s base size) (hz : z+8*n≤size) (hz8 : z%8=0) :
    ∀k≤n, WP isa (.block (windowOrCode z k)) s fun t =>
      t.gpr .x1=windowOr s.mem base z k (s.gpr .x1) ∧ Keeps [.x1,.x2] s t
  | 0,_ => WP.block_nil ⟨rfl,⟨fun _ _ => rfl,rfl,rfl,rfl,rfl⟩⟩
  | k+1,hk => by
    rw [windowOrCode,List.range_succ,List.flatMap_append,List.flatMap_singleton,WP.block_append_iff]
    refine WP.mono (window_or_ok hs hz hz8 k (by omega_arith)) fun u ⟨eu,ku⟩ => ?_
    have hu := hs.of_keeps ku (by decide)
    rw [←List.singleton_append,WP.block_append_iff]
    refine WP.mono (ldR_ok hu.ptr (d:=z+8*k) (by omega_arith) (by omega_arith) .x2)
      fun v ⟨ev,kv,_⟩ => ?_
    refine WP.mono (window_or_step v) fun t ⟨et,kt⟩ => ?_
    refine ⟨?_,ku.trans ((kv.mono (by simp)).trans (kt.mono (by simp)))⟩
    rw [et,kv.gpr .x1 (by decide),eu,ev,ku.mem]
    rfl

theorem window_or_zero (m : Mem) (base : Addr) (z k : Nat) (a : BitVec 64) :
    windowOr m base z k a=0#64 ↔ a=0#64 ∧ wordsVal m base z k=0 := by
  induction k with
  | zero => simp only [windowOr,wordsVal,and_true]
  | succ k ih =>
    rw [windowOr,BitVec.or_eq_zero_iff,ih,wordsVal_succ_top]
    have wordZero (w : BitVec 64) : w=0#64 ↔ w.toNat=0 := by
      constructor
      · intro h; rw [h]; rfl
      · intro h; exact BitVec.eq_of_toNat_eq h
    rw [wordZero (VG.Proof.Mont.word m base (z+8*k))]
    have hp : 0<2^(64*k) := Nat.two_pow_pos _
    simp only [Nat.add_eq_zero_iff,Nat.mul_eq_zero,show 2^(64*k)≠0 from Nat.ne_of_gt hp,false_or,and_assoc]

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Ed25519.AArch64
open VG.Proof.Ed25519.Word64

def windowMaskCode : List Instr := [.subs .x .x16 .x7 .x1,.sbc .x .x3 .x7 .x7]

theorem window_mask_ok (s : State) (zero : s.gpr .x7=0#64) :
    WP isa (.block windowMaskCode) s fun t =>
      t.gpr .x3=(if s.gpr .x1=0#64 then 0#64 else BitVec.allOnes 64) ∧
      Keeps [.x16,.x3] s t := by
  have carryZero (x : Word) : carryOut (0#64) (~~~x) true=decide (x=0#64) := by
    simp only [carryOut,BitVec.toNat_ofNat,BitVec.toNat_not,Bool.toNat_true,Nat.zero_add,Nat.zero_mod]
    have bound := x.isLt
    have eq : x=0#64 ↔ x.toNat=0 := by
      constructor
      · intro h; rw [h]; rfl
      · intro h; exact BitVec.eq_of_toNat_eq h
    rw [decide_eq_decide,eq]
    omega_arith
  apply WP.of_runBlock
  simp only [windowMaskCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,BitVec.setWidth_eq,
    zero,reduceCtorEq,ite_true,ite_false,Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨?_,?_,?_,?_,?_⟩⟩
  · change addCarry (0#64) (~~~(0#64)) (carryOut (0#64) (~~~(s.gpr .x1)) true)=_
    rw [carryZero]
    by_cases h : s.gpr .x1=0#64 <;> simp only [h,decide_true,decide_false,ite_true,ite_false] <;> rfl
  · reg_keeps
  · simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry]
  · simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry]
  · simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry]
  · simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]

end VG.Proof.Weierstrass.AArch64.P521Native
