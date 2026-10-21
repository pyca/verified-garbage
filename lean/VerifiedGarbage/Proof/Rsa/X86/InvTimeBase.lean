module
import VerifiedGarbage.Proof.Rsa.X86.BatchLaw

import VerifiedGarbage.Proof.Rsa.X86.InvChoose
public import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Proof.Framework.Taint
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Impl.Rsa.X86.KeyRt
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall

/-! # Public arguments at the CRT inverse boundary -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvTiming
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Rsa.X86.CrtValuesRt

 def τ : VG.X86.Taint.T := {regs:=.ofList [.edi,.esp],flags:=false,argLen:=68}
 def ArgsOk (s : State) : Prop :=
  (s.gpr .esp).toNat+68≤2^32 ∧ ∀ r∈s.wr,Region.Disjoint ⟨(s.gpr .esp).setWidth 64,68⟩ r
 structure Public (args : Nat → BitVec 32) (base : Addr) (size : Nat) (sp : BitVec 32) (s : State) : Prop where
  argsOk : ArgsOk s
  stack : s.gpr .esp=sp
  arguments : ∀ i,i<16 → CallArgument s base size i (args i)

 theorem Public.keep {args : Nat → BitVec 32} {base : Addr} {size : Nat} {sp : BitVec 32} {s t : State} {regs : List Reg}
    (h : Public args base size sp s) (K : Keeps regs s t) (keepSp : .esp∉regs)
    (O : Outside base 0 size s.mem t.mem) : Public args base size sp t := by
  have esp := K.1 .esp keepSp
  refine ⟨⟨?_,?_⟩,esp.trans h.stack,fun i hi => (h.arguments i hi).keep K keepSp O⟩
  · rw [esp]; exact h.argsOk.1
  · intro r hr
    rw [esp]
    exact h.argsOk.2 r (K.2.2 ▸ hr)

 theorem wf {s : State} (A : ArgsOk s) : VG.X86.Taint.Wf τ s :=
  VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h,fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim,fun _ => A,fun _ h => (List.not_mem_nil h).elim⟩

 theorem agree {args : Nat → BitVec 32} {base : Addr} {size : Nat} {sp : BitVec 32} {s t : State}
    (hs : Scr s base size) (ht : Scr t base size) (ps : Public args base size sp s) (pt : Public args base size sp t) :
    VG.X86.Taint.Agree τ s t := by
  refine ⟨⟨?_,fun h => nomatch h⟩,fun h => absurd rfl h,wf ps.argsOk,wf pt.argsOk,
    VG.X86.Taint.slotsOk_empty,VG.X86.Taint.slotsAgree_empty,fun _ => ps.stack.trans pt.stack.symm,?_⟩
  · intro r hr
    simp only [τ,RegSet.mem_ofList,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (hs.edi_toNat.trans ht.edi_toNat.symm)
    · exact ps.stack.trans pt.stack.symm
  · intro k h4 hk
    simp only [τ] at hk
    rw [show VG.X86.Taint.depth τ.stk=0 from rfl,Nat.zero_add,
      VG.X86.Taint.argByte_eq ps.argsOk.1 h4 hk,VG.X86.Taint.argByte_eq pt.argsOk.1 h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)),Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ ((ps.arguments _ (by omega)).value.trans (pt.arguments _ (by omega)).value.symm)

 theorem compare7_check (limit : Nat) :
    (VG.Taint.check taint τ (.block [.mov .eax (.mem (VG.Impl.Rsa.X86.KeyRt.argOp 7)),.alu .cmp .eax (.imm (BitVec.ofNat 32 limit))])
    (VG.Taint.hintOf taint τ (.block [.mov .eax (.mem (VG.Impl.Rsa.X86.KeyRt.argOp 7)),.alu .cmp .eax (.imm (BitVec.ofNat 32 limit))]))).isSome=true := by rfl
 theorem compare9_check (limit : Nat) :
    (VG.Taint.check taint τ (.block [.mov .eax (.mem (VG.Impl.Rsa.X86.KeyRt.argOp 9)),.alu .cmp .eax (.imm (BitVec.ofNat 32 limit))])
    (VG.Taint.hintOf taint τ (.block [.mov .eax (.mem (VG.Impl.Rsa.X86.KeyRt.argOp 9)),.alu .cmp .eax (.imm (BitVec.ofNat 32 limit))]))).isSome=true := by rfl
 theorem compare11_check (limit : Nat) :
    (VG.Taint.check taint τ (.block [.mov .eax (.mem (VG.Impl.Rsa.X86.KeyRt.argOp 11)),.alu .cmp .eax (.imm (BitVec.ofNat 32 limit))])
    (VG.Taint.hintOf taint τ (.block [.mov .eax (.mem (VG.Impl.Rsa.X86.KeyRt.argOp 11)),.alu .cmp .eax (.imm (BitVec.ofNat 32 limit))]))).isSome=true := by rfl

end VG.Proof.Rsa.X86.InvTiming
