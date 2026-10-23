module

public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Joint
public import VerifiedGarbage.Proof.X448.AArch64.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Recode

/-! Read one signed public digit without crossing either 464-byte buffer. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (BITS)
open VG.Proof.X448.AArch64 (Scr Keeps off read1_eq)

private theorem byte_zext : ∀ b:BitVec 8,(b.setWidth 32).setWidth 64=b.setWidth 64 := by decide +kernel

theorem keyDigit_ok {s:State} {base:Addr} (hs:Scr s base) {i:Nat} (hi:i<464)
    (hc:s.gpr .x19=BitVec.ofNat 64 i) :
    WP isa (.block keyDigit) s fun t =>
      t.gpr .x11=(s.mem (off base (BITS+i))).setWidth 64 ∧
      Keeps [.x2,.x11] s t ∧ t.mem=s.mem := by
  have ha:base+BitVec.ofNat 64 i+BitVec.ofNat 64 BITS=off base (BITS+i):=by
    rw [off,Offset.add_add]
    exact congrArg (fun n => base+BitVec.ofNat 64 n) (by omega)
  have hr:=hs.read (d:=BITS+i) (n:=1) (by simp only [BITS];omega)
  have enc:BITS%1=0 ∧ BITS<4096:=by decide
  apply WP.of_runBlock
  simp only [keyDigit,runBlock_cons,runStep_some,runBlock_nil,exec,State.read,Size.bits,
    addr,enc,and_self,RegUpd.gpr_write,RegUpd.rd_write,RegUpd.wr_write,RegUpd.mem_write,BitVec.setWidth_eq,hs.x3,hc,ha,
    State.load,hr,read1_eq,ite_true,ite_false,reduceCtorEq,Option.map_some,Option.bind_some,
    byte_zext,Option.some.injEq,exists_eq_left']
  refine ⟨by trivial,⟨fun r hr => ?_,rfl,rfl⟩,by trivial⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]

theorem baseDigit_ok {s:State} {base:Addr} (hs:Scr s base) {i:Nat} (hi:i<464)
    (hc:s.gpr .x19=BitVec.ofNat 64 i) :
    WP isa (.block baseDigit) s fun t =>
      t.gpr .x11=(s.mem (off base (SDIG+i))).setWidth 64 ∧
      Keeps [.x2,.x11] s t ∧ t.mem=s.mem := by
  have ha:base+BitVec.ofNat 64 i+(3400#64)+(3400#64)=off base (SDIG+i):=by
    change base+BitVec.ofNat 64 i+BitVec.ofNat 64 3400+BitVec.ofNat 64 3400=_
    rw [off,Offset.add_add,Offset.add_add]
    exact congrArg (fun n => base+BitVec.ofNat 64 n) (by simp only [SDIG];omega)
  have hr:=hs.read (d:=SDIG+i) (n:=1) (by simp only [SDIG];omega)
  apply WP.of_runBlock
  simp only [baseDigit,runBlock_cons,runStep_some,runBlock_nil,exec,State.read,Size.bits,
    addr,Nat.reduceMul,Nat.reduceLT,Nat.mod_one,and_self,RegUpd.gpr_write,RegUpd.rd_write,RegUpd.wr_write,RegUpd.mem_write,BitVec.setWidth_eq,hs.x3,hc,ha,
    BitVec.add_zero,State.load,hr,read1_eq,ite_true,ite_false,reduceCtorEq,Option.map_some,Option.bind_some,
    byte_zext,Option.some.injEq,exists_eq_left']
  refine ⟨by trivial,⟨fun r hr => ?_,rfl,rfl⟩,by trivial⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]

end VG.Proof.Ed448.AArch64.Sparse
