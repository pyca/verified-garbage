module

public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Joint
public import VerifiedGarbage.Proof.X448.AArch64.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Recode

/-! ### `Ed448.AArch64.Sparse.DigitLoads`, which the modules that import this one used -/

section

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
    exact congrArg (fun n => base+BitVec.ofNat 64 n) (by omega_using [])
  have hr:=hs.read (d:=BITS+i) (n:=1) (by simp only [BITS];omega_using [hi])
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
    exact congrArg (fun n => base+BitVec.ofNat 64 n) (by simp only [SDIG];omega_using [])
  have hr:=hs.read (d:=SDIG+i) (n:=1) (by simp only [SDIG];omega_using [hi])
  apply WP.of_runBlock
  simp only [baseDigit,runBlock_cons,runStep_some,runBlock_nil,exec,State.read,Size.bits,
    addr,Nat.reduceMul,Nat.reduceLT,Nat.mod_one,and_self,RegUpd.gpr_write,RegUpd.rd_write,RegUpd.wr_write,RegUpd.mem_write,BitVec.setWidth_eq,hs.x3,hc,ha,
    BitVec.add_zero,State.load,hr,read1_eq,ite_true,ite_false,reduceCtorEq,Option.map_some,Option.bind_some,
    byte_zext,Option.some.injEq,exists_eq_left']
  refine ⟨by trivial,⟨fun r hr => ?_,rfl,rfl⟩,by trivial⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]

end VG.Proof.Ed448.AArch64.Sparse

end

end

/-! Signed-byte magnitudes and signs for public table addresses. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Proof.X448.AArch64 (Keeps)

private theorem mag_fact : ∀ (n:Nat),n<255 →
    let d: Int:=n-127
    let v:BitVec 64:=(BitVec.ofInt 8 d).setWidth 64
    v>>>7=BitVec.ofNat 64 (if d<0 then 1 else 0) ∧
    (if (v&&&128)==0 then v else 256-v)=BitVec.ofNat 64 d.natAbs := by decide +kernel

private theorem bounded_int {d:Int} (hd:-127≤d ∧ d≤127) :
    ∃ (n:Nat),n<255 ∧ d=(n:Int)-127 := by
  refine ⟨(d+127).toNat,?_,?_⟩ <;> omega_using [hd]

theorem encoded_zero {d:Int} (hd:-127≤d ∧ d≤127) :
    ((BitVec.ofInt 8 d).setWidth 64==0)=decide (d=0) := by
  have h:∀ (n:Nat),n<255 →
      ((BitVec.ofInt 8 ((n:Int)-127)).setWidth 64==0)=decide ((n:Int)-127=0) := by decide +kernel
  obtain ⟨n,hn,rfl⟩:=bounded_int hd
  exact h n hn

theorem magnitude_ok {s:State} {d:Int} (hd:-127≤d ∧ d≤127)
    (h11:s.gpr .x11=(BitVec.ofInt 8 d).setWidth 64) :
    WP isa (.block magnitude) s fun t =>
      t.gpr .x21=BitVec.ofNat 64 (if d<0 then 1 else 0) ∧
      t.gpr .x11=BitVec.ofNat 64 d.natAbs ∧ Keeps [.x21,.x9,.x8,.x11] s t ∧ t.mem=s.mem := by
  obtain ⟨n,hn,he⟩:=bounded_int hd
  have hf:=mag_fact n hn
  rw [←he] at hf
  apply WP.of_runBlock
  simp only [magnitude,runBlock_cons,runStep_some,runBlock_nil,exec,State.read,Size.bits,
    Nat.reduceLT,Nat.reduceMul,ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,h11,
    CondCode.holds,RegUpd.mem_write,RegUpd.rd_write,RegUpd.wr_write,
    ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,⟨fun r hr => ?_,rfl,rfl⟩,by trivial⟩
  · exact hf.1
  · change (if (!decide ((BitVec.ofInt 8 d).setWidth 64&&&128=0))=true then
        256-(BitVec.ofInt 8 d).setWidth 64 else (BitVec.ofInt 8 d).setWidth 64)=_
    by_cases h:(BitVec.ofInt 8 d).setWidth 64&&&128=0 <;> simpa [h] using hf.2
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2.1,hr.2.2.1,hr.2.2.2,ite_false]

end VG.Proof.Ed448.AArch64.Sparse
