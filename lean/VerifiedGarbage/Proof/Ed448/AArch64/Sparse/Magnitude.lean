module

public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Joint
public import VerifiedGarbage.Proof.X448.AArch64.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

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
  refine ⟨(d+127).toNat,?_,?_⟩ <;> omega

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
