module

-- separate module: the bounded ABI argument-shuffle proof is independent of the region-membership precondition adapter

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.PrepareLoad
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-! The native prefix obtains its public table pointer and shuffles API arguments. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Ed25519.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native (outerBlock001)

theorem prepare_args_ok (s : State) :
    WP isa (.block (outerBlock001.take 5)) s fun t =>
      t.gpr .x26=s.sp ∧ t.gpr .x4=s.gpr .x3 ∧ t.gpr .x6=s.gpr .x2 ∧ t.gpr .x3=s.gpr .x1 ∧
      t.gpr .x2=s.gpr .x2+BitVec.ofNat 64 1 ∧ Keeps [.x2,.x3,.x4,.x6,.x26] s t ∧ t.v=s.v := by
  rw [prepare_args_source]
  apply WP.of_runBlock
  simp only [VG.Impl.Ecdh.AArch64.Cfg.args,List.cons_append,List.nil_append,runBlock_cons,
    runStep_some,runBlock_nil,reduceExec,read_x,RegUpd.gpr_write,BitVec.setWidth_eq,BitVec.add_zero,
    reduceCtorEq,ite_true,ite_false,show (0 : Nat)<4096 from by decide,show (1 : Nat)<4096 from by decide,
    Option.some.injEq,exists_eq_left']
  refine ⟨True.intro,True.intro,True.intro,True.intro,True.intro,⟨?_,?_,?_,?_,?_⟩,?_⟩
  · reg_keeps
  · simp only [RegUpd.mem_write]
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [RegUpd.sp_write]
  · simp only [RegUpd.v_write]

end VG.Proof.Weierstrass.AArch64.P521Native
