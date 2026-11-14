module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowMixedCall
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowDoubleStep
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-! Exact mixed-call argument setup and complete measured BL protocol. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Impl.Weierstrass.AArch64.P521Native

 def windowMixedArgs : List Instr := [.movz .x .x1 1288 0,.movz .x .x2 1072 0,.movz .x .x3 1504 0]
 def windowMixedStep : Prog isa := .seq (.block windowMixedArgs) callNormalMadd

 theorem window_mixed_args_source : outerBlock142.drop 747=windowMixedArgs := by
  have h := drop_flatten_prefix outerBlock142Chunks 23 736 11
    (by rw [List.length_flatten]; lit_decide)
  rw [outerBlock142,h]
  decide

 theorem window_mixed_args_ok (s : State) :
    WP isa (.block windowMixedArgs) s fun t =>
      t.gpr .x1=1288#64 ∧ t.gpr .x2=1072#64 ∧ t.gpr .x3=1504#64 ∧
      Keeps [.x1,.x2,.x3] s t ∧ t.v=s.v := by
  apply WP.of_runBlock
  simp only [windowMixedArgs,runBlock_cons,runStep_some,runBlock_nil,reduceExec,Size.bits,Nat.reduceMul,
    Nat.reduceLT,ite_true,BitVec.shiftLeft_zero,RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,ite_false,
    Option.some.injEq,exists_eq_left']
  refine ⟨rfl,rfl,rfl,⟨?_,by simp only [RegUpd.mem_write],by simp only [RegUpd.rd_write],
    by simp only [RegUpd.wr_write],by simp only [RegUpd.sp_write]⟩,rfl⟩
  reg_keeps

 theorem window_mixed_step_ok {s : State} {W : Nat}
    (hs : Scr s (s.gpr .x0) W) (room : 4512≤W)
    (ca : canonicalPoint s.mem (s.gpr .x0) 1072) (ce : canonicalPoint s.mem (s.gpr .x0) 1504) :
    WP isa windowMixedStep s fun t =>
      canonicalPoint t.mem (s.gpr .x0) 1288 ∧ ordinaryPoint t.mem (s.gpr .x0) 1288=windowMixedValue s.mem (s.gpr .x0) ∧
      WindowMixedFrame (s.gpr .x0) s.mem t.mem ∧ WindowStable s t := by
  rw [windowMixedStep,WP.seq_iff]
  refine WP.mono (window_mixed_args_ok s) fun u ⟨o,a,b,ku,vu⟩ => ?_
  have u0 := ku.gpr .x0 (by decide)
  have hu : Scr u (u.gpr .x0) W := by rw [u0]; exact hs.of_keeps ku (by decide)
  have au : canonicalPoint u.mem (u.gpr .x0) 1072 := by rw [u0,ku.mem]; exact ca
  have bu : canonicalPoint u.mem (u.gpr .x0) 1504 := by rw [u0,ku.mem]; exact ce
  refine WP.mono (window_mixed_call_ok hu room o a b au bu)
    fun t ⟨bt,pt,ft,zero,rd,wr,sp,gp,v29,v31⟩ => ?_
  rw [u0] at bt pt ft zero
  rw [ku.mem] at pt ft
  have fresh : ∀r∈preserved,r∉[Reg.x1,Reg.x2,Reg.x3] := by decide
  exact ⟨bt,pt,ft,zero,rd.trans ku.rd,wr.trans ku.wr,sp.trans ku.sp,
    fun r hr hn => (gp r hr hn).trans (ku.gpr r (fresh r hr)),by rw [v29,vu],by rw [v31,vu]⟩

end VG.Proof.Weierstrass.AArch64.P521Native
