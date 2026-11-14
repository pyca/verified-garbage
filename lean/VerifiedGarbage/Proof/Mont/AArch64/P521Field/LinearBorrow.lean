module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.LinearSum
public import VerifiedGarbage.Proof.Mont.AArch64.Csub
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.Block

/-! Borrow propagation with an explicit zero register. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

def linearBorrow (z : Reg) (rs : List Reg) : List Instr := rs.map fun r => .sbcs .x r r z

theorem linear_borrow_ok (z : Reg) : ∀ (rs : List Reg) (s : State),
    rs.Nodup → z∉rs → s.gpr z=0 →
    WP isa (.block (linearBorrow z rs)) s fun t =>
      regsVal t rs+(!s.c).toNat=regsVal s rs+2^(64*rs.length)*(!t.c).toNat ∧ Keeps rs s t
  | [], s, _, _, _ => WP.block_nil ⟨by simp [regsVal],fun _ _ => rfl,rfl,rfl,rfl,rfl⟩
  | r::rs, s, hn, hz, hv => by
    have hn' := List.nodup_cons.mp hn
    have hz' : z≠r ∧ z∉rs := by simpa only [List.mem_cons,not_or] using hz
    rw [linearBorrow,List.map_cons,←List.singleton_append,WP.block_append_iff]
    refine WP.mono (subc_ok s r r z false rfl) fun u ⟨eu,cu,ku⟩ => ?_
    simp only [Bool.false_eq_true,ite_false,hv] at eu cu
    have huz : u.gpr z=0 := (ku.gpr z (by simpa only [List.mem_singleton] using hz'.1)).trans hv
    change WP isa (.block (linearBorrow z rs)) u _
    refine WP.mono (linear_borrow_ok z rs u hn'.2 hz'.2 huz) fun t ⟨et,kt⟩ => ?_
    have htr : t.gpr r=u.gpr r := kt.gpr r hn'.1
    have hur : regsVal u rs=regsVal s rs := regsVal_congr fun q h =>
      ku.gpr q (by simp only [List.mem_singleton]; intro e; exact hn'.1 (e ▸ h))
    have eb := sub_borrow (s.gpr r) 0 s.c
    rw [←eu,←cu] at eb
    simp only [show (0 : BitVec 64).toNat=0 from rfl,Nat.add_zero] at eb
    rw [hur] at et
    refine ⟨?_,(ku.mono (by simp)).trans (kt.mono (fun _ h => List.mem_cons_of_mem _ h))⟩
    simp only [regsVal,List.length_cons,pow64_succ,htr,Nat.mul_assoc]
    have es := congrArg (fun n : Nat => 2^64*n) et
    simp only [Nat.mul_add] at es
    omega_using [es,eb]

theorem sbc_word_ok (s : State) (r m : Reg) :
    WP isa (.block [.sbc .x r r m]) s fun t =>
      t.gpr r=addCarry (s.gpr r) (~~~s.gpr m) s.c ∧ t.c=s.c ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,
    RegUpd.gpr_write,RegUpd.c_write,BitVec.setWidth_eq,
    Option.some.injEq,exists_eq_left']
  exact ⟨rfl,True.intro,⟨by intro q h; simp only [List.mem_singleton] at h; simp only [RegUpd.gpr_write,h,ite_false],
    by simp only [RegUpd.mem_write],by simp only [RegUpd.rd_write],
    by simp only [RegUpd.wr_write],by simp only [RegUpd.sp_write]⟩⟩

end VG.Proof.Mont.AArch64.P521Field
