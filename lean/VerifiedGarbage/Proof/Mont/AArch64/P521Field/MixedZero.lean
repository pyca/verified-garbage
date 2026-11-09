module

-- separate module: The wordwise Z-zero detection and field-zero equivalence (mixed_zero_or_iff) costs 3.72s of proof versus 0.29s of imports; MixedSelectLoads composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedExit
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.LoadWords
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-! Exact zero-coordinate detector before the mixed point selection. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

def mixedZeroRegs : List Reg := [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8]
def mixedZeroCode : List Instr := ((mixedFnBlocks.drop 134).flatten.drop 9).take 19

theorem mixedZero_source : mixedZeroCode=(mixedFnBlocks.flatten.drop 4297).take 19 := by
  have h := drop_flatten_prefix mixedFnBlocks 134 4288 9
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 19) h.symm

def mixedZeroArith : List Instr := [
  .logic .orr .x .x0 .x0 .x1,.logic .orr .x .x2 .x2 .x3,
  .logic .orr .x .x4 .x4 .x5,.logic .orr .x .x6 .x6 .x7,
  .logic .orr .x .x0 .x0 .x2,.logic .orr .x .x4 .x4 .x6,
  .logic .orr .x .x0 .x0 .x4,.logic .orr .x .x0 .x0 .x8,
  .movz .x .x1 0 0,.subs .x .x2 .x0 .x1]

def mixedZeroOr (s : State) : Word :=
  (((s.gpr .x0|||s.gpr .x1)|||(s.gpr .x2|||s.gpr .x3))|||
    ((s.gpr .x4|||s.gpr .x5)|||(s.gpr .x6|||s.gpr .x7)))|||s.gpr .x8

theorem mixedZero_hoist : hoistLoads .x27 mixedZeroCode=some (loadsR .x27 mixedZeroRegs 144,mixedZeroArith) := by decide

theorem mixed_zero_arith (s : State) :
    WP isa (.block mixedZeroArith) s fun t =>
      t.zf=decide (mixedZeroOr s=0) ∧ Keeps [.x0,.x1,.x2,.x4,.x6] s t := by
  have zf (u : State) (a b : Word) (c : Bool) : (u.addWithCarry .x .x2 a b c).zf=decide (addCarry a b c=0) := rfl
  have addZero (x : Word) : addCarry x (~~~(0#64)) true=x := by
    change x+~~~(0 : Word)+1#64=x
    rw [BitVec.add_assoc,show ~~~(0 : Word)+1#64=0 from rfl]
    exact BitVec.add_zero x
  apply WP.of_runBlock
  simp only [mixedZeroArith,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,Nat.mul_zero,Nat.reduceLT,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,
    BitVec.shiftLeft_zero,Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨?_,?_,?_,?_,?_⟩⟩
  · rw [zf]
    change decide (addCarry (mixedZeroOr s) (~~~(0#64)) true=0#64)=decide (mixedZeroOr s=0#64)
    rw [addZero]
  · reg_keeps
  · simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry]
  · simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry]
  · simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry]
  · simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]

theorem mixed_zero_or_iff (s : State) : mixedZeroOr s=0#64 ↔ regsVal s mixedZeroRegs=0 := by
  have wordZero (w : Word) : w=0#64 ↔ w.toNat=0 := by
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact BitVec.eq_of_toNat_eq h
  simp only [mixedZeroOr,BitVec.or_eq_zero_iff]
  simp only [wordZero,mixedZeroRegs,regsVal,Nat.mul_zero,Nat.add_zero]
  omega_arith

theorem mixed_zero_ok {s : State} {p : Addr} {size : Nat} (hp : Ptr s .x27 p size) (hd : 216≤size) :
    WP isa (.block mixedZeroCode) s fun t =>
      t.zf=decide (wordsVal s.mem p 144 9=0) ∧ Keeps mixedZeroRegs s t := by
  apply WP.hoistLoads mixedZero_hoist
  rw [WP.block_append_iff]
  refine WP.mono (loadsR_ok mixedZeroRegs hp (by simpa only [show mixedZeroRegs.length=9 from rfl] using hd)
    (by decide) (by decide) (by decide)) fun u ⟨value,ku,_⟩ => ?_
  refine WP.mono (mixed_zero_arith u) fun t ⟨flag,kt⟩ => ?_
  have he : decide (mixedZeroOr u=0)=decide (regsVal u mixedZeroRegs=0) := decide_eq_decide.mpr (mixed_zero_or_iff u)
  rw [he,value] at flag
  exact ⟨flag,ku.trans (kt.mono (by decide))⟩

end VG.Proof.Mont.AArch64.P521Field
