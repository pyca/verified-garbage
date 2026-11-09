module

-- separate module: bounded scalar mux execution is checked separately from the recursive word-array induction

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishZeroMask
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.StreamMemory
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-! One branchless ordinate word in the canonical projective infinity fix. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Ed25519.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

def finishYArith (first : Bool) : List Instr := [
  .bicRor .x .x9 .x9 .x2 0,
  .movz .x .x4 (if first then 1 else 0) 0,
  .movk .x .x4 0 1,.movk .x .x4 0 2,.movk .x .x4 0 3,
  .logic .and .x .x4 .x4 .x2,.logic .orr .x .x4 .x4 .x9]

theorem finish_y_arith_ok (s : State) (first chooseOne : Bool)
    (mask : s.gpr .x2=if chooseOne then BitVec.allOnes 64 else 0#64) :
    WP isa (.block (finishYArith first)) s fun t =>
      t.gpr .x4=(if chooseOne then (if first then 1#64 else 0#64) else s.gpr .x9) ∧
      Keeps [.x9,.x4] s t := by
  cases first <;> cases chooseOne <;>
    apply WP.of_runBlock <;>
    simp only [finishYArith,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
      Nat.reduceLT,Nat.reduceMul,BitVec.shiftLeft_zero,RegUpd.gpr_write,BitVec.setWidth_eq,
      mask,reduceCtorEq,ite_true,ite_false,Option.some.injEq,exists_eq_left']
  all_goals refine ⟨?_,⟨?_,?_,?_,?_,?_⟩⟩
  all_goals try rfl
  all_goals try reg_keeps
  all_goals try simp
  all_goals first | exact BitVec.and_allOnes | decide

def finishYWord (o : Nat) (first : Bool) : List Instr :=
  [.ldr .x .x9 .x0 o]++finishYArith first++[.str .x .x4 .x0 o]

theorem finish_y_word_ok {s : State} {base : Addr} {W o : Nat} (hs : Scr s base W)
    (ho : o+8≤W) (ho8 : o%8=0) (first chooseOne : Bool)
    (mask : s.gpr .x2=if chooseOne then BitVec.allOnes 64 else 0#64) :
    WP isa (.block (finishYWord o first)) s fun t =>
      t.mem=s.mem.writeW (off base o)
        (if chooseOne then (if first then 1#64 else 0#64) else word s.mem base o) ∧
      KeepRegs [.x9,.x4] s t := by
  rw [finishYWord,List.append_assoc,WP.block_append_iff]
  refine WP.mono (ldR_ok hs.ptr ho ho8 .x9) fun u ⟨eu,ku,_⟩ => ?_
  rw [WP.block_append_iff]
  have mu : u.gpr .x2=if chooseOne then BitVec.allOnes 64 else 0#64 := by
    rw [ku.gpr .x2 (by decide),mask]
  refine WP.mono (finish_y_arith_ok u first chooseOne mu) fun v ⟨ev,kv⟩ => ?_
  have hv : Scr v base W := (hs.of_keeps ku (by decide)).of_keeps kv (by decide)
  refine WP.mono (stR_ok hv.ptrW ho ho8 .x4) fun t et => ?_
  have k : Keeps [.x9,.x4] s v := (ku.mono (by simp)).trans kv
  refine ⟨?_,?_⟩
  · rw [et,ev,eu,kv.mem,ku.mem]
  · rw [et]
    exact ⟨k.gpr,k.rd,k.wr,k.sp⟩

end VG.Proof.Weierstrass.AArch64.P521Native
