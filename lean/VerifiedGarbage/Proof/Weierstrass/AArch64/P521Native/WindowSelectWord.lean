module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedSelectLoads
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! The measured branchless word mux used for both exceptional window cases. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field

def windowSelectArith : List Instr := [
  .logic .eor .x .x2 .x2 .x1,
  .logic .and .x .x2 .x2 .x3,
  .logic .eor .x .x1 .x1 .x2]

theorem window_select_arith (s : State) (takeB : Bool)
    (mask : s.gpr .x3=if takeB then BitVec.allOnes 64 else 0) :
    WP isa (.block windowSelectArith) s fun t =>
      t.gpr .x1=(if takeB then s.gpr .x2 else s.gpr .x1) ∧
      Keeps [.x1,.x2] s t ∧ t.v=s.v ∧ t.zf=s.zf := by
  apply WP.of_runBlock
  simp only [windowSelectArith,runBlock_cons,runStep_some,runBlock_nil,reduceExec,Size.bits,read_x,
    RegUpd.gpr_write,RegUpd.v_write,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨?_,by simp only [RegUpd.mem_write],by simp only [RegUpd.rd_write],
    by simp only [RegUpd.wr_write],by simp only [RegUpd.sp_write]⟩,trivial,rfl⟩
  · rw [mask]
    cases takeB
    · change s.gpr .x1 ^^^ ((s.gpr .x2 ^^^ s.gpr .x1) &&& 0#64)=s.gpr .x1
      rw [BitVec.and_zero,BitVec.xor_zero]
    · change s.gpr .x1 ^^^ ((s.gpr .x2 ^^^ s.gpr .x1) &&& BitVec.allOnes 64)=s.gpr .x2
      rw [BitVec.and_allOnes,BitVec.xor_comm (s.gpr .x2),←BitVec.xor_assoc,
        BitVec.xor_self,BitVec.zero_xor]
  · reg_keeps

def windowSelectWord (a b o : Nat) : List Instr :=
  [.ldr .x .x1 .x0 a,.ldr .x .x2 .x0 b]++windowSelectArith++[.str .x .x1 .x0 o]

theorem window_select_word {s : State} {base : Addr} {size a b o : Nat}
    (hs : Scr s base size) (ha : a+8≤size) (hb : b+8≤size) (ho : o+8≤size)
    (ha8 : a%8=0) (hb8 : b%8=0) (ho8 : o%8=0) (takeB : Bool)
    (mask : s.gpr .x3=if takeB then BitVec.allOnes 64 else 0) :
    WP isa (.block (windowSelectWord a b o)) s fun t =>
      t.mem=s.mem.writeW (off base o) (if takeB then word s.mem base b else word s.mem base a) ∧
      KeepRegs [.x1,.x2] s t := by
  rw [windowSelectWord,List.append_assoc,WP.block_append_iff]
  change WP isa (.block ([.ldr .x .x1 .x0 a]++[.ldr .x .x2 .x0 b])) s _
  rw [WP.block_append_iff]
  refine WP.mono (ldR_ok hs.ptr ha ha8 .x1) fun u ⟨e1,k1,_⟩ => ?_
  have hu : Scr u base size := hs.of_keeps k1 (by decide)
  refine WP.mono (ldR_ok hu.ptr hb hb8 .x2) fun v ⟨e2,k2,_⟩ => ?_
  rw [WP.block_append_iff]
  have vm : v.gpr .x3=if takeB then BitVec.allOnes 64 else 0 := by
    rw [k2.gpr .x3 (by decide),k1.gpr .x3 (by decide),mask]
  refine WP.mono (window_select_arith v takeB vm) fun w ⟨ew,kw,_,_⟩ => ?_
  have hw : Scr w base size := (hu.of_keeps k2 (by decide)).of_keeps kw (by decide)
  refine WP.mono (stR_ok hw.ptrW ho ho8 .x1) fun t et => ?_
  have k : Keeps [.x1,.x2] s w :=
    (k1.mono (by simp)).trans ((k2.mono (by simp)).trans kw)
  refine ⟨?_,?_⟩
  · rw [et,ew,e2,k2.gpr .x1 (by decide),e1,kw.mem,k2.mem,k1.mem]
  · rw [et]
    exact ⟨k.gpr,k.rd,k.wr,k.sp⟩

end VG.Proof.Weierstrass.AArch64.P521Native
