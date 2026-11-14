module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.LinearPairs
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.StreamValue
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

theorem adc_word_ok (s : State) (r m : Reg) :
    WP isa (.block [.adc .x r r m]) s fun t =>
      t.gpr r=addCarry (s.gpr r) (s.gpr m) s.c ∧ t.c=s.c ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,
    RegUpd.gpr_write,RegUpd.c_write,BitVec.setWidth_eq,
    Option.some.injEq,exists_eq_left']
  exact ⟨rfl,True.intro,⟨by intro q h; simp only [List.mem_singleton] at h; simp only [RegUpd.gpr_write,h,ite_false],
    by simp only [RegUpd.mem_write],by simp only [RegUpd.rd_write],
    by simp only [RegUpd.wr_write],by simp only [RegUpd.sp_write]⟩⟩

def linearAddLast (rn r : Reg) (b : Nat) : List Instr := [.ldr .x .x4 rn b,.adc .x r r .x4]

theorem linear_add_last_ok {s : State} {rn r : Reg} {p : Addr} {size b : Nat}
    (hp : Ptr s rn p size) (hb : b+8≤size) (hb8 : b%8=0) (hr : r≠.x4) :
    WP isa (.block (linearAddLast rn r b)) s fun t =>
      t.gpr r=addCarry (s.gpr r) (word s.mem p b) s.c ∧ t.c=s.c ∧ Keeps [.x4,r] s t := by
  rw [linearAddLast,←List.singleton_append,WP.block_append_iff]
  refine WP.mono (ldR_ok hp hb hb8 .x4) fun u ⟨bu,ku,cu⟩ => ?_
  refine WP.mono (adc_word_ok u r .x4) fun t ⟨a,ct,kt⟩ => ?_
  rw [bu,cu,ku.gpr r (by simpa only [List.mem_singleton] using hr)] at a
  exact ⟨a,ct.trans cu,(ku.mono (by simp)).trans (kt.mono (by simp))⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

def linearPairs8 : List (Reg × Reg) := [(.x5,.x6),(.x7,.x8),(.x9,.x10),(.x11,.x12)]
def linearRegs8 : List Reg := pairRegs linearPairs8
def linearRegs9 : List Reg := linearRegs8++[.x13]
def linearSum (rn : Reg) (b : Nat) : List Instr :=
  linearAddPairs rn linearPairs8 b++linearAddLast rn .x13 (b+64)

theorem linear_sum_ok {s : State} {rn : Reg} {p : Addr} {size b : Nat}
    (hp : Ptr s rn p size) (hb : b+72≤size) (hb8 : b%8=0)
    (hr : rn∉[Reg.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13])
    (hs : regsVal s linearRegs9+wordsVal s.mem p b 9+s.c.toNat<2^576) :
    WP isa (.block (linearSum rn b)) s fun t =>
      regsVal t linearRegs9=regsVal s linearRegs9+wordsVal s.mem p b 9+s.c.toNat ∧
      Keeps (.x3::.x4::linearRegs9) s t := by
  have hr3 : rn≠.x3 := fun e => hr (by simp [e])
  have hr4 : rn≠.x4 := fun e => hr (by simp [e])
  rw [linearSum,WP.block_append_iff]
  refine WP.mono (linear_add_pairs_ok linearPairs8 hp (by change b+8*8≤size; omega_arith)
    hb8 (by decide) hr3 hr4 (by
      intro r h
      have hf : r∉[Reg.x3,.x4] := (by decide : ∀r∈pairRegs linearPairs8,r∉[Reg.x3,.x4]) r h
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hf ⊢
      exact ⟨hf.1,hf.2,fun e => hr ((by decide : ∀r∈pairRegs linearPairs8,r∈[Reg.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13]) rn (e ▸ h))⟩))
    fun u ⟨eu,ku⟩ => ?_
  have hpu := hp.of_keeps ku (by
    intro h
    exact hr ((by decide : ∀r∈.x3::.x4::pairRegs linearPairs8,r∈[Reg.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13]) rn h))
  refine WP.mono (linear_add_last_ok hpu (b:=b+64) (by omega_arith) (by omega_arith) (by decide))
    fun t ⟨et,ct,kt⟩ => ?_
  have hu13 : u.gpr .x13=s.gpr .x13 := ku.gpr .x13 (by decide)
  have ht8 : regsVal t linearRegs8=regsVal u linearRegs8 := regsVal_congr fun r h =>
    kt.gpr r ((by decide : ∀r∈linearRegs8,r∉[Reg.x4,.x13]) r h)
  have hlast := addCarry_value (u.gpr .x13) (word u.mem p (b+64)) u.c
  rw [←et,hu13,ku.mem] at hlast
  have hone : wordsVal s.mem p (b+64) 1=(word s.mem p (b+64)).toNat := by
    simp only [wordsVal,Nat.mul_zero,Nat.add_zero]
  have hsplit := wordsVal_split s.mem p b 8 1
  simp only [Nat.reduceAdd,Nat.reduceMul,hone] at hsplit
  have hfull : regsVal t linearRegs9+2^576*(carryOut (u.gpr .x13) (word u.mem p (b+64)) u.c).toNat=
      regsVal s linearRegs9+wordsVal s.mem p b 9+s.c.toNat := by
    rw [linearRegs9,regsVal_append,regsVal_append]
    have honeReg (v : State) : regsVal v [.x13]=(v.gpr .x13).toNat := by
      simp only [regsVal,Nat.mul_zero,Nat.add_zero]
    rw [honeReg,honeReg]
    simp only [show linearRegs8.length=8 from by decide,Nat.reduceMul]
    have hscaled := congrArg (fun n : Nat => 2^512*n) hlast
    simp only [Nat.mul_add,←Nat.mul_assoc] at hscaled
    have he : 2^512*2^64=2^576 := by lit_decide
    rw [he] at hscaled
    rw [ht8,hsplit,hu13,ku.mem]
    simp only [show (pairRegs linearPairs8).length=8 from by decide,Nat.reduceMul] at eu
    dsimp only [linearRegs8] at eu ⊢
    omega_using [eu,hscaled]
  refine ⟨by omega_using [hfull,hs],(ku.mono (by
    intro r h
    simp only [linearRegs9,List.mem_append,List.mem_cons] at ⊢
    simp only [List.mem_cons] at h
    rcases h with h|h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h)))).trans (kt.mono (by
      intro r h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl <;> simp [linearRegs9]))⟩

end VG.Proof.Mont.AArch64.P521Field
