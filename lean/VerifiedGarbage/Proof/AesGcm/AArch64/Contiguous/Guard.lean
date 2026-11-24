module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Leaves
import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.Guard
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Prepared

/-! Unsigned selection on nonce, AAD and plaintext sizes, preserving all
caller argument values and memory in either buffer arrangement. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Guard

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64.Contiguous
abbrev temps : List Reg := [.x9,.x10,.x11]

structure View (o t : State) : Prop where
  keep : Regs temps o t
  vec : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (o.v r).extractLsb' 0 64
  dit : t.dit=o.dit

theorem standard_ok (s : State) : WP isa (.block standardGuard) s fun t =>
    View s t ∧ (t.gpr .x10 = 0 ↔ standard s) := by
  have run : WP isa (.block standardGuard) s fun t => (t.gpr .x10 = 0 ↔ standard s) ∧ Regs temps s t := by
    refine WP.of_runBlock ⟨_,by unfold standardGuard; arun [gpr_addWithCarry,sp_addWithCarry,rd_addWithCarry,wr_addWithCarry,mem_addWithCarry],?_,?_⟩
    · simp only [gpr_write,gpr_addWithCarry,c_addWithCarry,Size.bits,BitVec.setWidth_eq,ite_true,ite_false,
        reduceCtorEq,Bool.toNat_true,BitVec.shiftLeft_zero,decide_eq_true_eq,standard]
      have aad : (~~~BitVec.setWidth 64 17#16).toNat = 2^64-18 := by decide
      simp only [aad]
      split
      · simp; omega
      · have eq := BitVec.sub_eq_iff_eq_add (x := s.gpr .x3) (y := 12) (z := 0)
        simp at eq
        exact ⟨fun h => ⟨congrArg BitVec.toNat (eq.mp h),by omega⟩,fun h => eq.mpr (BitVec.eq_of_toNat_eq h.1)⟩
    · refine ⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩
      simp only [temps,List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
      simp [gpr_write,gpr_addWithCarry,hr.1,hr.2.1,hr.2.2]
  obtain ⟨tr,t,exec,hit,keep⟩ := run
  exact ⟨tr,t,exec,⟨keep,Exec.preservedV exec (by lit_decide),Exec.dit (by lit_decide) exec⟩,hit⟩

abbrev limitCode (n : Nat) : List Instr :=
  [Impl.AesGcm.AArch64.imm .x9 n,.subs .x .x11 .x10 .x9,.sbc .x .x11 .x11 .x11]

theorem limit_ok {n : Nat} (bound : n=97 ∨ n=225 ∨ n=768 ∨ n=4096) (s : State) :
    WP isa (.block (limitCode n)) s fun t =>
      View s t ∧ t.gpr .x10 = s.gpr .x10 ∧ (t.gpr .x11 ≠ 0 ↔ (s.gpr .x10).toNat < n) := by
  have run : WP isa (.block (limitCode n)) s fun t => (t.gpr .x11 ≠ 0 ↔ (s.gpr .x10).toNat<n) ∧
      t.gpr .x10=s.gpr .x10 ∧ Regs temps s t := by
    refine WP.of_runBlock ⟨_,by unfold limitCode; arun [gpr_addWithCarry,sp_addWithCarry,rd_addWithCarry,wr_addWithCarry,mem_addWithCarry],?_,?_,?_⟩
    · simp only [gpr_write,gpr_addWithCarry,c_addWithCarry,Size.bits,BitVec.setWidth_eq,ite_true,ite_false,
        reduceCtorEq,Bool.toNat_true,BitVec.shiftLeft_zero]
      have threshold : (~~~BitVec.setWidth 64 (BitVec.ofNat 16 n)).toNat = 2^64-(n+1) := by rcases bound with rfl|rfl|rfl|rfl <;> decide
      rw [threshold]
      have mask (x : BitVec 64) : x + ~~~x = -1 := by
        rw [BitVec.not_eq_neg_add]
        change x + (-x - 1) = -1
        rw [BitVec.sub_eq_add_neg, ← BitVec.add_assoc, BitVec.add_neg_eq_sub (x := x) (y := x), BitVec.sub_self, BitVec.zero_add]
      rw [mask]
      simp only [Nat.reducePow] 
      by_cases h : (s.gpr .x10).toNat<n
      · have e : ¬ (18446744073709551615 ≤ (s.gpr .x10).toNat + (18446744073709551615-n)) := by
          rcases bound with rfl|rfl|rfl|rfl <;> omega
        simp [h,e]
      · have e : 18446744073709551615 ≤ (s.gpr .x10).toNat + (18446744073709551615-n) := by
          rcases bound with rfl|rfl|rfl|rfl <;> omega
        simp [h,e]
    · rfl
    · refine ⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩
      simp only [temps,List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
      simp [gpr_write,gpr_addWithCarry,hr.1,hr.2.2]
  obtain ⟨tr,t,exec,hit,x10,keep⟩ := run
  exact ⟨tr,t,exec,⟨keep,Exec.preservedV exec (by rcases bound with rfl|rfl|rfl|rfl <;> lit_decide),
    Exec.dit (by rcases bound with rfl|rfl|rfl|rfl <;> lit_decide) exec⟩,x10,hit⟩

end VG.Proof.AesGcm.AArch64.Contiguous.Guard
