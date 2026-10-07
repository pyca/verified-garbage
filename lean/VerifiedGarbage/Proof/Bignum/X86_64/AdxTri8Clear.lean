import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Rows
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Math

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem clear_ok (rs : List Reg) (s : State) :
    WP isa (.block (rs.map (fun r => Instr.mov32 r (.imm 0)))) s fun t =>
      (∀ r∈rs, t.gpr r=0) ∧ t.mem=s.mem ∧ Keep rs s t := by
  induction rs generalizing s with
  | nil => exact WP.block_nil ⟨fun _ h => False.elim (List.not_mem_nil h),rfl,Keep.refl _ _⟩
  | cons r rs ih =>
    rw [List.map_cons,show Instr.mov32 r (.imm 0)::rs.map (fun r => Instr.mov32 r (.imm 0))=
      [Instr.mov32 r (.imm 0)]++rs.map (fun r => Instr.mov32 r (.imm 0)) from rfl,WP.block_append_iff]
    refine WP.mono (movZero_ok s r) fun a ⟨za,_,_,ka⟩ => ?_
    refine WP.mono (ih a) fun t ⟨zt,mt,kt⟩ => ?_
    refine ⟨?_,mt.trans ka.2.1,(ka.keep.trans kt).mono (by simp)⟩
    intro q hq
    rcases List.mem_cons.mp hq with eq | hq
    · subst q
      by_cases hr : r∈rs
      · exact zt r hr
      · exact (kt.gpr hr).trans za
    · exact zt q hq

theorem value_zero {s : State} {rs : List Reg} (h : ∀ r∈rs, s.gpr r=0) : value s rs=0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [value,h r (by simp),ih (fun q hq => h q (by simp [hq]))]
    rfl

theorem value_zero_lt {s : State} {rs : List Reg} (h : ∀ r∈rs, s.gpr r=0) (n : Nat) :
    value s rs<2^(64*n) := by
  rw [value_zero h]
  exact Nat.two_pow_pos (64*n)

theorem columns_regs : Regs AdxTri8.columns := by
  unfold Regs Safe AdxTri8.columns
  decide

end VG.Proof.Bignum.X86_64.AdxTri8
