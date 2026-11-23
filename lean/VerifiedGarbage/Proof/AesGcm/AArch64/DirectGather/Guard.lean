module

public import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather
public import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Unsigned size selection at entry, including near the address-space limit. -/

public section

namespace VG.Proof.AesGcm.AArch64.DirectGather

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64.DirectGather

theorem recordGuard_ok {limit : Nat} (bound : limit = 96 ∨ limit = 224) (s : State) (h : InRegions (s.rd ++ s.wr) (s.sp + 8) 8) :
    let n := (s.mem.readW (s.sp + 8) 64).toNat
    WP isa (.block (recordGuard limit)) s fun t =>
      (t.gpr .x10 = 0 ↔ s.gpr .x3 = 12 ∧ (s.gpr .x5).toNat ≤ 16 ∧ n ≤ limit) ∧
      Regs [.x9, .x10, .x11, .x12] s t := by
  change InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 at h
  dsimp only
  refine WP.of_runBlock ⟨_, by
    unfold recordGuard
    arun [h, gpr_addWithCarry, sp_addWithCarry, rd_addWithCarry, wr_addWithCarry, mem_addWithCarry], ?_, ?_⟩
  · simp only [gpr_write, gpr_addWithCarry, c_addWithCarry,
      Size.bits, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
      Bool.toNat_true, BitVec.shiftLeft_zero, Mem.readW]
    have threshold : (~~~BitVec.setWidth 64 (BitVec.ofNat 16 (limit+1))).toNat = 2^64 - (limit+2) := by
      rcases bound with rfl | rfl <;> decide
    have nz : BitVec.setWidth 64 (BitVec.ofNat 16 (limit+1)) ≠ 0 := by rcases bound with rfl | rfl <;> decide
    have aadThreshold : (~~~BitVec.setWidth 64 17#16).toNat = 2^64-18 := by decide
    have small : limit ≤ 224 := by omega
    simp only [decide_eq_true_eq,threshold,aadThreshold,Nat.reduceDiv]
    change _ ↔ _ ∧ _ ∧ (s.mem.read (s.sp+8#64) 8).toNat ≤ limit
    split
    · simp only [nz,false_iff,not_and]; omega
    · split
      · simp; omega
      · have eq := BitVec.sub_eq_iff_eq_add (x := s.gpr .x3) (y := 12) (z := 0)
        simp at eq
        exact ⟨fun h => ⟨eq.mp h,by omega,by change (s.mem.read (s.sp+8#64) 8).toNat ≤ limit; omega⟩,
          fun h => eq.mpr h.1⟩
  · refine ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h₉, h₁₀, h₁₁, h₁₂⟩ := hr
    simp [gpr_write, gpr_addWithCarry, h₉, h₁₀, h₁₁, h₁₂]

end VG.Proof.AesGcm.AArch64.DirectGather
