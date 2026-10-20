module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Stack
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Stage

/-! # The saved bookkeeping corresponds to the caller's original header -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Impl.MillerRabin.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate

theorem entered_bookkeeping {s t : State} {B : Addr} (h : Staged B s t)
    (hn : 120 ≤ (t.gpr .rsp).toNat) : ∀ p ∈ restoreSlots,
    (entered t).mem.readW ((entered t).gpr .rsp + BitVec.ofNat 64 p.2) 64 = word s.mem B (8 * p.1) := by
  simp only [restoreSlots, List.mem_cons, List.not_mem_nil, or_false]
  rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · have ha : (entered t).gpr .rsp + 64#64 = t.gpr .rsp - BitVec.ofNat 64 (8 * (5 + 1)) := by
      rw [entered_rsp]
      bv_omega
    rw [ha]
    have hg : t.gpr saved[5] = t.gpr .rsi := rfl
    exact (entered_saved t hn (j := 5) (by decide +kernel)).trans
      (hg.trans (h (kOut, Reg.rsi) (by simp [bookkeeping])))
  · have ha : (entered t).gpr .rsp + 56#64 = t.gpr .rsp - BitVec.ofNat 64 (8 * (6 + 1)) := by
      rw [entered_rsp]
      bv_omega
    rw [ha]
    have hg : t.gpr saved[6] = t.gpr .rdx := rfl
    exact (entered_saved t hn (j := 6) (by decide +kernel)).trans
      (hg.trans (h (kLen, Reg.rdx) (by simp [bookkeeping])))
  · have ha : (entered t).gpr .rsp + 48#64 = t.gpr .rsp - BitVec.ofNat 64 (8 * (7 + 1)) := by
      rw [entered_rsp]
      bv_omega
    rw [ha]
    have hg : t.gpr saved[7] = t.gpr .rcx := rfl
    exact (entered_saved t hn (j := 7) (by decide +kernel)).trans
      (hg.trans (h (kUsedP, Reg.rcx) (by simp [bookkeeping])))
  · have ha : (entered t).gpr .rsp + 40#64 = t.gpr .rsp - BitVec.ofNat 64 (8 * (8 + 1)) := by
      rw [entered_rsp]
      bv_omega
    rw [ha]
    have hg : t.gpr saved[8] = t.gpr .r8 := rfl
    exact (entered_saved t hn (j := 8) (by decide +kernel)).trans
      (hg.trans (h (kRand, Reg.r8) (by simp [bookkeeping])))
  · have ha : (entered t).gpr .rsp + 32#64 = t.gpr .rsp - BitVec.ofNat 64 (8 * (9 + 1)) := by
      rw [entered_rsp]
      bv_omega
    rw [ha]
    have hg : t.gpr saved[9] = t.gpr .r9 := rfl
    exact (entered_saved t hn (j := 9) (by decide +kernel)).trans
      (hg.trans (h (kRandLen, Reg.r9) (by simp [bookkeeping])))
  · have ha : (entered t).gpr .rsp + 24#64 = t.gpr .rsp - BitVec.ofNat 64 (8 * (10 + 1)) := by
      rw [entered_rsp]
      bv_omega
    rw [ha]
    have hg : t.gpr saved[10] = t.gpr .rax := rfl
    exact (entered_saved t hn (j := 10) (by decide +kernel)).trans
      (hg.trans (h (kChecks, Reg.rax) (by simp [bookkeeping])))
  · have ha : (entered t).gpr .rsp + 16#64 = t.gpr .rsp - BitVec.ofNat 64 (8 * (11 + 1)) := by
      rw [entered_rsp]
      bv_omega
    rw [ha]
    have hg : t.gpr saved[11] = t.gpr .r10 := rfl
    exact (entered_saved t hn (j := 11) (by decide +kernel)).trans
      (hg.trans (h (kI, Reg.r10) (by simp [bookkeeping])))
  · have ha : (entered t).gpr .rsp + 8#64 = t.gpr .rsp - BitVec.ofNat 64 (8 * (12 + 1)) := by
      rw [entered_rsp]
      bv_omega
    rw [ha]
    have hg : t.gpr saved[12] = t.gpr .r11 := rfl
    exact (entered_saved t hn (j := 12) (by decide +kernel)).trans
      (hg.trans (h (kUsed, Reg.r11) (by simp [bookkeeping])))

end VG.Proof.MillerRabin.X86_64
