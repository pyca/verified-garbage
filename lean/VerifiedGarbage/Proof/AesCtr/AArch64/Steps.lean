import VerifiedGarbage.Proof.AesCtr.Inc
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.AesCbc.AArch64.Body
import VerifiedGarbage.Impl.AesCtr.AArch64

/-!
# AES-CTR on AArch64: the code between the calls

The straight-line pieces of a block, run once each: the arguments of the
call on the copy of the counter block (`args`), the output block XORed
into the data block (`xorOut`), and the increment of the counter block
(`incr`, whose block is `Spec.Ctr.inc` of the one it read: `incMem_bytes`).
-/

namespace VG.Proof.AesCtr.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCtr.AArch64
open VG.Impl.AesCbc.AArch64 (mov cOff copy)
open VG.Proof.AesCbc (xorMem)
open VG.Spec.Aes (bytesAt)

/-- The arguments of the call on the copy of the counter block. -/
def args : List Instr := [mov .x0 .x19, mov .x1 .x20, .addImm .x .x2 .x24 2048, .movz .x .x3 1 0, mov .x4 .x24]

theorem pre_eq : pre = copy .x24 cOff .x21 0 ++ args := rfl

theorem args_ok (s : State) :
    ∃ s', runBlock isa args s = some s' ∧
      s'.gpr .x0 = s.gpr .x19 ∧ s'.gpr .x1 = s.gpr .x20 ∧ s'.gpr .x2 = s.gpr .x24 + BitVec.ofNat 64 2048 ∧
      s'.gpr .x3 = 1 ∧ s'.gpr .x4 = s.gpr .x24 ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [args, exec_addImm_x (show 2048 < 4096 by decide)], ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], ?_, by simp [gpr_write],
    fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp [gpr_write]
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]

/-- The block at `x22` XORed with the one in the scratch buffer. -/
theorem xorOut_ok (s : State) {P Q : Addr} (hp : s.gpr .x22 = P) (hq : s.gpr .x24 + BitVec.ofNat 64 2048 = Q)
    (hq8 : s.gpr .x24 + BitVec.ofNat 64 (2048 + 8) = Q + BitVec.ofNat 64 8)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rp8 : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 8) 8)
    (rq : InRegions (s.rd ++ s.wr) Q 8) (rq8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (wp : InRegions s.wr P 8) (wp8 : InRegions s.wr (P + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa xorOut s = some s' ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = xorMem s.mem P Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [xorOut, cOff, hp, hq, hq8, rp, rp8, rq, rq8, wp, wp8], ?_⟩
  refine ⟨fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, ?_, rfl, rfl⟩
  simp only [xorMem, Mem.writeW, Mem.readW, BitVec.setWidth_eq]

/-- The memory after `incr` on the block at `Q`. -/
def incMem (m : Mem) (Q : Addr) : Mem :=
  let lo := rev64 (m.readW (Q + BitVec.ofNat 64 8) 64)
  let hi := rev64 (m.readW Q 64)
  let c := decide (2 ^ 64 ≤ lo.toNat + (1 : BitVec 64).toNat + (false).toNat)
  (m.writeW (Q + BitVec.ofNat 64 8) (rev64 (lo + 1 + BitVec.ofNat 64 (false).toNat))).writeW Q
    (rev64 (hi + 0 + BitVec.ofNat 64 c.toNat))

theorem incr_ok (s : State) {Q : Addr} (hq : s.gpr .x21 = Q)
    (r0 : InRegions (s.rd ++ s.wr) Q 8) (r8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (w0 : InRegions s.wr Q 8) (w8 : InRegions s.wr (Q + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa incr s = some s' ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = incMem s.mem Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [incr, gpr_addWithCarry, c_addWithCarry, c_write, mem_addWithCarry, rd_addWithCarry,
    wr_addWithCarry, sp_addWithCarry, hq, r0, r8, w0, w8], ?_⟩
  refine ⟨fun r h₁ h₂ h₃ h₄ => by simp [gpr_write, gpr_addWithCarry, h₁, h₂, h₃, h₄], rfl, ?_, rfl, rfl⟩
  rfl

theorem incMem_bytes (m : Mem) (Q : Addr) : bytesAt (incMem m Q) Q 16 = Spec.Ctr.inc (bytesAt m Q 16) := by
  apply AesCtr.inc_words64
  · show (rev64 _ + 1 + BitVec.ofNat 64 (false).toNat).toNat = ((rev64 _).toNat + 1) % 2 ^ 64
    rw [BitVec.toNat_add, BitVec.toNat_add]
    simp only [Bool.toNat_false, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero, Nat.mod_mod]
    rfl
  · show (rev64 _ + 0 + _).toNat = ((rev64 _).toNat + ((rev64 _).toNat + 1) / 2 ^ 64) % 2 ^ 64
    generalize rev64 (m.readW (Q + BitVec.ofNat 64 8) 64) = L
    generalize rev64 (m.readW Q 64) = H
    have hL := L.isLt
    have e₀ : (0 : BitVec 64).toNat = 0 := rfl
    have e₁ : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, BitVec.toNat_add, e₀, e₁, BitVec.toNat_ofNat]
    by_cases h : 2 ^ 64 ≤ L.toNat + 1 + (false).toNat
    · rw [decide_eq_true h]
      simp only [Bool.toNat_false, Bool.toNat_true] at h ⊢
      rw [show (L.toNat + 1) / 2 ^ 64 = 1 by omega]
      omega
    · rw [decide_eq_false h]
      simp only [Bool.toNat_false] at h ⊢
      rw [show (L.toNat + 1) / 2 ^ 64 = 0 by omega]
      omega

theorem incMem_frame (m : Mem) (Q : Addr) : Frame [⟨Q, 16⟩] m (incMem m Q) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains_base Q (d := 8) (n := 8) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (by simpa using Offset.contains_base Q (d := 0) (n := 8) (k := 16) (by decide) (by decide))

end VG.Proof.AesCtr.AArch64
