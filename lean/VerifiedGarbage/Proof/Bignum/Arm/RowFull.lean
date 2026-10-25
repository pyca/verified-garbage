module

public import VerifiedGarbage.Impl.Bignum.Arm.RowFull
public import VerifiedGarbage.Proof.Bignum.Arm.RowState
import VerifiedGarbage.Proof.Bignum.Arm.Row
import VerifiedGarbage.Proof.Bignum.Arm.RowCarryMemory
import VerifiedGarbage.Proof.Bignum.Arm.RowCarry
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # A complete scalar multiply-add in an extended accumulator -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem pow32_addtwo (n : Nat) : (2 : Nat) ^ (32 * (n + 2)) = 2 ^ (32 * n) * 2 ^ 64 := by
  rw [Nat.mul_add, Nat.pow_add]

theorem rowFull_ok (s : State) {base : BitVec 32} {size o b n : Nat}
    (ctx : RowCtx s base size o b n) (hn : 0 < n)
    (hspace : o + 4 * (n + 2) ≤ size)
    (hp0 : s.gpr .r0 = base + BitVec.ofNat 32 o)
    (hp12 : s.gpr .r12 = base + BitVec.ofNat 32 b)
    (hcount : s.gpr .lr = BitVec.ofNat 32 n)
    (hfit : val32 s.mem (State.addr base) o (n + 2) +
      (s.gpr .r1).toNat * val32 s.mem (State.addr base) b n + (s.gpr .r11).toNat <
        2 ^ (32 * (n + 2))) :
    WP isa rowFull s fun t =>
      val32 t.mem (State.addr base) o (n + 2) =
        val32 s.mem (State.addr base) o (n + 2) +
          (s.gpr .r1).toNat * val32 s.mem (State.addr base) b n + (s.gpr .r11).toNat ∧
      Outside (State.addr base) o (4 * (n + 2)) s.mem t.mem ∧
      t.gpr .r0 = base + BitVec.ofNat 32 (o + 4 * n) ∧ Rest loopClobbers s t := by
  have nowrap := ctx.nowrap
  rw [rowFull, WP.seq_iff]
  refine WP.mono (row_ok s ctx hn hp0 hp12 hcount) ?_
  intro u inv
  have tops := inv.outside.val32 (d := o + 4 * n) (k := 2) (by omega) (by omega)
  have total : val32 u.mem (State.addr base) o n + 2 ^ (32 * n) *
      (val32 u.mem (State.addr base) (o + 4 * n) 2 + (u.gpr .r11).toNat) =
      val32 s.mem (State.addr base) o (n + 2) +
        (s.gpr .r1).toNat * val32 s.mem (State.addr base) b n + (s.gpr .r11).toNat := by
    rw [tops, val32_append s.mem (State.addr base) o n 2]
    have value := inv.value
    generalize 2 ^ (32 * n) = P at *
    grind
  have topfit : val32 u.mem (State.addr base) (o + 4 * n) 2 + (u.gpr .r11).toNat < 2 ^ 64 := by
    rw [← total, pow32_addtwo] at hfit
    exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hfit)
  have ahi : State.addr (u.gpr .r0 + BitVec.ofNat 32 4) =
      off (State.addr base) (o + 4 * n + 4) := by
    rw [inv.outPtr, Offset.add_add]
    exact VG.Arm.addr_add (by omega)
  refine WP.mono (rowCarry_ok u _ _ (row_addr ctx inv.outPtr (by omega)) ahi
    (row_writable ctx inv.rest.wr (by omega)) (row_writable ctx inv.rest.wr (by omega)) ?_) ?_
  · simpa only [val32, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.mul_comm, w32] using topfit
  · rintro t ⟨value, mem, keep⟩
    have nowrap' : (State.addr base).toNat + size ≤ 2 ^ 32 := by
      simpa only [State.addr, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show base.toNat < 2 ^ 64 by have := base.isLt; omega)] using nowrap
    obtain ⟨outside, whole⟩ := rowCarry_memory nowrap' hspace mem
    have vtop : (t.gpr .r3).toNat + 2 ^ 32 * (t.gpr .r4).toNat =
        val32 u.mem (State.addr base) (o + 4 * n) 2 + (u.gpr .r11).toNat := by
      simpa only [val32, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.mul_comm, w32] using value
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [whole, vtop]; exact total
    · exact (inv.outside.mono (Nat.le_refl _) (by omega)).trans (outside.mono (by omega) (by omega))
    · exact (keep.gpr .r0 (by decide)).trans inv.outPtr
    · exact inv.rest.trans (keep.mono (by decide))

end VG.Proof.Bignum.Arm
