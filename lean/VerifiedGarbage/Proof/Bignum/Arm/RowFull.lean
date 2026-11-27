module

public import VerifiedGarbage.Impl.Bignum.Arm.RowFull
public import VerifiedGarbage.Proof.Bignum.Arm.RowState
import VerifiedGarbage.Proof.Bignum.Arm.Row
import VerifiedGarbage.Proof.Bignum.Arm.RowCarryMemory
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Impl.Bignum.Arm.RowCarry
import VerifiedGarbage.Proof.Bignum.Arm.Mac
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Block

/-! ### `Bignum.Arm.RowCarry`, which this module and modules that import it used -/

section

/-! # Correctness of the two-word carry propagation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str)

/-- Carry propagation writes only the two top words and preserves the
pointers and scalar. The exact sum includes any carry from the low word. -/
theorem rowCarry_ok (s : State) (lo hi : Addr)
    (hlo : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = lo)
    (hhi : State.addr (s.gpr .r0 + BitVec.ofNat 32 4) = hi)
    (wl : InRegions s.wr lo 4) (wh : InRegions s.wr hi 4)
    (hfit : (s.mem.readW lo 32).toNat + (s.mem.readW hi 32).toNat * 2 ^ 32 +
      (s.gpr .r11).toNat < 2 ^ 64) :
    WP isa rowCarry s fun t =>
      (t.gpr .r3).toNat + (t.gpr .r4).toNat * 2 ^ 32 =
        (s.mem.readW lo 32).toNat + (s.mem.readW hi 32).toNat * 2 ^ 32 + (s.gpr .r11).toNat ∧
      t.mem = (s.mem.writeW lo (t.gpr .r3)).writeW hi (t.gpr .r4) ∧ Rest [.r3, .r4] s t := by
  have rl : InRegions (s.rd ++ s.wr) lo 4 := by
    rcases wl with ⟨R, hR, hsub⟩; exact ⟨R, List.mem_append_right _ hR, hsub⟩
  have rh : InRegions (s.rd ++ s.wr) hi 4 := by
    rcases wh with ⟨R, hR, hsub⟩; exact ⟨R, List.mem_append_right _ hR, hsub⟩
  rw [rowCarry, WP.seq_iff]
  refine wp_ldr (by decide) hlo rl fun s1 u1 => ?_
  refine wp_ldr (a := hi) (by decide) (by rw [u1.other .r0 (by decide)]; exact hhi)
    (by rw [u1.rd, u1.wr]; exact rh) fun s2 u2 => ?_
  apply WP.block_nil
  have low : s2.gpr .r3 = s.mem.readW lo 32 := (u2.other .r3 (by decide)).trans u1.gpr
  have high : s2.gpr .r4 = s.mem.readW hi 32 := by rw [u2.gpr, u1.mem]
  have carry : s2.gpr .r11 = s.gpr .r11 :=
    (u2.other .r11 (by decide)).trans (u1.other .r11 (by decide))
  rw [WP.seq_iff]
  refine WP.mono (addWord_ok s2 .r11 (by rw [low, high, carry]; exact hfit)) ?_
  rintro s3 ⟨value, keep⟩
  have ptr : s3.gpr .r0 = s.gpr .r0 := (keep.regs .r0 (by simp)).trans
    ((u2.other .r0 (by decide)).trans (u1.other .r0 (by decide)))
  have mem3 : s3.mem = s.mem := keep.mem.trans (u2.mem.trans u1.mem)
  have wr3 : s3.wr = s.wr := keep.wr.trans (u2.wr.trans u1.wr)
  refine wp_str (a := lo) (by decide) (by rw [ptr]; exact hlo)
    (by rw [wr3]; exact wl) fun s4 u4 => ?_
  refine wp_str (a := hi) (by decide) (by rw [u4.gpr, ptr]; exact hhi)
    (by rw [u4.wr, wr3]; exact wh) fun s5 u5 => WP.block_nil ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [u5.gpr, u4.gpr, value, low, high, carry]
  · rw [u5.mem, u4.mem, mem3, u5.gpr, u4.gpr]
  · have k3 : Rest [.r3, .r4] s2 s3 := ⟨keep.regs, keep.rd, keep.wr, keep.sp⟩
    exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans (k3.trans ((u4.rest _).trans (u5.rest _))))

end VG.Proof.Bignum.Arm

end

end

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
  have tops := inv.outside.val32 (d := o + 4 * n) (k := 2) (by omega_using []) (by omega_using [hspace, nowrap])
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
    exact VG.Arm.addr_add (by omega_using [hspace, nowrap])
  refine WP.mono (rowCarry_ok u _ _ (row_addr ctx inv.outPtr (by omega_using [hspace])) ahi
    (row_writable ctx inv.rest.wr (by omega_using [hspace])) (row_writable ctx inv.rest.wr (by omega_using [hspace])) ?_) ?_
  · simpa only [val32, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.mul_comm, w32] using topfit
  · rintro t ⟨value, mem, keep⟩
    have nowrap' : (State.addr base).toNat + size ≤ 2 ^ 32 := by
      simpa only [State.addr, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show base.toNat < 2 ^ 64 by have := base.isLt; omega_using [])] using nowrap
    obtain ⟨outside, whole⟩ := rowCarry_memory nowrap' hspace mem
    have vtop : (t.gpr .r3).toNat + 2 ^ 32 * (t.gpr .r4).toNat =
        val32 u.mem (State.addr base) (o + 4 * n) 2 + (u.gpr .r11).toNat := by
      simpa only [val32, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.mul_comm, w32] using value
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [whole, vtop]; exact total
    · exact (inv.outside.mono (Nat.le_refl _) (by omega_using [])).trans (outside.mono (by omega_using []) (by omega_using []))
    · exact (keep.gpr .r0 (by decide)).trans inv.outPtr
    · exact inv.rest.trans (keep.mono (by decide))

end VG.Proof.Bignum.Arm
