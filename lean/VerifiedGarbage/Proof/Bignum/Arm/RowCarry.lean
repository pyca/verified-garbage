module

public import VerifiedGarbage.Impl.Bignum.Arm.RowCarry
public import VerifiedGarbage.Proof.Bignum.Arm.Mac
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

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
