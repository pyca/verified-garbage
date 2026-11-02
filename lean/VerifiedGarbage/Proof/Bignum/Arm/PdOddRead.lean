module

public import VerifiedGarbage.Impl.Bignum.Arm.PdChecks
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # Load the modulus's low byte and the public sanity-check bit -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt)
open VG.Proof.X25519.Arm (Rest wp_ldr wp_ldrb)

theorem pdOddRead_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : LayoutFrameReady base len w s) (fit : s.sp.toNat + 52 ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 48) 4) :
    WP isa pdOddRead s fun t =>
      t.gpr .r1 = (s.mem (off (State.addr base) (arrAt w 0))).setWidth 32 ∧
      t.gpr .r11 = s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      t.mem = s.mem ∧ Rest [.r1, .r11] s t := by
  have nowrap := h.workspace.nowrap
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have end0 := array_end_le (w := w) (by decide : 0 < 8)
  have small : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have header := nativeHeader_of_layout s.mem base nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  rw [pdOddRead, WP.seq_iff]
  refine wp_ldr (a := off (State.addr base) 64) (by decide)
    (by rw [h.ptr]; exact addr_add (by omega)) (h.workspace.read (by omega)) fun u a => WP.block_nil ?_
  have ptrU : u.gpr .r1 = base + BitVec.ofNat 32 (arrAt w 0) := a.gpr.trans (header.array 0 (by decide))
  rw [WP.seq_iff]
  refine wp_ldrb (a := off (State.addr base) (arrAt w 0)) (by decide)
    (by rw [ptrU, BitVec.add_zero]; exact addr_add (by omega))
    (by rw [a.rd, a.wr]; exact ⟨_, List.mem_append_right _ h.workspace.writable,
      Offset.contains_base _ (by omega) (by omega)⟩) fun v b => WP.block_nil ?_
  refine wp_loadStack (a := off (State.addr s.sp) 48) (by decide)
    (by rw [b.sp, a.sp]; exact addr_add (by omega))
    (by rw [b.rd, b.wr, a.rd, a.wr]; exact read) fun t c => WP.block_nil ?_
  exact ⟨by rw [c.other .r1 (by decide), b.gpr, a.mem],
    by rw [c.gpr, b.mem, a.mem], c.mem.trans (b.mem.trans a.mem),
    (a.rest (by simp)).trans ((b.rest (by simp)).trans (c.rest (by simp)))⟩

end VG.Proof.Bignum.Arm
