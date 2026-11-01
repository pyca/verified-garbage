module

public import VerifiedGarbage.Impl.Bignum.Arm.R2Normalized
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady

import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Mont.Words32
/-! The normalized initializer sets R/2 and two without reading scratch contents. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/R2TopBit.lean`, which only this module imported.
section

/-! Write the public top radix bit using the existing array header. -/

section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_mov wp_str op2_lsl op2_imm dpVal)

theorem r2TopBit_ok (s : State) {base : BitVec 32} {size w d : Nat}
    (ws : Workspace s base size) (fit : 100 ≤ size) (hw : 0 < w)
    (arrayFit : d + 8 * w ≤ size) (ptr : s.gpr .r0 = base)
    (width : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w)
    (array : s.mem.readW (off (State.addr base) 96) 32 = base + BitVec.ofNat 32 d) :
    WP isa (.block r2TopBit) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) (d + 8 * w - 4)) (0x80000000 : BitVec 32) ∧
      Rest [.r1, .r4, .r5] s t := by
  have nowrap := ws.nowrap
  unfold r2TopBit
  refine wp_ldr (a := off (State.addr base) 96) (by decide)
    (by rw [ptr]; exact addr_add (by omega)) (ws.read (by omega)) fun s1 u1 => ?_
  refine wp_ldr (a := off (State.addr base) 48) (by decide)
    (by rw [u1.other .r0 (by decide), ptr]; exact addr_add (by omega))
    (by rw [u1.rd, u1.wr]; exact ws.read (off := 48) (by omega)) fun s2 u2 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s3 u3 => ?_
  refine wp_dp (op2_imm (by decide)) fun s4 u4 => ?_
  refine wp_mov (op2_imm (by decide)) fun s5 u5 => ?_
  have address : s5.gpr .r4 = base + BitVec.ofNat 32 (d + 8 * w - 4) := by
    rw [u5.other .r4 (by decide), u4.gpr, dpVal, u3.gpr, dpVal,
      u2.other .r4 (by decide), u1.gpr, array, u2.gpr, u1.mem, width,
      BitVec.shiftLeft_eq_mul_twoPow]
    change base + BitVec.ofNat 32 d + BitVec.ofNat 32 w * BitVec.ofNat 32 8 - BitVec.ofNat 32 4 = _
    rw [← BitVec.ofNat_mul, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [show d + w * 8 = (d + 8 * w - 4) + 4 by omega,
      BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_sub_cancel]
  refine wp_str (a := off (State.addr base) (d + 8 * w - 4)) (by decide)
    (by rw [address, BitVec.add_zero]; exact addr_add (by omega))
    (by rw [u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]; exact ws.write (by omega)) fun t u6 => WP.block_nil ?_
  refine ⟨?_, (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans
    ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans (u6.rest _)))))⟩
  rw [u6.mem, u5.gpr, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/TopBitMemory.lean`, which only this module imported.
section

/-! Set only the top bit of an otherwise zero packed-word array. -/

section
namespace VG.Proof.Bignum.Arm
open VG VG.Proof.Mont

theorem val32_write_top_of_zero (m : Mem) (base : Addr) {d n : Nat} (hn : 0 < n)
    (fit : d + 4 * n < 2 ^ 64) (zero : val32 m base d n = 0) (v : BitVec 32) :
    val32 (m.writeW (off base (d + 4 * (n - 1))) v) base d n =
      2 ^ (32 * (n - 1)) * v.toNat := by
  have split : n = (n - 1) + 1 := by omega
  have low : val32 m base d (n - 1) = 0 := by
    rw [split, val32_succ] at zero
    omega
  have outside := writeW32_outside m base (d := d + 4 * (n - 1)) v (by omega)
  calc
    _ = val32 (m.writeW (off base (d + 4 * (n - 1))) v) base d ((n - 1) + 1) := congrArg _ split
    _ = _ := by rw [val32_succ, w32_write_self,
    outside.val32 (d := d) (k := n - 1) (by omega) (by omega), low, Nat.zero_add]

theorem val32_write_top_bit (m : Mem) (base : Addr) {d w : Nat} (hw : 0 < w)
    (fit : d + 8 * w < 2 ^ 64) (zero : val32 m base d (2 * w) = 0) :
    val32 (m.writeW (off base (d + 8 * w - 4)) (0x80000000 : BitVec 32)) base d (2 * w) =
      2 ^ (64 * w - 1) := by
  have address : d + 8 * w - 4 = d + 4 * (2 * w - 1) := by omega
  rw [address, val32_write_top_of_zero m base (by omega) (by omega) zero]
  change 2 ^ (32 * (2 * w - 1)) * 2 ^ 31 = _
  rw [← Nat.pow_add]
  congr 1
  omega

end VG.Proof.Bignum.Arm
end

end

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem r2TopBitReady_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) (zero : numAt s.mem (State.addr base) w 4 = 0) :
    WP isa (.block r2TopBit) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (64 * w - 1) ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have arrayFits := Nat.le_trans (array_end_le (w := w) (by decide : 4 < 8)) fits
  have size : 100 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  refine WP.mono (r2TopBit_ok s h.workspace size (by omega) (by omega) h.ptr header.count
    (header.array 4 (by decide))) ?_
  rintro t ⟨mem, rest⟩
  have outside := writeW32_outside s.mem (State.addr base)
    (d := arrAt w 4 + 8 * w - 4) (0x80000000 : BitVec 32) (by have := h.workspace.nowrap; omega)
  rw [← mem] at outside
  have arrayOutside := outside.mono (show arrAt w 4 ≤ arrAt w 4 + 8 * w - 4 by omega)
    (show arrAt w 4 + 8 * w - 4 + 4 ≤ arrAt w 4 + 8 * w by omega)
  have keeps := outside_array_keeps arrayOutside (len := len) (by have := h.workspace.nowrap; omega)
  have frame := outside_workspace arrayOutside (size := 8 * len) (by omega)
  have fullRest : Rest roundClobbers s t := rest.mono (by decide)
  have ready := h.after_array (by decide : 4 ≠ 0) keeps frame fullRest
    ((rest.gpr .r0 (by decide)).trans h.ptr)
  refine ⟨ready.1, ?_, ready.2, frame, fullRest⟩
  rw [numAt_native, mem]
  exact val32_write_top_bit s.mem (State.addr base) (by omega) (by have := h.workspace.nowrap; omega)
    (by rw [← numAt_native]; exact zero)

theorem r2NormalizedConstants_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) :
    WP isa r2NormalizedConstants s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (64 * w - 1) ∧
      w32 t.mem (State.addr base) (arrAt w 7) = 2 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [r2NormalizedConstants, WP.seq_iff]
  refine WP.mono (smallConst_ok s (o := 4) 0 h (by decide) (by decide) (by decide) (by decide)) ?_
  rintro u ⟨ready, zero, _, keeps1, frame1, rest1⟩
  rw [WP.seq_iff]
  refine WP.mono (r2TopBitReady_ok u ready zero) ?_
  rintro v ⟨readyV, top, modV, frameV, restV⟩
  refine WP.mono (smallConst_ok v (o := 7) 2 readyV (by decide) (by decide) (by decide) (by decide)) ?_
  rintro t ⟨next, _, two, keeps2, frame2, rest2⟩
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  exact ⟨next, (keeps_array_num keeps2 fits op4 (by decide)).trans top, two,
    (keeps_array_num keeps2 fits op0 (by decide)).trans
      (modV.trans (keeps_array_num keeps1 fits op0 (by decide))),
    frame1.trans (frameV.trans frame2), rest1.trans (restV.trans rest2)⟩

end VG.Proof.Bignum.Arm
