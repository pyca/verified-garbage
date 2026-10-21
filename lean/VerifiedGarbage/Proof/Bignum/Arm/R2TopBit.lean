module

public import VerifiedGarbage.Impl.Bignum.Arm.R2Normalized
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Write the public top radix bit using the existing array header. -/

@[expose] public section
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
