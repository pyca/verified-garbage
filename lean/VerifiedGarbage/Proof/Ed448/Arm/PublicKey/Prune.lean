import VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Layout
import VerifiedGarbage.Proof.Ed448.PruneBytes
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.X448.Arm.BitWrite
import VerifiedGarbage.Proof.X25519.Arm.Instr

/-!
# Ed448 public-key derivation on ARMv7: pruning the hash in place

`pruneOps` clears bits 0–1 of byte 0 of the hash, sets bit 7 of byte 55 and
clears byte 56, from `r12`; the 57 bytes are then `Spec.Ed448.prune` of the
hash (`prune_step`, by `Proof.Ed448.prune_bytes`).
-/

namespace VG.Proof.Ed448.Arm.PublicKey

open VG VG.Arm VG.Impl.Ed448.Arm.PublicKey VG.Impl.Ed25519.Arm.Whole
open VG.Proof.X25519.Arm (wp_ldrb wp_strb wp_dp wp_movw op2_imm)
open VG.Proof.X448.Arm (writeW8_apply)
open VG.Proof.Ed25519.Arm (Whole.FR)

/-! ## The bytes -/

theorem bytesAt_split (m : Mem) (q : Addr) :
    Spec.Ed448.bytesAt m q 57 = m q :: (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54 ++
      [m (q + BitVec.ofNat 64 55), m (q + BitVec.ofNat 64 56)]) := by
  have b1 : Spec.X25519.bytesAt m q 1 = [m q] := by
    simp [Spec.X25519.bytesAt]
  have b2 : ∀ p : Addr, Spec.X25519.bytesAt m p 2 = [m p, m (p + BitVec.ofNat 64 1)] := fun p => by
    simp [Spec.X25519.bytesAt, List.range_succ]
  rw [Proof.Ed448.bytesAt_eq, show 57 = 1 + (54 + 2) from rfl, VG.Proof.X25519.bytesAt_add,
    VG.Proof.X25519.bytesAt_add, b1, b2, Offset.add_add, Offset.add_add]
  rfl

theorem decodeLE_split (m : Mem) (q : Addr) :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m q 57) = (m q).toNat + 256 *
      (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54) + 2 ^ 432 *
        ((m (q + BitVec.ofNat 64 55)).toNat + 256 * (m (q + BitVec.ofNat 64 56)).toNat)) := by
  rw [bytesAt_split, Spec.Ed448.decodeLE, Proof.Ed448.decodeLE_append]
  have hl : (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54).length = 54 := by simp [Spec.Ed448.bytesAt]
  rw [hl, show (256 : Nat) ^ 54 = 2 ^ 432 by decide +kernel]
  simp only [Spec.Ed448.decodeLE, Nat.mul_zero, Nat.add_zero]

/-! ## The instructions -/

theorem and_fc : ∀ x : BitVec 8, (x.setWidth 32 &&& 0xfc#32).setWidth 8 = BitVec.ofNat 8 (x.toNat &&& 252) := by
  decide

theorem or_80 : ∀ x : BitVec 8, (x.setWidth 32 ||| 0x80#32).setWidth 8 = BitVec.ofNat 8 (x.toNat ||| 128) := by
  decide

theorem pruneOps_ok {s : State} {q : Addr} (hq : State.addr (s.gpr .r12) = q)
    (hfit : (s.gpr .r12).toNat + 57 ≤ 2 ^ 32) (hw : ∀ j < 57, InRegions s.wr (q + BitVec.ofNat 64 j) 1) :
    WP isa (.block pruneOps) s fun t =>
      t.mem = ((s.mem.writeW q (BitVec.ofNat 8 ((s.mem q).toNat &&& 252))).writeW
        (q + BitVec.ofNat 64 55) (BitVec.ofNat 8 ((s.mem (q + BitVec.ofNat 64 55)).toNat ||| 128))).writeW
          (q + BitVec.ofNat 64 56) (0 : BitVec 8) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ ∀ r, r ≠ .r0 → t.gpr r = s.gpr r := by
  have hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1 := fun j hj => by
    obtain ⟨R, hR, hc⟩ := hw j hj
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  have ea : ∀ j < 57, State.addr (s.gpr .r12 + BitVec.ofNat 32 j) = q + BitVec.ofNat 64 j := fun j hj => by
    rw [addr_add (by omega), hq]
  have e0 : q + BitVec.ofNat 64 0 = q := BitVec.add_zero q
  have ne55 : q + BitVec.ofNat 64 55 ≠ q := by
    intro h
    have := congrArg (fun x => (x - q).toNat) h
    simp only [BitVec.sub_self, Offset.add_sub_cancel_left] at this
    exact absurd this (by decide)
  unfold pruneOps
  refine wp_ldrb (a := q) (by decide) (by rw [ea 0 (by decide), e0]) (by rw [← e0]; exact hr 0 (by decide))
    fun s1 v1 => ?_
  refine wp_dp (op2_imm (by decide)) fun s2 v2 => ?_
  refine wp_strb (a := q) (by decide)
    (by rw [v2.other _ (by decide), v1.other _ (by decide), ea 0 (by decide), e0])
    (by rw [v2.wr, v1.wr, ← e0]; exact hw 0 (by decide)) fun s3 v3 => ?_
  refine wp_ldrb (a := q + BitVec.ofNat 64 55) (by decide)
    (by rw [v3.gpr, v2.other _ (by decide), v1.other _ (by decide), ea 55 (by decide)])
    (by rw [v3.rd, v3.wr, v2.rd, v2.wr, v1.rd, v1.wr]; exact hr 55 (by decide)) fun s4 v4 => ?_
  refine wp_dp (op2_imm (by decide)) fun s5 v5 => ?_
  refine wp_strb (a := q + BitVec.ofNat 64 55) (by decide)
    (by rw [v5.other _ (by decide), v4.other _ (by decide), v3.gpr, v2.other _ (by decide),
      v1.other _ (by decide), ea 55 (by decide)])
    (by rw [v5.wr, v4.wr, v3.wr, v2.wr, v1.wr]; exact hw 55 (by decide)) fun s6 v6 => ?_
  refine wp_movw fun s7 v7 => ?_
  refine wp_strb (a := q + BitVec.ofNat 64 56) (by decide)
    (by rw [v7.other _ (by decide), v6.gpr, v5.other _ (by decide), v4.other _ (by decide), v3.gpr,
      v2.other _ (by decide), v1.other _ (by decide), ea 56 (by decide)])
    (by rw [v7.wr, v6.wr, v5.wr, v4.wr, v3.wr, v2.wr, v1.wr]; exact hw 56 (by decide)) fun t vt =>
      WP.block_nil ⟨?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · have r2 : s2.gpr .r0 = (s.mem q).setWidth 32 &&& 0xfc#32 := by
      rw [v2.gpr]; change s1.gpr .r0 &&& _ = _; rw [v1.gpr]; rfl
    have m3 : s3.mem = s.mem.writeW q ((s2.gpr .r0).setWidth 8) := by rw [v3.mem, v2.mem, v1.mem]
    have r5 : s5.gpr .r0 = (s.mem (q + BitVec.ofNat 64 55)).setWidth 32 ||| 0x80#32 := by
      rw [v5.gpr]; change s4.gpr .r0 ||| _ = _
      rw [v4.gpr, m3, writeW8_apply, ite_eq_right ne55]; rfl
    rw [vt.mem, v7.mem, v6.mem, v5.mem, v4.mem, m3, v7.gpr, r5, r2, and_fc, or_80]
    rfl
  · rw [vt.sp, v7.sp, v6.sp, v5.sp, v4.sp, v3.sp, v2.sp, v1.sp]
  · rw [vt.rd, v7.rd, v6.rd, v5.rd, v4.rd, v3.rd, v2.rd, v1.rd]
  · rw [vt.wr, v7.wr, v6.wr, v5.wr, v4.wr, v3.wr, v2.wr, v1.wr]
  · rw [vt.gpr, v7.other r hr, v6.gpr, v5.other r hr, v4.other r hr, v3.gpr, v2.other r hr, v1.other r hr]

end VG.Proof.Ed448.Arm.PublicKey
