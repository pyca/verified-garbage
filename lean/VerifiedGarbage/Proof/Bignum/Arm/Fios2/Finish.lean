module

public import VerifiedGarbage.Impl.Bignum.Arm.Fios2
public import VerifiedGarbage.Proof.Bignum.Arm.RoundMeta
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.RoundFinishSteps
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! The end of a two-row round: clear the top word, move the first operand's
pointer by two words and the remaining rounds down by two. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str wp_dp wp_subs op2_imm dpVal)

theorem advanceOperand2_ok (s : State) {base : BitVec 32} {size tmp : Nat}
    (ws : Workspace s base size) (fit : tmp + 20 ≤ size)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 tmp) :
    WP isa (.block VG.Impl.Bignum.Arm.Fios2.advanceOperand2) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) (tmp + 16))
        (s.mem.readW (off (State.addr base) (tmp + 16)) 32 + 8) ∧ Rest [.r4] s t := by
  unfold VG.Impl.Bignum.Arm.Fios2.advanceOperand2
  refine wp_ldr (by decide) (ws.ea ptr (by omega)) (ws.read fit) fun u hu => ?_
  refine wp_dp (op2_imm (by decide)) fun v hv => ?_
  have wv := (ws.congr hu.wr).congr hv.wr
  have pv := (hv.other .r0 (by decide)).trans ((hu.other .r0 (by decide)).trans ptr)
  refine wp_str (by decide) (wv.ea pv (by omega)) (wv.write fit) fun t ht => WP.block_nil ?_
  refine ⟨?_, ?_⟩
  · rw [ht.mem, hv.mem, hu.mem, hv.gpr, dpVal, hu.gpr]
  · exact (hu.rest (by simp)).trans ((hv.rest (by simp)).trans (ht.rest _))

theorem decrementRounds2_ok (s : State) {base : BitVec 32} {size tmp : Nat}
    (ws : Workspace s base size) (fit : tmp + 24 ≤ size)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 tmp) :
    WP isa (.block VG.Impl.Bignum.Arm.Fios2.decrementRounds2) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) (tmp + 20))
        (s.mem.readW (off (State.addr base) (tmp + 20)) 32 - 2) ∧
      t.z = (s.mem.readW (off (State.addr base) (tmp + 20)) 32 - 2 == 0) ∧ Rest [.lr] s t := by
  unfold VG.Impl.Bignum.Arm.Fios2.decrementRounds2
  refine wp_ldr (by decide) (ws.ea ptr (by omega)) (ws.read fit) fun u hu => ?_
  refine wp_subs (op2_imm (by decide)) fun v hv hz => ?_
  have wv := (ws.congr hu.wr).congr hv.wr
  have pv := (hv.other .r0 (by decide)).trans ((hu.other .r0 (by decide)).trans ptr)
  refine wp_str_z (by decide) (wv.ea pv (by omega)) (wv.write fit) fun t ht htz => WP.block_nil ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [ht.mem, hv.mem, hu.mem, hv.gpr, hu.gpr]
  · rw [htz, hz, hu.gpr]
  · exact (hu.rest (by simp)).trans ((hv.rest (by simp)).trans (ht.rest _))

def finishMem2 (mem : Mem) (base : Addr) (top tmp : Nat) : Mem :=
  ((mem.writeW (off base top) (0 : BitVec 32)).writeW (off base (tmp + 16))
    (mem.readW (off base (tmp + 16)) 32 + 8)).writeW (off base (tmp + 20))
    (mem.readW (off base (tmp + 20)) 32 - 2)

theorem finish_ok (s : State) {base : BitVec 32} {size top tmp : Nat}
    (ws : Workspace s base size) (fit : tmp + 24 ≤ size) (htmp : tmp = top + 12)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 top) :
    WP isa (.block VG.Impl.Bignum.Arm.Fios2.finish) s fun t =>
      t.mem = finishMem2 s.mem (State.addr base) top tmp ∧
      t.gpr .r0 = base + BitVec.ofNat 32 tmp ∧
      t.z = (s.mem.readW (off (State.addr base) (tmp + 20)) 32 - 2 == 0) ∧
      Rest [.r0, .r3, .r4, .lr] s t := by
  have hn := ws.nowrap
  rw [VG.Impl.Bignum.Arm.Fios2.finish, List.append_assoc]
  apply WP.block_append_iff.mpr
  refine WP.mono (clearTop_ok s ws (by omega) ptr) ?_
  rintro u ⟨mem1, ptr1, keep1⟩
  rw [← htmp] at ptr1
  have wr1 := writeW32_outside s.mem (State.addr base) (d := top) (0 : BitVec 32) (by omega)
  rw [← mem1] at wr1
  have oldPtr := outside_read32 wr1 (d := tmp + 16) (by omega) (by omega)
  have oldCount := outside_read32 wr1 (d := tmp + 20) (by omega) (by omega)
  apply WP.block_append_iff.mpr
  refine WP.mono (advanceOperand2_ok u (ws.congr keep1.wr) (by omega) ptr1) ?_
  rintro v ⟨mem2, keep2⟩
  have wr2 := writeW32_outside u.mem (State.addr base) (d := tmp + 16)
    (u.mem.readW (off (State.addr base) (tmp + 16)) 32 + 8) (by omega)
  rw [← mem2] at wr2
  have oldCount2 := (outside_read32 wr2 (d := tmp + 20) (by omega) (by omega)).trans oldCount
  refine WP.mono (decrementRounds2_ok v ((ws.congr keep1.wr).congr keep2.wr) fit
    ((keep2.gpr .r0 (by simp)).trans ptr1)) ?_
  rintro t ⟨mem3, zero, keep3⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mem3, oldCount2, mem2, oldPtr, mem1, finishMem2]
  · rw [keep3.gpr .r0 (by simp), keep2.gpr .r0 (by simp), ptr1]
  · rw [zero, oldCount2]
  · exact (keep1.mono (by simp_all)).trans
      ((keep2.mono (by simp_all)).trans (keep3.mono (by simp_all)))

theorem finish_meta {mem : Mem} {base : BitVec 32} {size top tmp a b mod acc n i : Nat} {inv : BitVec 32}
    (nowrap : base.toNat + size ≤ 2 ^ 32) (fit : tmp + 32 ≤ size) (htmp : tmp = top + 12)
    (hdr : RoundMeta mem base tmp a b mod acc n i inv) (hi : i + 2 ≤ n) :
    RoundMeta (finishMem2 mem (State.addr base) top tmp) base tmp a b mod acc n (i + 2) inv := by
  have hb : (State.addr base).toNat + size ≤ 2 ^ 32 := by
    rw [VG.Proof.X25519.Arm.addr_toNat]
    exact nowrap
  have stable (d : Nat) (hd : d + 4 ≤ 32) (sep : d + 4 ≤ 16 ∨ 24 ≤ d) :
      (finishMem2 mem (State.addr base) top tmp).readW (off (State.addr base) (tmp + d)) 32 =
        mem.readW (off (State.addr base) (tmp + d)) 32 := by
    apply BitVec.eq_of_toNat_eq
    change w32 (finishMem2 mem (State.addr base) top tmp) (State.addr base) (tmp + d) =
      w32 mem (State.addr base) (tmp + d)
    rw [finishMem2, w32_write_ne hb (by omega) (by omega) (by omega),
      w32_write_ne hb (by omega) (by omega) (by omega),
      w32_write_ne hb (by omega) (by omega) (by omega)]
  have ap : (finishMem2 mem (State.addr base) top tmp).readW (off (State.addr base) (tmp + 16)) 32 =
      mem.readW (off (State.addr base) (tmp + 16)) 32 + 8 := by
    apply BitVec.eq_of_toNat_eq
    change w32 (finishMem2 mem (State.addr base) top tmp) (State.addr base) (tmp + 16) = _
    rw [finishMem2, w32_write_ne hb (by omega) (by omega) (by omega), w32_write_self]
  have count : (finishMem2 mem (State.addr base) top tmp).readW (off (State.addr base) (tmp + 20)) 32 =
      mem.readW (off (State.addr base) (tmp + 20)) 32 - 2 := by
    rw [finishMem2, Mem.readW_writeW_self32]
  refine ⟨(stable 0 (by decide) (by decide)).trans hdr.count,
    (stable 4 (by decide) (by decide)).trans hdr.bPtr,
    (stable 8 (by decide) (by decide)).trans hdr.mPtr,
    (stable 12 (by decide) (by decide)).trans hdr.inverse, ?_, ?_,
    (stable 28 (by decide) (by decide)).trans hdr.accPtr⟩
  · rw [ap, hdr.aPtr]
    change base + BitVec.ofNat 32 (a + 4 * i) + BitVec.ofNat 32 8 = _
    rw [Offset.add_add]
    congr 1
  · rw [count, hdr.remaining]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 2 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1

theorem finish_value {mem : Mem} {base : Addr} {size acc top tmp n : Nat}
    (nowrap : base.toNat + size ≤ 2 ^ 32) (fit : tmp + 24 ≤ size)
    (htop : top = acc + 4 * (n + 1)) (htmp : tmp = top + 12) :
    val32 (finishMem2 mem base top tmp) base acc (n + 2) = val32 mem base acc (n + 1) ∧
      Outs base [(acc, 4 * (n + 2)), (tmp + 16, 8)] mem (finishMem2 mem base top tmp) := by
  have k1 := writeW32_outside mem base (d := top) (0 : BitVec 32) (by omega)
  have k2 := writeW32_outside (mem.writeW (off base top) (0 : BitVec 32)) base (d := tmp + 16)
    (mem.readW (off base (tmp + 16)) 32 + 8) (by omega)
  have k3 := writeW32_outside ((mem.writeW (off base top) (0 : BitVec 32)).writeW
    (off base (tmp + 16)) (mem.readW (off base (tmp + 16)) 32 + 8)) base (d := tmp + 20)
    (mem.readW (off base (tmp + 20)) 32 - 2) (by omega)
  have low1 := k1.val32 (d := acc) (k := n + 1) (by omega) (by omega)
  have low2 := k2.val32 (d := acc) (k := n + 1) (by omega) (by omega)
  have low3 := k3.val32 (d := acc) (k := n + 1) (by omega) (by omega)
  have hi2 := k2.w32 (d := top) (by omega) (by omega)
  have hi3 := k3.w32 (d := top) (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · rw [show n + 2 = (n + 1) + 1 by omega, val32_succ, finishMem2, low3, low2, low1,
      ← htop, hi3, hi2, w32_write_self]
    simp only [show (0 : BitVec 32).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
  · exact (Outs.of_outside (k1.mono (o' := acc) (n' := 4 * (n + 2)) (by omega) (by omega)) (by simp)).trans
      ((Outs.of_outside (k2.mono (o' := tmp + 16) (n' := 8) (by omega) (by omega)) (by simp)).trans
        (Outs.of_outside (k3.mono (o' := tmp + 16) (n' := 8) (by omega) (by omega)) (by simp)))

end VG.Proof.Bignum.Arm.Fios2
