module
public import VerifiedGarbage.Impl.Bignum.Arm.Round
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace

import VerifiedGarbage.Proof.Bignum.Arm.RoundFinishSteps
import VerifiedGarbage.Proof.Framework.Block

/-! # Exact stores and public loop condition at the end of a Montgomery round -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem roundFinish_ok (s : State) {base : BitVec 32} {size top tmp : Nat}
    (ws : Workspace s base size) (fit : tmp + 24 ≤ size) (htmp : tmp = top + 12)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 top) :
    WP isa (.block roundFinish) s fun t =>
      t.mem = ((s.mem.writeW (off (State.addr base) top) (0 : BitVec 32)).writeW
        (off (State.addr base) (tmp + 16)) (s.mem.readW (off (State.addr base) (tmp + 16)) 32 + 4)).writeW
        (off (State.addr base) (tmp + 20)) (s.mem.readW (off (State.addr base) (tmp + 20)) 32 - 1) ∧
      t.gpr .r0 = base + BitVec.ofNat 32 tmp ∧
      t.z = (s.mem.readW (off (State.addr base) (tmp + 20)) 32 - 1 == 0) ∧
      Rest [.r0, .r3, .r4, .lr] s t := by
  have hn := ws.nowrap
  rw [roundFinish, List.append_assoc]
  apply WP.block_append_iff.mpr
  refine WP.mono (clearTop_ok s ws (by omega) ptr) ?_
  rintro u ⟨mem1, ptr1, keep1⟩
  rw [← htmp] at ptr1
  have wr1 := writeW32_outside s.mem (State.addr base) (d := top) (0 : BitVec 32) (by omega)
  rw [← mem1] at wr1
  have oldPtr := outside_read32 wr1 (d := tmp + 16) (by omega) (by omega)
  have oldCount := outside_read32 wr1 (d := tmp + 20) (by omega) (by omega)
  apply WP.block_append_iff.mpr
  refine WP.mono (advanceOperand_ok u (ws.congr keep1.wr) (by omega) ptr1) ?_
  rintro v ⟨mem2, keep2⟩
  have wr2 := writeW32_outside u.mem (State.addr base) (d := tmp + 16)
    (u.mem.readW (off (State.addr base) (tmp + 16)) 32 + 4) (by omega)
  rw [← mem2] at wr2
  have oldCount2 := (outside_read32 wr2 (d := tmp + 20) (by omega) (by omega)).trans oldCount
  refine WP.mono (decrementRounds_ok v ((ws.congr keep1.wr).congr keep2.wr) fit
    ((keep2.gpr .r0 (by simp)).trans ptr1)) ?_
  rintro t ⟨mem3, zero, keep3⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mem3, oldCount2, mem2, oldPtr, mem1]
  · rw [keep3.gpr .r0 (by simp), keep2.gpr .r0 (by simp), ptr1]
  · rw [zero, oldCount2]
  · exact (keep1.mono (by simp_all)).trans
      ((keep2.mono (by simp_all)).trans (keep3.mono (by simp_all)))

end VG.Proof.Bignum.Arm
