module

public import VerifiedGarbage.Proof.Bignum.Arm.SquareReduce
public import VerifiedGarbage.Proof.Bignum.Arm.Csub
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The square's canonical result, and the whole square -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str wp_dp wp_mov op2_imm op2_reg op2_lsl dpVal)

theorem sqFinishHeader_ok (s : State) {base : BitVec 32} {size mod M : Nat}
    (ws : Workspace s base size) (fit : 84 ≤ size) (p0 : s.gpr .r0 = base)
    (hm : s.mem.readW (off (State.addr base) 64) 32 = base + BitVec.ofNat 32 mod)
    (hM : s.mem.readW (off (State.addr base) 80) 32 = base + BitVec.ofNat 32 M) :
    WP isa (.block sqFinishHeader) s fun t =>
      t.gpr .r12 = base + BitVec.ofNat 32 mod ∧ t.gpr .r0 = base + BitVec.ofNat 32 M ∧
      t.mem = s.mem ∧ Rest [.r0, .r12] s t := by
  have nowrap := ws.nowrap
  unfold sqFinishHeader
  refine wp_ldr (by decide) (sq_ea0 nowrap p0 (by omega)) (ws.read (by omega)) fun s1 u1 => ?_
  refine wp_ldr (by decide) (sq_ea0 nowrap ((u1.other .r0 (by decide)).trans p0) (by omega))
    (by rw [u1.rd, u1.wr]; exact ws.read (by omega)) fun t u2 => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [u2.other .r12 (by decide), u1.gpr, hm]
  · rw [u2.gpr, u1.mem, hM]
  · rw [u2.mem, u1.mem]
  · exact (u1.rest (by simp)).trans (u2.rest (by simp))

theorem sqFinishLoad_ok (s : State) {base : BitVec 32} {size M n out : Nat}
    (ws : Workspace s base size) (fit : M + 16 ≤ size) (p0 : s.gpr .r0 = base + BitVec.ofNat 32 M)
    (hn : s.mem.readW (off (State.addr base) M) 32 = BitVec.ofNat 32 n)
    (ho : s.mem.readW (off (State.addr base) (M + 4)) 32 = base + BitVec.ofNat 32 out) :
    WP isa (.block sqFinishLoad) s fun t =>
      t.gpr .r7 = BitVec.ofNat 32 n ∧ t.gpr .r9 = base + BitVec.ofNat 32 out ∧
      t.gpr .r3 = s.mem.readW (off (State.addr base) (M + 12)) 32 ∧ t.gpr .r0 = s.gpr .r0 ∧
      t.mem = s.mem ∧ Rest [.r3, .r7, .r9] s t := by
  have nowrap := ws.nowrap
  unfold sqFinishLoad
  refine wp_ldr (by decide) (by simpa only [Nat.add_zero] using sq_ea nowrap p0 (imm := 0) (by omega))
    (ws.read (by omega)) fun s1 u1 => ?_
  have p1 := (u1.other .r0 (by decide)).trans p0
  refine wp_ldr (by decide) (sq_ea nowrap p1 (by omega)) (by rw [u1.rd, u1.wr]; exact ws.read (by omega))
    fun s2 u2 => ?_
  have p2 := (u2.other .r0 (by decide)).trans p1
  refine wp_ldr (by decide) (sq_ea nowrap p2 (by omega))
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact ws.read (by omega)) fun t u3 => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u3.other .r7 (by decide), u2.other .r7 (by decide), u1.gpr, hn]
  · rw [u3.other .r9 (by decide), u2.gpr, u1.mem, ho]
  · rw [u3.gpr, u2.mem, u1.mem]
  · rw [u3.other .r0 (by decide), u2.other .r0 (by decide), u1.other .r0 (by decide)]
  · rw [u3.mem, u2.mem, u1.mem]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans (u3.rest (by simp)))

theorem sqFinishArgs_ok (s : State) {base : BitVec 32} {size M n : Nat}
    (ws : Workspace s base size) (fit : M + 8 * n + 28 ≤ size)
    (p0 : s.gpr .r0 = base + BitVec.ofNat 32 M) (p7 : s.gpr .r7 = BitVec.ofNat 32 n) :
    WP isa (.block sqFinishArgs) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) (M + 8 * n + 24)) (s.gpr .r3) ∧
      t.gpr .r10 = base + BitVec.ofNat 32 (M + 24 + 4 * n) ∧ t.gpr .lr = BitVec.ofNat 32 n ∧
      t.gpr .r11 = 0 ∧ Rest [.r10, .r11, .lr] s t := by
  have nowrap := ws.nowrap
  unfold sqFinishArgs
  refine wp_dp (op2_lsl (by decide)) fun s1 u1 => ?_
  have v1 : s1.gpr .r10 = base + BitVec.ofNat 32 (M + 8 * n) := by
    rw [u1.gpr, dpVal, p0, p7, ofNat_shl (by omega), Offset.add_add, Nat.mul_comm n]
  refine wp_str (by decide) (sq_ea nowrap v1 (by omega)) (by rw [u1.wr]; exact ws.write (by omega))
    fun s2 u2 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s3 u3 => ?_
  refine wp_dp (op2_imm (by decide)) fun s4 u4 => ?_
  refine wp_mov (op2_reg _ _) fun s5 u5 => ?_
  refine wp_mov (op2_imm (by decide)) fun t u6 => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, u6.gpr, ?_⟩
  · rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u1.other .r3 (by decide)]
  · rw [u6.other .r10 (by decide), u5.other .r10 (by decide), u4.gpr, dpVal, u3.gpr, dpVal, u2.gpr,
      u1.other .r0 (by decide), u1.other .r7 (by decide), p0, p7, ofNat_shl (by omega)]
    change base + BitVec.ofNat 32 M + BitVec.ofNat 32 (n * 2 ^ 2) + BitVec.ofNat 32 24 = _
    rw [Offset.add_add, Offset.add_add, show M + (n * 2 ^ 2 + 24) = M + 24 + 4 * n by omega]
  · rw [u6.other .lr (by decide), u5.gpr, u4.other .r7 (by decide), u3.other .r7 (by decide), u2.gpr,
      u1.other .r7 (by decide), p7]
  · exact (u1.rest (by simp)).trans ((u2.rest _).trans ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans
      ((u5.rest (by simp)).trans (u6.rest (by simp))))))

end VG.Proof.Bignum.Arm
