module

public import VerifiedGarbage.Impl.Bignum.Arm.Shift
public import VerifiedGarbage.Proof.X25519.Arm.Instr

/-! # One in-place packed-word shift step -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str wp_dp wp_subs op2_imm dpVal)

theorem shiftStep_ok (s : State) (lo hi : Addr)
    (hlo : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = lo)
    (hhi : State.addr (s.gpr .r0 + BitVec.ofNat 32 4) = hi)
    (wl : InRegions s.wr lo 4) (rh : InRegions (s.rd ++ s.wr) hi 4) :
    WP isa (.block shiftStep) s fun t =>
      t.mem = s.mem.writeW lo (s.mem.readW hi 32) ∧
      t.gpr .r0 = s.gpr .r0 + 4 ∧ t.gpr .lr = s.gpr .lr - 1 ∧
      t.z = (s.gpr .lr - 1 == 0) ∧ Rest [.r0, .r3, .lr] s t := by
  unfold shiftStep
  refine wp_ldr (by decide) hhi rh fun s1 u1 => ?_
  refine wp_str (a := lo) (by decide) (by rw [u1.other .r0 (by decide)]; exact hlo)
    (by rw [u1.wr]; exact wl) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_subs (op2_imm (by decide)) fun s4 u4 hz => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [u4.mem, u3.mem, u2.mem, u1.mem, u1.gpr]
  · rw [u4.other .r0 (by decide), u3.gpr, dpVal, u2.gpr, u1.other .r0 (by decide)]
  · rw [u4.gpr, u3.other .lr (by decide), u2.gpr, u1.other .lr (by decide)]
  · rw [hz, u3.other .lr (by decide), u2.gpr, u1.other .lr (by decide)]
  · exact (u1.rest (by simp)).trans ((u2.rest _).trans
      ((u3.rest (by simp)).trans (u4.rest (by simp))))

end VG.Proof.Bignum.Arm
