module

public import VerifiedGarbage.Impl.Bignum.Arm.Precompute
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Address setup for the modulus inverse -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wOf Layout)
open VG.Proof.X25519.Arm (Rest wp_mov wp_ldr op2_reg)

theorem inverseArgs_ok (s : State) {base : BitVec 32} {len w : Nat}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (width : wOf s.mem (State.addr base) = w) (ptr : s.gpr .r0 = base) :
    WP isa (.block inverseArgs) s fun t =>
      t.gpr .r0 = base + BitVec.ofNat 32 (arrAt w 0) ∧ t.gpr .r12 = base ∧
      t.mem = s.mem ∧ Rest [.r0, .r12] s t := by
  have fits := layout.2.2.1
  have size : 68 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have header := nativeHeader_of_layout s.mem base ws.nowrap (Nat.le_refl _) layout
  rw [width] at header
  unfold inverseArgs
  refine wp_mov (op2_reg _ _) fun u moved => ?_
  refine wp_ldr (a := off (State.addr base) 64) (by decide)
    (by rw [moved.other .r0 (by decide), ptr]; exact addr_add (by have := ws.nowrap; omega))
    (by rw [moved.rd, moved.wr]; exact ws.read size) fun t loaded => WP.block_nil ?_
  refine ⟨?_, ?_, loaded.mem.trans moved.mem, (moved.rest (by simp)).trans (loaded.rest (by simp))⟩
  · rw [loaded.gpr, moved.mem]; exact header.array 0 (by decide)
  · rw [loaded.other .r12 (by decide), moved.gpr, ptr]

end VG.Proof.Bignum.Arm
