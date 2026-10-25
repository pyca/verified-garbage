module

public import VerifiedGarbage.Impl.Bignum.Arm.R2Normalized
import VerifiedGarbage.Proof.Bignum.Arm.R2Normalized
import VerifiedGarbage.Proof.Bignum.Arm.R2NormalizedCount
import VerifiedGarbage.Proof.Bignum.Arm.DoubleCountMemory
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopState

/-! Establish the original doubling-loop invariant after normalized initialization. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (arrAt numAt)
open VG.Proof.X25519.Arm (Rest)

theorem r2NormalizedCountState_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s)
    (top : numAt s.mem (State.addr base) w 4 = 2 ^ (64 * w - 1))
    (bound : numAt s.mem (State.addr base) w 4 < numAt s.mem (State.addr base) w 0)
    (two : w32 s.mem (State.addr base) (arrAt w 7) = 2) :
    WP isa (.block r2NormalizedCount) s fun t => DoubleLoopReady base len w (w + 1) t ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (64 * w - 1) ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits := h.layout.2.2.1
  have size : 212 ≤ 8 * len := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at fits; omega
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  let c := (s.mem.readW (off (State.addr base) 208) 32).toNat
  have loop : DoubleLoopReady base len w c s :=
    ⟨h.workspace, h.layout, h.width, h.ptr, h.inverse, bound, two,
      by simp only [c, BitVec.ofNat_toNat, BitVec.setWidth_eq], h.stackRead, h.stackSep, h.saved⟩
  refine WP.mono (r2NormalizedCount_ok s h.workspace size h.ptr header.count) ?_
  rintro u ⟨mem, keep⟩
  obtain ⟨next, frame, number, modulus⟩ := loop.after_count mem keep
  exact ⟨next, number.trans top, modulus, frame, keep.mono (by decide)⟩

end VG.Proof.Bignum.Arm
