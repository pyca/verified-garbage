module
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Impl.Bignum.Arm.R2
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopState

import VerifiedGarbage.Proof.Bignum.Arm.R2Constants
import VerifiedGarbage.Proof.Bignum.Arm.R2CountInit
import VerifiedGarbage.Proof.Bignum.Arm.DoubleCountMemory
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Block

/-! # Initialize every loop invariant for RSA R-squared precomputation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt)
open VG.Proof.X25519.Arm (Rest)

theorem r2Init_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) :
    WP isa r2Init s fun t => DoubleLoopReady base len w (65 * w) t ∧
      numAt t.mem (State.addr base) w 4 = 1 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [r2Init, WP.seq_iff]
  refine WP.mono (r2Constants_ok s h) ?_
  rintro u ⟨ready, one, two, modulus, frame, rest⟩
  have fits := ready.layout.2.2.1
  have size : 212 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have header := nativeHeader_of_layout u.mem base ready.workspace.nowrap (Nat.le_refl _) ready.layout
  rw [ready.width] at header
  let c := (u.mem.readW (off (State.addr base) 208) 32).toNat
  have loop : DoubleLoopReady base len w c u := by
    refine ⟨ready.workspace, ready.layout, ready.width, ready.ptr, ready.inverse,
      ?_, two, ?_, ready.stackRead, ready.stackSep, ready.saved⟩
    · rw [one]; exact ready.modulus
    · simp only [c, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (r2CountInit_ok u ready.workspace size ready.ptr header.count) ?_
  rintro t ⟨mem, keep⟩
  obtain ⟨next, frameT, number, modT⟩ := loop.after_count mem keep
  exact ⟨next, number.trans one, modT.trans modulus, frame.trans frameT,
    rest.trans (keep.mono (by decide))⟩

end VG.Proof.Bignum.Arm
