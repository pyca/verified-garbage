module
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Impl.Bignum.Arm.PdChecks

import VerifiedGarbage.Proof.Bignum.Arm.PdOddRead
import VerifiedGarbage.Proof.Bignum.Arm.PdOddFinish
import VerifiedGarbage.Proof.Bignum.Arm.PdParity
import VerifiedGarbage.Proof.Framework.Block

/-! # The public precomputation checks include exact odd-modulus validation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem pdOdd_ok (s : State) {base : BitVec 32} {len w : Nat} {accepted : Bool}
    (h : LayoutFrameReady base len w s) (fit : s.sp.toNat + 52 ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 48) 4)
    (flag : s.mem.readW (off (State.addr s.sp) 48) 32 = BitVec.ofNat 32 accepted.toNat) :
    WP isa pdOdd s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 (accepted && decide (numAt s.mem (State.addr base) w 0 % 2 = 1)).toNat ∧
      t.z = !(accepted && decide (numAt s.mem (State.addr base) w 0 % 2 = 1)) ∧
      t.mem = s.mem ∧ Rest [.r1, .r11] s t := by
  have positive : 0 < w := by have := h.width ▸ h.layout.1; omega
  rw [pdOdd, WP.seq_iff]
  refine WP.mono (pdOddRead_ok s h fit read) ?_
  rintro u ⟨byte, saved, memU, restU⟩
  refine WP.mono (pdOddFinish_ok u) ?_
  rintro t ⟨value, zero, memT, restT⟩
  have parity : (s.mem (off (State.addr base) (Proof.Rsa.Mont.arrAt w 0))).setWidth 32 &&& 1 =
      BitVec.ofNat 32 (numAt s.mem (State.addr base) w 0 % 2) := numAt_parity_word s.mem _ positive
  rw [byte, saved, flag, parity] at value zero
  have bit : BitVec.ofNat 32 accepted.toNat &&& BitVec.ofNat 32 (numAt s.mem (State.addr base) w 0 % 2) =
      BitVec.ofNat 32 (accepted && decide (numAt s.mem (State.addr base) w 0 % 2 = 1)).toNat := by
    have cases : numAt s.mem (State.addr base) w 0 % 2 = 0 ∨ numAt s.mem (State.addr base) w 0 % 2 = 1 := by omega
    rcases cases with hh | hh <;> cases accepted <;> simp [hh]
  rw [bit] at value zero
  refine ⟨value, ?_, memT.trans memU, restU.trans restT⟩
  rw [zero]
  cases accepted && decide (numAt s.mem (State.addr base) w 0 % 2 = 1) <;> rfl

end VG.Proof.Bignum.Arm
