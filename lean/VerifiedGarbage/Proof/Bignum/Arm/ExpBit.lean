module
public import VerifiedGarbage.Proof.Bignum.Arm.ExpState
public import VerifiedGarbage.Impl.Bignum.Arm.Exp

import VerifiedGarbage.Proof.Bignum.Arm.ExpBitTest
import VerifiedGarbage.Proof.Bignum.Arm.ExpStep
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block

/-! # One binary exponent bit updates the proved Montgomery power -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt arrAt Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem expBit_ok (s : State) {base : BitVec 32} {len w M x E V : Nat}
    (h : ExpState base len w M x E s) (hv : V < 2 ^ 32)
    (byte : s.mem.readW (VG.Proof.Mont.off (State.addr base) 200) 32 = BitVec.ofNat 32 V) :
    WP isa expBit s fun t => ExpState base len w M x (2 * E + V / 128 % 2) t ∧
      Keeps (State.addr base) len w 6 s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have size : 256 ≤ 8 * len := by
    have := h.ready.layout.2.2.1
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at this
    omega
  rw [expBit, WP.seq_iff]
  refine WP.mono (exp_square_ok s h) ?_
  rintro u ⟨square, keepsU, frameU, restU⟩
  have byteU := (keeps_header_readW keepsU size (d := 200) (bits := 32) (by decide)).trans byte
  rw [WP.seq_iff]
  refine WP.mono (expBitTest_ok u square.ready.workspace (by omega) square.ready.ptr hv byteU) ?_
  rintro v ⟨flag, memV, restV⟩
  have stateV := square.of_mem memV restV ((restV.gpr .r0 (by decide)).trans square.ready.ptr)
  have keepV : Keeps (State.addr base) len w 6 s.mem v.mem := by rw [memV]; exact keepsU
  have frameV : Frame [⟨State.addr base, 8 * len⟩] s.mem v.mem := by rw [memV]; exact frameU
  have rest : Rest roundClobbers s v := restU.trans (restV.mono (by decide))
  by_cases bit : V / 128 % 2 = 0
  · refine WP.ite false (by simp [eval, flag, bit]) (by simp) (fun _ => WP.block_nil ?_)
    exact ⟨by simpa only [bit, Nat.add_zero] using stateV, keepV, frameV, rest⟩
  · have one : V / 128 % 2 = 1 := by omega
    refine WP.ite true (by simp [eval, flag, bit]) (fun _ => ?_) (by simp)
    refine WP.mono (exp_multiply_ok v stateV) ?_
    rintro t ⟨final, keepsT, frameT, restT⟩
    exact ⟨by simpa only [one] using final,
      fun i hi sep => (keepsT i hi sep).trans (keepV i hi sep), frameV.trans frameT, rest.trans restT⟩

end VG.Proof.Bignum.Arm
