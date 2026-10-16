module

public import VerifiedGarbage.Proof.Bignum.Arm.SecretBitValue
public import VerifiedGarbage.Proof.Bignum.Arm.SecretMultiply
public import VerifiedGarbage.Proof.Bignum.Arm.SelectPower
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Every private exponent bit computes both candidates and selects without branching -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (numAt arrAt Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem secretExpBit_ok (s : State) {base : BitVec 32} {len w M x E V : Nat}
    (h : ExpState base len w M x E s) (hv : V < 2 ^ 32)
    (byte : s.mem.readW (VG.Proof.Mont.off (State.addr base) 200) 32 = BitVec.ofNat 32 V) :
    WP isa secretExpBit s fun t => ExpState base len w M x (2 * E + V / 128 % 2) t ∧
      (∀ d, d + 4 ≤ 256 → t.mem.readW (VG.Proof.Mont.off (State.addr base) d) 32 =
        s.mem.readW (VG.Proof.Mont.off (State.addr base) d) 32) ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have size : 256 ≤ 8 * len := by
    have := h.ready.layout.2.2.1
    simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at this
    omega
  rw [secretExpBit, WP.seq_iff]
  refine WP.mono (exp_square_ok s h) ?_
  rintro u ⟨square, keepsU, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (secretMultiply_ok u square) ?_
  rintro v ⟨power, candidateBound, candidateValue, keepsV, frameV, restV⟩
  have byteV := (keeps_header_readW keepsV size (d := 200) (bits := 32) (by decide)).trans
    ((keeps_header_readW keepsU size (d := 200) (bits := 32) (by decide)).trans byte)
  rw [WP.seq_iff]
  refine WP.mono (secretBitValue_ok v power.ready.workspace (by omega) power.ready.ptr hv byteV) ?_
  rintro z ⟨bit, memZ, restZ⟩
  have pz := power.of_mem memZ restZ ((restZ.gpr .r0 (by simp)).trans power.ready.ptr)
  refine WP.mono (selectPower_ok z pz.ready (by rw [bit]; omega)) ?_
  rintro t ⟨ready, value, keepsT, frameT, restT⟩
  have modulus := (pz.ready.after_array (by decide : 6 ≠ 0) keepsT frameT restT ready.ptr).2.trans pz.modulus
  have bound : numAt t.mem (State.addr base) w 6 < M := by
    rw [value, bit]
    split
    · exact pz.powerBound
    · rw [memZ]; exact candidateBound
  have result : numAt t.mem (State.addr base) w 6 % M = x ^ (2 * E + V / 128 % 2) * 2 ^ (64 * w) % M := by
    rw [value, bit]
    by_cases zero : V / 128 % 2 = 0
    · simpa only [zero, ite_true, Nat.add_zero] using pz.powerValue
    · have one : V / 128 % 2 = 1 := by omega
      simp only [one, memZ]
      exact candidateValue
  refine ⟨pz.after_y ready modulus keepsT bound result, ?_, ?_, ?_⟩
  · intro d hd
    rw [keeps_header_readW keepsT size (d := d) (bits := 32) hd, memZ,
      keeps_header_readW keepsV size (d := d) (bits := 32) hd,
      keeps_header_readW keepsU size (d := d) (bits := 32) hd]
  · rw [memZ] at frameT
    exact frameU.trans (frameV.trans frameT)
  · exact restU.trans (restV.trans ((restZ.mono (by simp [roundClobbers])).trans restT))

end VG.Proof.Bignum.Arm
