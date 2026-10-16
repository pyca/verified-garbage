module

public import VerifiedGarbage.Proof.Bignum.Arm.SecretPowerInput
public import VerifiedGarbage.Proof.Bignum.Arm.ImportOperand
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Ciphertext import establishes all secret-exponentiation preconditions -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt arrAt)
open VG.Proof.X25519.Arm (Rest)

theorem secretPower_import_ready (s : State) {base xp ep : BitVec 32} {len w k eLen M : Nat} {xb eb : List Byte}
    (h : SecretPowerInput base xp ep len w k eLen M xb eb s)
    (pointer : s.mem.readW (off (State.addr base) 128) 32 = ep)
    (count : s.mem.readW (off (State.addr base) 132) 32 = BitVec.ofNat 32 eLen) :
    WP isa (importOperand 1) s fun t => ExpPhaseInput base ep len w M (Spec.Rsa.os2ip xb) eb t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (importOperand_ok s h.ready (by decide : 1 < 8) (by decide) h.inputPositive h.inputFits
    h.input.fits h.input.read h.inputSeparate h.source h.count) ?_
  rintro t ⟨ready, input, keeps, frame, rest⟩
  rw [h.input.bytes] at input
  have exponent := h.exponent.after_frame frame rest
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.exponentSeparate)
  have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at fits; omega
  have modulus := (keeps_array_num keeps fits (q := 0)
    (by simp [Spec.Rsa.Mont.Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]) (by decide)).trans h.modulus
  have r2 := (keeps_array_num keeps fits (q := 4)
    (by simp [Spec.Rsa.Mont.Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]) (by decide)).trans h.r2
  have positive : 0 < M := by have := h.ready.modulus; rw [h.modulus] at this; omega
  refine ⟨⟨ready, modulus, h.odd, input, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, exponent.byte⟩, frame, rest⟩
  · rw [r2]; exact Nat.mod_lt _ positive
  · rw [r2, Nat.mod_mod, ← Nat.pow_add, show 64 * w + 64 * w = 128 * w by omega]
  · rw [keeps_header_readW keeps size (d := 128) (bits := 32) (by decide)]; exact pointer
  · rw [keeps_header_readW keeps size (d := 132) (bits := 32) (by decide), exponent.length]; exact count
  · rw [exponent.length]; exact h.exponentPositive
  · rw [exponent.length]; exact h.exponentFits
  · rw [exponent.length]; exact exponent.fits
  · rw [exponent.length]; exact exponent.read
  · rw [exponent.length]; exact h.exponentSeparate

end VG.Proof.Bignum.Arm
