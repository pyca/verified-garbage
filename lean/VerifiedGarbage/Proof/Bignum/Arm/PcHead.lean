module

public import VerifiedGarbage.Impl.Bignum.Arm.PcFn
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Proof.X25519.Arm.Instr

/-! # Compute the shared RSA limb count from the public byte length -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_dp wp_mov op2_imm op2_lsr dpVal)

theorem modulus_words_word (k : BitVec 32) (fit : k.toNat + 7 < 2 ^ 32) :
    (k + 7) >>> 3 = BitVec.ofNat 32 (Spec.Rsa.modulusWords k.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add]
  simp only [show (7 : BitVec 32).toNat = 7 from rfl, Nat.mod_eq_of_lt fit,
    Spec.Rsa.modulusWords, BitVec.toNat_ofNat]
  omega

theorem pcHead_ok (s : State) {k : Nat} (hk : k ≤ 1024)
    (count : s.gpr .r6 = BitVec.ofNat 32 k) :
    WP isa (.block PcFn.head) s fun t =>
      t.gpr .r7 = BitVec.ofNat 32 (Spec.Rsa.modulusWords k) ∧ t.gpr .r3 = 0 ∧
      t.mem = s.mem ∧ Rest [.r3, .r7] s t := by
  have kn : (s.gpr .r6).toNat = k := by rw [count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold PcFn.head
  refine wp_dp (op2_imm (by decide)) fun u h => ?_
  refine wp_mov (op2_lsr (by decide)) fun v j => ?_
  refine wp_mov (op2_imm (by decide)) fun t l => WP.block_nil ?_
  refine ⟨?_, l.gpr, l.mem.trans (j.mem.trans h.mem),
    (h.rest (by simp)).trans ((j.rest (by simp)).trans (l.rest (by simp)))⟩
  rw [l.other .r7 (by decide), j.gpr, h.gpr, dpVal]
  have value := modulus_words_word (s.gpr .r6) (by rw [kn]; omega)
  rw [kn] at value
  exact value

end VG.Proof.Bignum.Arm
