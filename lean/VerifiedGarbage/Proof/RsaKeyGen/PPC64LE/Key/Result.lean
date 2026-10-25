module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Body
public import VerifiedGarbage.Proof.RsaKeyGen.KeyOp
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# `vg_rsa_keygen_key` on PPC64LE: the key the body's numbers make

`key_result`: `keyFromPrimes` of the inputs is the key of the body's numbers
under `kMask`, `.inr ()` (the status 2) under `kSmall`, and an error
otherwise (`Proof/RsaKeyGen/KeyOp.lean`'s `keyFromPrimes_code`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Key

open VG VG.PPC64LE

theorem mL_eq (P : Nat) : mL P = VG.Proof.RsaKeyGen.qModP P := by
  unfold mL good VG.Proof.RsaKeyGen.qModP
  by_cases a : P < 3 <;> by_cases b : P % 2 = 1 <;> simp [a, b]

theorem hpl_of (s0 : State) : pIn s0 < 2 ^ (8 * kL s0) := by
  have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s0.mem (s0.gpr .r7) (kL s0))
  rw [show (Spec.Rsa.bytesAt s0.mem (s0.gpr .r7) (kL s0)).length = kL s0 by simp [Spec.Rsa.bytesAt]] at this
  rw [Nat.pow_mul]; exact this

theorem hql_of (s0 : State) : qIn s0 < 2 ^ (8 * kL s0) := by
  have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s0.mem (s0.gpr .r9) (kL s0))
  rw [show (Spec.Rsa.bytesAt s0.mem (s0.gpr .r9) (kL s0)).length = kL s0 by simp [Spec.Rsa.bytesAt]] at this
  rw [Nat.pow_mul]; exact this

theorem hel_of {s0 : State} (h : keyP.pre s0) : eIn s0 < 2 ^ 64 := by
  have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 6) (PPC64LE.stackArg s0 7).toNat)
  rw [show (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 6) (PPC64LE.stackArg s0 7).toNat).length =
    (PPC64LE.stackArg s0 7).toNat by simp [Spec.Rsa.bytesAt]] at this
  exact Nat.lt_of_lt_of_le this (by
    rw [show (2 : Nat) ^ 64 = 256 ^ 8 by decide]; exact Nat.pow_le_pow_right (by decide) (kpre h).el8)

theorem key_result {s0 : State} (h : keyP.pre s0) {D x : Nat} (hxl : x < mL (kP s0))
    (hx : ((mL (kP s0) : Nat) : Int) ∣ (x : Int) * kQ s0 - Nat.gcd (kQ s0) (mL (kP s0)))
    (hinv : okv (eIn s0) (kLc s0) → Spec.Rsa.inverse (eIn s0) (kLc s0) = some D) :
    Spec.RsaKeyGen.keyFromPrimes (16 * kL s0) (eIn s0) (pIn s0) (qIn s0) =
      if kMask s0 D then .inl (.ok ⟨kP s0 * kQ s0, eIn s0, D, kP s0, kQ s0, D % (kP s0 - 1), D % (kQ s0 - 1), x⟩)
      else if kSmall s0 D then .inr () else .inl (.error .internal) := by
  have p := kpre h
  have hpl := hpl_of s0
  have hql := hql_of s0
  have hel := hel_of h
  rw [mL_eq] at hxl hx
  rw [VG.Proof.RsaKeyGen.keyFromPrimes_code p.l1 p.l2 hpl hql hel hx hxl]
  by_cases ok : okv (eIn s0) (kLc s0)
  · have hi := hinv ok
    simp only [kLc, kP, kQ] at hi
    rw [hi]
    dsimp only
    by_cases hs : D ≤ 2 ^ (8 * kL s0)
    · have sm : kSmall s0 D := ⟨ok, by omega_arith⟩
      have nm : ¬ kMask s0 D := fun m => m.1 sm
      simp only [hs, nm, sm, ↓reduceIte]
    · have sm : ¬ kSmall s0 D := fun a => hs (by have := a.2; omega_arith)
      simp only [hs, sm, ↓reduceIte]
      by_cases hm : kMask s0 D
      · simp only [hm, ↓reduceIte]
        refine ite_eq_left ?_
        obtain ⟨-, top, -, g, pp, qq, ee, e3, e33⟩ := hm
        rw [← mL_eq]
        simp only [kP, kQ] at top g pp qq
        simp [Spec.Rsa.exponentValid, g, pp, qq, ee, e33]
        omega_arith
      · simp only [hm, ↓reduceIte]
        refine ite_eq_right fun c => ?_
        apply hm
        simp only [Bool.and_eq_true, decide_eq_true_eq, Spec.Rsa.exponentValid, beq_iff_eq] at c
        obtain ⟨⟨⟨⟨top, g⟩, pp⟩, qq⟩, ⟨ee, e3⟩, e33⟩ := c
        rw [← mL_eq] at g
        exact ⟨sm, by simp only [kP, kQ]; omega_arith, ok, g, pp, qq, ee, by omega_arith, e33⟩
  · have hi := okv_none ok
    simp only [kLc, kP, kQ] at hi
    rw [hi]
    have sm : ¬ kSmall s0 D := fun a => ok a.1
    have nm : ¬ kMask s0 D := fun m => ok m.2.2.1
    simp only [nm, sm, ↓reduceIte]

end VG.Proof.RsaKeyGen.PPC64LE.Key
