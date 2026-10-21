module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyQinv
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Proof.RsaKeyGen.KeyOp
import VerifiedGarbage.Proof.Framework.Omega

/-! # Relate native key components and statuses to the shared specification -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

def assembledKey (B : Addr) (n : Nat) (m : Mem) : Spec.RsaKeyGen.Key :=
  ⟨num m B n aN, val32 m B kEv 2, num m B n aD, num m B n aPa, num m B n aQa,
    num m B n aDp, num m B n aDq, num m B n aQi⟩

def CoreOutcome (B : Addr) (n e p q : Nat) (m : Mem) : Prop :=
  match Spec.RsaKeyGen.keyFromPrimes (32 * n) e p q with
  | .inl (.ok key) => slot m B kStatus = 1 ∧ slot m B kOk = 1 ∧ assembledKey B n m = key
  | .inr () => slot m B kStatus = 2 ∧ slot m B kOk = 0
  | .inl (.error _) => slot m B kStatus = 0 ∧ slot m B kOk = 0

abbrev nativeShape (n e p q : Nat) : Prop :=
  2 ^ (32 * n - 1) ≤ p * q ∧ Nat.gcd q (safePrime p) = 1 ∧
    p % 2 = 1 ∧ q % 2 = 1 ∧ Spec.Rsa.exponentValid e = true

theorem qModP_eq_safePrime (p : Nat) : VG.Proof.RsaKeyGen.qModP p = safePrime p := by
  unfold VG.Proof.RsaKeyGen.qModP safePrime
  by_cases H : p < 3
  · have G : ¬3 ≤ p := by omega
    simp [H, G]
  · have G : 3 ≤ p := by omega
    simp [H, G]

theorem sorted_left (p q : Nat) : (if p < q then q else p) = max p q := by
  by_cases H : p < q
  · simp only [H, ite_true, Nat.max_eq_right (Nat.le_of_lt H)]
  · simp only [H, ite_false, Nat.max_eq_left (show q ≤ p by omega)]

theorem sorted_right (p q : Nat) : (if p < q then p else q) = min p q := by
  by_cases H : p < q
  · simp only [H, ite_true, Nat.min_eq_left (Nat.le_of_lt H)]
  · simp only [H, ite_false, Nat.min_eq_right (show q ≤ p by omega)]

theorem keyFromPrimes_native {n e p q x : Nat} (lower : 16 ≤ n) (upper : n ≤ 256)
    (boundP : p < 2 ^ (16 * n)) (boundQ : q < 2 ^ (16 * n)) (boundE : e < 2 ^ 64)
    (congruence : (safePrime (max p q) : Int) ∣ (x : Int) * min p q - Nat.gcd (min p q) (safePrime (max p q)))
    (boundX : x < safePrime (max p q)) :
    Spec.RsaKeyGen.keyFromPrimes (32 * n) e p q =
      match Spec.Rsa.inverse e (Nat.lcm (max p q - 1) (min p q - 1)) with
      | none => .inl (.error .internal)
      | some d => if d ≤ 2 ^ (16 * n) then .inr ()
        else if nativeShape n e (max p q) (min p q) then
          .inl (.ok ⟨max p q * min p q, e, d, max p q, min p q,
            d % (max p q - 1), d % (min p q - 1), x⟩)
        else .inl (.error .internal) := by
  have exponent : 8 * (2 * n) = 16 * n := by omega
  have modulus : 16 * (2 * n) = 32 * n := by omega
  have raw := VG.Proof.RsaKeyGen.keyFromPrimes_code (pLen := 2 * n) (e := e) (P₀ := p) (Q₀ := q) (x := x)
    (by omega) (by omega) (by rw [exponent]; exact boundP) (by rw [exponent]; exact boundQ) boundE
    (by simpa only [sorted_left, sorted_right, qModP_eq_safePrime] using congruence)
    (by simpa only [sorted_left, qModP_eq_safePrime] using boundX)
  simp only [modulus, exponent, sorted_left, sorted_right, qModP_eq_safePrime,
    Bool.and_eq_true, decide_eq_true_eq, and_assoc] at raw
  rw [raw]
  cases inverse : Spec.Rsa.inverse e (Nat.lcm (max p q - 1) (min p q - 1)) with
  | none => rfl
  | some d =>
    by_cases small : d ≤ 2 ^ (16 * n)
    · simp [small]
    · by_cases shape : nativeShape n e (max p q) (min p q) <;> simp_all [nativeShape]

theorem keyFromPrimes_retry {n e p q d : Nat}
    (inverse : Spec.Rsa.inverse e (Nat.lcm (max p q - 1) (min p q - 1)) = some d)
    (small : d ≤ 2 ^ (16 * n)) : Spec.RsaKeyGen.keyFromPrimes (32 * n) e p q = .inr () := by
  have order : (if p < q then (q, p) else (p, q)) = (max p q, min p q) := by
    by_cases H : p < q
    · simp only [H, ite_true, Nat.max_eq_right (Nat.le_of_lt H), Nat.min_eq_left (Nat.le_of_lt H)]
    · simp only [H, ite_false, Nat.max_eq_left (show q ≤ p by omega), Nat.min_eq_right (show q ≤ p by omega)]
  unfold Spec.RsaKeyGen.keyFromPrimes
  rw [order]
  dsimp only
  rw [inverse]
  dsimp only
  rw [show 32 * n / 2 = 16 * n by omega, ite_eq_left small]

end VG.Proof.RsaKeyGen.X86.Key
