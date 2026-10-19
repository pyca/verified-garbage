module

public import VerifiedGarbage.Proof.Bignum.X86.CrtCompute
public import VerifiedGarbage.Proof.Bignum.CrtNatural
public import VerifiedGarbage.Proof.Bignum.CrtResult

/-! # Accepted i686 CRT arithmetic agrees with the RSA specification -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt

theorem resultValue_eq {p q dp dq qi x : Nat}
    (hp : 1 < p) (hop : p % 2 = 1) (hq : 1 < q) (hoq : q % 2 = 1) :
    resultValue p q dp dq qi x = VG.Proof.Bignum.crtResult p q dp dq qi x := by
  unfold resultValue coefficientValue residueValue VG.Proof.Bignum.crtResult
  rw [safePrime_of_valid hp hop, safePrime_of_valid hq hoq,
    VG.Proof.Bignum.crt_coefficient_natural (by omega)]
  exact Nat.add_comm _ _

theorem accepted_result {N p q dp dq qi x : Nat}
    (odd : N % 2 = 1) (pBound : p < N) (qBound : q < N) (product : p * q = N) :
    resultValue p q dp dq qi x = VG.Proof.Bignum.crtResult p q dp dq qi x ∧
      resultValue p q dp dq qi x < N := by
  obtain ⟨hq, hoq⟩ := VG.Proof.Bignum.factor_facts product pBound odd
  obtain ⟨hp, hop⟩ := VG.Proof.Bignum.factor_facts (by rw [Nat.mul_comm]; exact product) qBound odd
  refine ⟨resultValue_eq hp hop hq hoq, ?_⟩
  unfold resultValue coefficientValue residueValue
  rw [safePrime_of_valid hp hop, safePrime_of_valid hq hoq, Nat.add_comm, ← product]
  exact VG.Proof.Bignum.crt_recombine_bound (by omega) (Nat.mod_lt _ (by omega))

end VG.Proof.Bignum.X86.Crt
