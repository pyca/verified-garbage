module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPhaseA
import VerifiedGarbage.Proof.Bignum.CrtResult
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# The RSA private-key operation on PPC64LE: what the mask gives

`mask_true`: under the mask, the checks hold and `p` and `q` are odd and
above 1. `masked_ok`: the masked `p` and `q` are odd and above 1 and below
`2^(64 w)` for their working spaces, `m₂` below `256^qL`, `qInv` below `p`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG

theorem mask_true {nb cb pb qb ib : List Byte} {k : Nat} (hk : 64 ≤ k) (hpl : pb.length < k)
    (hql : qb.length < k)
    (h : crtMask (Spec.Rsa.os2ip nb) k (Spec.Rsa.os2ip cb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
      (Spec.Rsa.os2ip ib) = true) :
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true ∧ Spec.Rsa.os2ip cb < Spec.Rsa.os2ip nb ∧
      Spec.Rsa.os2ip ib < Spec.Rsa.os2ip pb ∧ Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb ∧
      1 < Spec.Rsa.os2ip pb ∧ Spec.Rsa.os2ip pb % 2 = 1 ∧ 1 < Spec.Rsa.os2ip qb ∧ Spec.Rsa.os2ip qb % 2 = 1 := by
  simp only [crtMask, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hv, hc⟩, hi⟩, hpq⟩ := h
  obtain ⟨hodd, _, hP, hQ⟩ := VG.Proof.Bignum.crt_bounds_of hv hk rfl hpl rfl hql
  obtain ⟨hq1, hqo⟩ := VG.Proof.Bignum.factor_facts hpq hP hodd
  obtain ⟨hp1, hpo⟩ := VG.Proof.Bignum.factor_facts (by rw [Nat.mul_comm]; exact hpq) hQ hodd
  exact ⟨hv, hc, hi, hpq, hp1, hpo, hq1, hqo⟩

theorem pow256_le {L w : Nat} (h : L ≤ 8 * w) : 256 ^ L ≤ 2 ^ (64 * w) := by
  rw [VG.Proof.Bignum.pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by omega)

theorem os2ip_lt' (bs : List Byte) {L : Nat} (h : bs.length = L) : Spec.Rsa.os2ip bs < 256 ^ L := by
  have := VG.Proof.Bignum.os2ip_lt bs; rwa [h] at this

end VG.Proof.Bignum.PPC64LE.Crt
