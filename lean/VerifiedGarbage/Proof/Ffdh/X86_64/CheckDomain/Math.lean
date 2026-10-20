module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Main
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH domain validation on x86-64: relation to the specification -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem Base.params_none {p : CdP} {s : State} (h : Base p s)
    (hd : p.dl = 2 * p.k) : p.params.q = none := by
  change (if p.dom.length = 3 * p.k then some p.Q else none) = none
  have hk := h.k1
  rw [h.doml, hd, ite_eq_right (by omega)]

theorem Base.params_some {p : CdP} {s : State} (h : Base p s)
    (hd : p.dl = 3 * p.k) : p.params.q = some p.Q := by
  change (if p.dom.length = 3 * p.k then some p.Q else none) = some p.Q
  rw [h.doml, hd, ite_eq_left rfl]

theorem accept_valid {p : CdP} {s : State} (h : Base p s) (hm : p.mv = true) :
    p.accept ↔ Spec.Ffdh.domainValid p.k p.dom = true := by
  have ho := (valid_facts hm h.k1).1
  have hv := domainValid_iff p.k p.dom
  change Spec.Ffdh.domainValid p.k p.dom = true ↔ (p.mv = true ∧
    (1 < p.G ∧ p.G < p.P - 1) ∧ ∀ q, p.params.q = some q →
      (q % 2 = 1 ∧ 1 < q ∧ q < p.P - 1) ∧ (p.P - 1) % q = 0 ∧ p.G ^ q % p.P = 1) at hv
  rw [hv]
  simp only [hm, true_and]
  have heG := lt_pm1 ho p.G
  have heQ := lt_pm1 ho p.Q
  rcases h.dl with hd | hd
  · have hq := h.params_none hd
    simp only [CdP.accept, CdP.gr, hd, true_or, and_true, hq, reduceCtorEq, false_implies, implies_true]
    exact and_congr_right (fun _ => heG)
  · have hq := h.params_some hd
    have hk := h.k1
    have hn : ¬p.dl = 2 * p.k := by omega
    simp only [CdP.accept, hn, false_or, CdP.relation, CdP.gr, CdP.qr, hq, Option.some.injEq, forall_eq']
    rw [heG, heQ]

theorem invalid_modulus {p : CdP} (hm : p.mv = false) : Spec.Ffdh.domainValid p.k p.dom = false := by
  cases hv : Spec.Ffdh.domainValid p.k p.dom with
  | false => rfl
  | true =>
    have he : p.mv = true := domainValid_mod hv
    rw [hm] at he
    contradiction

end VG.Proof.Ffdh.X86_64.CheckDomain
