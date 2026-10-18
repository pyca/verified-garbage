module

public import VerifiedGarbage.Proof.Rsa.X86.RvCandidateBodyTiming
public import VerifiedGarbage.Proof.Rsa.X86.RvSearchLoop

/-! # The declared attempt count determines the recovery search's stopping condition -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Spec.Rsa (recoverPrimes)

abbrev CandidateData.tries {g : Geo} {m eLen dLen : Nat} (C : CandidateData g m eLen dLen) : Nat :=
  (recoverPrimes.go m (C.V sTc) (C.AW wR) 100).2

def CandidateData.atCandidate {g : Geo} {m eLen dLen : Nat}
    (C : CandidateData g m eLen dLen) (j : Nat) (hj : j < 100) : CandidateData g m eLen dLen where
  s0 := C.s0
  A := C.A
  AW := C.AW
  V := VJ C.V j
  zero := C.zero
  value := C.value
  bound := C.bound
  inverse := by simpa [VJ, upd, sInv, sCnt, sCand] using C.inverse
  odd := C.odd
  large := C.large
  one := C.one
  neg := C.neg
  r2 := C.r2
  candidate := by simpa only [VJ, upd_self] using hj
  baseBound := by simp only [VJ, upd_self]; have := C.large; omega
  ae := C.ae
  ad := C.ad
  tc := by simpa [VJ, upd, sTc, sCnt, sCand] using C.tc
  rb := C.rb
  count := C.count
  limit := C.limit

theorem candidate_condition {m t r c j : Nat} (ht : 1 ≤ t) (hc : t ≤ c)
    (hj : j < (recoverPrimes.go m t r 100).2)
    (hgo : recoverPrimes.go m t r 100 = recoverPrimes.go m t r (100 - j)) :
    (decide (j + 1 < 100) && !(candidateState m t r c j).2.2) =
      decide (j + 1 < (recoverPrimes.go m t r 100).2) := by
  have some : (Spec.Rsa.recoverStep m t r (j + 2)).isSome = (candidateState m t r c j).2.2 := by
    have result := VG.Proof.Rsa.sq_result (n := m) (r := r) (g := j + 2) ht hc
    change VG.Proof.Rsa.sqRes (candidateState m t r c j) = _ at result
    rw [← result]
    unfold VG.Proof.Rsa.sqRes
    cases (candidateState m t r c j).2.2 <;> rfl
  have condition := VG.Proof.Rsa.cand_cond m t r
    (show j < (recoverPrimes.go m t r Spec.Rsa.recoverTries).2 from hj) hgo
  simp only [Bool.not_not, some, Spec.Rsa.recoverTries] at condition
  exact condition

theorem searchBody_ok {g : Geo} {m eLen dLen : Nat} (C : CandidateData g m eLen dLen)
    {j : Nat} (hj : j < 100) {s : State} (hs : CI g C.s0 C.A C.AW C.V j s) :
    WP isa (candBody g.n) s fun t =>
      SI g C.s0 C.A C.AW (VJ C.V (j + 1)) m (8 * (dLen + eLen)) 0
        (candidateState m (C.V sTc) (C.AW wR) (8 * (dLen + eLen)) j) t ∧
      t.zf = some (!(decide (j + 1 < 100) &&
        !(candidateState m (C.V sTc) (C.AW wR) (8 * (dLen + eLen)) j).2.2)) :=
  candBody_index C.zero C.value C.bound C.inverse C.odd C.large C.one C.neg C.r2
    C.ae C.ad C.tc C.rb C.count C.limit hs hj

def SearchInvariant {g : Geo} {m eLen dLen : Nat}
    (C : CandidateData g m eLen dLen) (j : Nat) (s : State) : Prop :=
  CI g C.s0 C.A C.AW C.V j s ∧ j < C.tries ∧
    recoverPrimes.go m (C.V sTc) (C.AW wR) 100 = recoverPrimes.go m (C.V sTc) (C.AW wR) (100 - j)

theorem searchBody_post {g : Geo} {m eLen dLen : Nat} (C : CandidateData g m eLen dLen)
    (tc : 1 ≤ C.V sTc) {j : Nat} {s : State} (h : SearchInvariant C j s) :
    WP isa (candBody g.n) s fun t =>
      isa.eval .ne t = some (decide (j + 1 < C.tries)) ∧
      (isa.eval .ne t = some true → SearchInvariant C (j + 1) t) := by
  have top := VG.Proof.Rsa.go_le m (C.V sTc) (C.AW wR) 100 (by decide)
  change C.tries ≤ 100 at top
  have hj : j < 100 := by have prior := h.2.1; omega
  refine WP.mono (searchBody_ok C hj h.1) fun t ⟨ht, zt⟩ => ?_
  have condition := candidate_condition tc C.tc h.2.1 h.2.2
  have flag : isa.eval .ne t = some (decide (j + 1 < C.tries)) := by
    change t.zf.map (!·) = _
    rw [zt]
    simpa only [Option.map_some, Bool.not_not] using congrArg some condition
  refine ⟨flag, ?_⟩
  intro more
  have next : j + 1 < C.tries := of_decide_eq_true (Option.some.inj (flag.symm.trans more))
  have continuing : (decide (j + 1 < 100) &&
      Bool.not (candidateState m (C.V sTc) (C.AW wR) (8 * (dLen + eLen)) j).2.2) = true := by
    rw [condition]
    exact decide_eq_true next
  have failed : (candidateState m (C.V sTc) (C.AW wR) (8 * (dLen + eLen)) j).2.2 = false := by
    have both : (j + 1 < 100) ∧ (candidateState m (C.V sTc) (C.AW wR) (8 * (dLen + eLen)) j).2.2 = false := by
      simpa only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] using continuing
    exact both.2
  refine ⟨ht.nextCandidate, next, ?_⟩
  exact h.2.2.trans (by rw [candidate_go hj tc C.tc, failed]; rfl)

end VG.Proof.Rsa.X86.Recover
