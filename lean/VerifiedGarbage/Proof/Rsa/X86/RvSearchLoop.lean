module

public import VerifiedGarbage.Proof.Rsa.X86.RvSearchState

/-! # The bounded search for a factor-producing recovery candidate -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (pqOf)
open VG.Spec.Rsa (recoverPrimes)

section
variable {g : Geo} {s0 : State} {A AW V : Nat → Nat} {m eLen dLen : Nat}
  (zero : A aZ = 0) (value : A mBase = m) (bound : m < 2 ^ (64 * g.n))
  (inverse : (m * V sInv + 1) % 2 ^ 32 = 0) (odd : m % 2 = 1) (large : 101 < m)
  (one : A aO = 2 ^ (64 * g.n) % m) (neg : A aNg = m - 2 ^ (64 * g.n) % m)
  (r2 : A mR2 = 2 ^ (128 * g.n) % m)
  (ae : CallArgument s0 g.B g.Z 7 (BitVec.ofNat 32 eLen))
  (ad : CallArgument s0 g.B g.Z 9 (BitVec.ofNat 32 dLen))
  (ht : V sTc ≤ 8 * (dLen + eLen)) (rb : AW wR < 2 ^ (8 * (dLen + eLen)))
  (count : 0 < 8 * (dLen + eLen)) (limit : 8 * (dLen + eLen) ≤ 16384)
  (hwide : 8 * (dLen + eLen) < 32 * g.W)

include zero value bound inverse odd large one neg r2 ae ad ht rb count limit hwide

theorem candBody_index {s : State} {j : Nat} (h : CI g s0 A AW V j s) (hj : j < 100) :
    WP isa (candBody g.n) s fun t =>
      SI g s0 A AW (VJ V (j + 1)) m (8 * (dLen + eLen)) 0
        (candidateState m (V sTc) (AW wR) (8 * (dLen + eLen)) j) t ∧
      t.zf = some (!(decide (j + 1 < 100) &&
        !(candidateState m (V sTc) (AW wR) (8 * (dLen + eLen)) j).2.2)) := by
  refine WP.mono (candBody_ok h zero value bound
    (by simpa [VJ, upd, sInv, sCnt, sCand] using inverse) odd (by omega) one neg r2
    (by simpa only [VJ, upd_self] using hj) (by simp only [VJ, upd_self]; omega)
    ae ad (by simpa [VJ, upd, sTc, sCnt, sCand] using ht) rb count limit hwide) fun t result => ?_
  simpa only [VJ, upd_self, upd_ne _ _ (by decide : sTc ≠ sCand),
    upd_ne _ _ (by decide : sTc ≠ sCnt), upd_twice] using result

theorem searchLoop_ok {s : State} (h : CI g s0 A AW V 0 s) (ht1 : 1 ≤ V sTc) :
    WP isa (.loop (candBody g.n) .ne) s (SearchResult g s0 A AW V m (8 * (dLen + eLen))) := by
  refine WP.loop (M := isa)
    (fun left u => ∃ j, j + left = 100 ∧ 0 < left ∧ CI g s0 A AW V j u ∧
      recoverPrimes.go m (V sTc) (AW wR) 100 = recoverPrimes.go m (V sTc) (AW wR) (100 - j))
    ?_ 100 s ⟨0, rfl, by decide, h, rfl⟩
  intro left u ⟨j, sum, pos, hu, go⟩
  have hj : j < 100 := by omega
  refine WP.mono (candBody_index zero value bound inverse odd large one neg r2 ae ad ht rb count limit hwide
    hu hj)
    fun t ⟨hs, zt⟩ => ?_
  have step := go.trans (candidate_go hj ht1 ht)
  have small := candidate_lt (m := m) (t := V sTc) (r := AW wR)
    (c := 8 * (dLen + eLen)) (j := j) (by omega)
  by_cases success : (candidateState m (V sTc) (AW wR) (8 * (dLen + eLen)) j).2.2 = true
  · left
    refine ⟨?_, j, _, hj, hs, small, candidate_positive ht1 ht, ?_⟩
    · change t.zf.map (!·) = some false
      simp [zt, success]
    · simpa only [success, ite_true] using step.symm
  · have failed : (candidateState m (V sTc) (AW wR) (8 * (dLen + eLen)) j).2.2 = false := by
      cases eq : (candidateState m (V sTc) (AW wR) (8 * (dLen + eLen)) j).2.2 <;> simp_all
    simp only [failed, Bool.false_eq_true, ite_false] at step
    by_cases last : j + 1 = 100
    · left
      refine ⟨?_, j, _, hj, hs, small, candidate_positive ht1 ht, ?_⟩
      · change t.zf.map (!·) = some false
        simp [zt, last]
      · rw [last, Nat.sub_self] at step
        change recoverPrimes.go m (V sTc) (AW wR) 100 = (none, 100) at step
        simpa only [failed, Bool.false_eq_true, ite_false, last] using step.symm
    · right
      refine ⟨?_, left - 1, by omega, j + 1, by omega, by omega, hs.nextCandidate, step⟩
      change t.zf.map (!·) = some true
      simp [zt, failed, show j + 1 < 100 by omega]

theorem candLoop_ok {s : State}
    (h : KS g s0 A liveM AW [wR] V [sInv, sTc, sCnt] s)
    (vc : V sCnt = 0) (ht1 : 1 ≤ V sTc) :
    WP isa (candLoop g.n) s (SearchResult g s0 A AW V m (8 * (dLen + eLen))) := by
  unfold candLoop
  refine WP.seq (wp_movS rfl fun u U _ => ?_)
  have hu := h.of_rest U.keeps (by decide) U.mem
  refine WP.mono (hu.storeSlot (d := sCand) (by decide) .eax) fun v ⟨hv, _, _⟩ => ?_
  rw [U.gpr] at hv
  have initial : CI g s0 A AW V 0 v := by
    refine hv.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩) ?_
    intro d hd
    simp only [slotsExp, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [VJ, upd, sInv, sTc, sCnt, sCand] <;> exact vc
  exact searchLoop_ok zero value bound inverse odd large one neg r2 ae ad ht rb count limit hwide initial ht1

end
end VG.Proof.Rsa.X86.Recover
