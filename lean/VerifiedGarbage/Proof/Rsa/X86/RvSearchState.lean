module

public import VerifiedGarbage.Proof.Rsa.X86.RvCandidate
import VerifiedGarbage.Proof.Bignum.Math

/-! # The state and specification of the candidate search -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (sqRes pqOf)
open VG.Spec.Rsa (recoverPrimes recoverTries)

def VJ (V : Nat → Nat) (j : Nat) : Nat → Nat := upd (upd V sCnt 0) sCand j

def CI (g : Geo) (s0 : State) (A AW V : Nat → Nat) (j : Nat) (s : State) : Prop :=
  KS g s0 A liveM AW [wR] (VJ V j) slotsExp s

def SearchResult (g : Geo) (s0 : State) (A AW V : Nat → Nat) (m c : Nat) (s : State) : Prop :=
  ∃ j st, j < 100 ∧ SI g s0 A AW (VJ V (j + 1)) m c 0 st s ∧ st.1 < m ∧ (st.2.2 = true → 1 ≤ st.1) ∧
    ((if st.2.2 then some (pqOf m st.1) else none), j + 1) =
      recoverPrimes.go m (V sTc) (AW wR) 100

theorem candidate_go {m t r c j : Nat} (hj : j < 100) (ht : 1 ≤ t) (hc : t ≤ c) :
    recoverPrimes.go m t r (100 - j) =
      if (candidateState m t r c j).2.2 then
        (some (pqOf m (candidateState m t r c j).1), j + 1)
      else recoverPrimes.go m t r (100 - (j + 1)) := by
  have eq := VG.Proof.Rsa.go_eq m t r (show j < recoverTries from hj)
  rw [← VG.Proof.Rsa.sq_result (n := m) (r := r) (g := j + 2) ht hc] at eq
  change recoverPrimes.go m t r (100 - j) =
    (match sqRes (candidateState m t r c j) with
      | some y => (some (pqOf m y), j + 1)
      | none => recoverPrimes.go m t r (100 - (j + 1))) at eq
  rw [eq]
  unfold sqRes
  by_cases hs : (candidateState m t r c j).2.2 = true <;> simp [hs]

theorem candidate_lt {m t r c j : Nat} (hm : 0 < m) : (candidateState m t r c j).1 < m := by
  apply VG.Proof.Rsa.sqIter_lt hm
  change Spec.Rsa.powMod (j + 2) r m < m
  rw [VG.Proof.Bignum.powMod_eq]
  exact Nat.mod_lt _ hm

theorem candidate_positive {m t r c j : Nat} (ht : 1 ≤ t) (hc : t ≤ c)
    (ok : (candidateState m t r c j).2.2 = true) : 1 ≤ (candidateState m t r c j).1 := by
  have result := VG.Proof.Rsa.sq_result (n := m) (r := r) (g := j + 2) ht hc
  change sqRes (candidateState m t r c j) = _ at result
  simp only [sqRes, ok, ite_true] at result
  have square := VG.Proof.Rsa.recoverStep_some result.symm
  by_contra h
  have zero : (candidateState m t r c j).1 = 0 := by omega
  simp only [zero, Nat.zero_mul, Nat.zero_mod] at square
  omega

theorem SI.nextCandidate {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m c j : Nat}
    {st : Nat × Bool × Bool} (h : SI g s0 A AW (VJ V j) m c 0 st s) : CI g s0 A AW V j s := by
  refine h.mono ?_ (by simp) ?_
  · intro i hi
    refine ⟨by simp [liveSq, hi], ?_⟩
    simp only [liveM, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [upd, mY, aNg, aO, mR2, mBase, aOne, aZ, aN]
  · intro d hd
    simp only [slotsExp, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [slotsSq, VS, VJ, upd, sInv, sCnt, sTc, sCand, sK, sDone, sOk]

end VG.Proof.Rsa.X86.Recover
