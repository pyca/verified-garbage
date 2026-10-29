module

public import VerifiedGarbage.Proof.Rsa.X86.RvSquareStep
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Proof.Rsa.X86.RvWindowOps

import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Rsa.X86.RvSquareInit
import VerifiedGarbage.Proof.Rsa.X86.RvScalarOps
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Rsa.RecoverMath
import VerifiedGarbage.Proof.Rsa.X86.RvBase
import VerifiedGarbage.Proof.Rsa.X86.RvCandidateExp
import VerifiedGarbage.Proof.Rsa.X86.RvCandidateNext
/-! # The state and specification of the candidate search -/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/RvSquareLoop.lean`, which only this module imported.
section

/-! # The public bound on the masked squaring search -/

section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa (sqIter)

theorem sqLoop_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m c : Nat}
    {st : Nat × Bool × Bool} (h : SI g s0 A AW V m 0 c st s)
    (value : A mBase = m) (bound : m < 2 ^ (64 * g.n))
    (inverse : (m * V sInv + 1) % 2 ^ 32 = 0) (odd : m % 2 = 1) (hm : 1 < m)
    (one : A aO = 2 ^ (64 * g.n) % m) (neg : A aNg = m - 2 ^ (64 * g.n) % m)
    (ht : V sTc ≤ c) (count : 0 < c) (limit : c ≤ 16384) :
    WP isa (.loop VG.Impl.Rsa.X86.RecoverRt.sqBody .ne) s fun t =>
      SI g s0 A AW V m c 0 (sqIter m (V sTc) c st) t := by
  refine WP.loop (M := isa)
    (fun j u => ∃ k, k + j = c ∧ 0 < j ∧
      SI g s0 A AW V m k (c - k) (sqIter m (V sTc) k st) u)
    ?_ c s ⟨0, by omega, count, h⟩
  intro j u ⟨k, sum, pos, hu⟩
  refine WP.mono (sqBody_step hu value bound inverse odd hm one neg
    (by omega) (by omega) (by omega) (by omega)) fun t ⟨hs, zt⟩ => ?_
  have next : SI g s0 A AW V m (k + 1) (c - (k + 1)) (sqIter m (V sTc) (k + 1) st) t := by
    simpa only [sqIter, Nat.sub_sub] using hs
  by_cases last : k + 1 = c
  · left
    refine ⟨?_, ?_⟩
    · change t.zf.map (!·) = some false
      simp [zt, show c - k - 1 = 0 by omega]
    · simpa only [last, Nat.sub_self] using next
  · right
    refine ⟨?_, j - 1, by omega, k + 1, by omega, by omega, next⟩
    change t.zf.map (!·) = some true
    simp [zt, show c - k - 1 ≠ 0 by omega]

end VG.Proof.Rsa.X86.Recover
end

end

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/RvCandidateSquare.lean`, which only this module imported.
section

/-! # The squaring search following a candidate's exponentiation -/

section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (b2n sqStart sqIter)

theorem candSquare_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m y eLen dLen : Nat}
    (h : KS g s0 (upd A mY (y * 2 ^ (64 * g.n) % m)) liveSq AW [wR] V slotsExp s)
    (value : A mBase = m) (bound : m < 2 ^ (64 * g.n))
    (inverse : (m * V sInv + 1) % 2 ^ 32 = 0) (odd : m % 2 = 1) (hm : 1 < m)
    (one : A aO = 2 ^ (64 * g.n) % m) (neg : A aNg = m - 2 ^ (64 * g.n) % m)
    (yl : y < m)
    (ae : CallArgument s0 g.B g.Z 7 (BitVec.ofNat 32 eLen))
    (ad : CallArgument s0 g.B g.Z 9 (BitVec.ofNat 32 dLen))
    (ht : V sTc ≤ 8 * (dLen + eLen))
    (count : 0 < 8 * (dLen + eLen)) (limit : 8 * (dLen + eLen) ≤ 16384) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.candSquare s fun t => SI g s0 A AW V m (8 * (dLen + eLen)) 0
      (sqIter m (V sTc) (8 * (dLen + eLen)) (sqStart m y)) t := by
  have cop := VG.Proof.Bignum.coprime_pow2 odd (64 * g.n)
  unfold VG.Impl.Rsa.X86.RecoverRt.candSquare VG.Impl.Rsa.X86.RecoverRt.candSquareInit VG.Impl.Rsa.X86.RecoverRt.eqAt
  simp only [seqs]
  refine WP.seq ?_
  refine WP.seq (WP.mono (h.eqS_w (d := sE1) (a := mY) (b := aO)
    (by simp [liveSq]) (by simp [liveSq, liveM]) (by decide) (by decide) (by decide) (by decide))
    fun s1 ⟨h1, _⟩ => ?_)
  refine WP.seq (WP.mono (h1.eqS_w (d := sE2) (a := mY) (b := aNg)
    (by simp [liveSq]) (by simp [liveSq, liveM]) (by decide) (by decide) (by decide) (by decide))
    fun s2 ⟨h2, _⟩ => ?_)
  have eo : (if y * 2 ^ (64 * g.n) % m = A aO then 1 else 0) = b2n (decide (y = 1)) := by
    simp only [one, VG.Proof.Rsa.eq_one_mont cop hm yl rfl]
    simp [b2n]
  have en : (if y * 2 ^ (64 * g.n) % m = A aNg then 1 else 0) = b2n (decide (y = m - 1)) := by
    simp only [neg, VG.Proof.Rsa.eq_neg_mont cop hm yl rfl]
    simp [b2n]
  simp only [upd_self, upd_ne _ _ (by decide : aO ≠ mY), upd_ne _ _ (by decide : aNg ≠ mY), eo, en] at h2
  refine WP.mono (sqInit_ok h2 (e1 := decide (y = 1)) (e2 := decide (y = m - 1))
    (by simp) (by simp) (by simp [upd, sE1, sE2]) (by simp [upd]) ae ad (by omega)) fun s3 h3 => ?_
  have initial : SI g s0 A AW V m 0 (8 * (dLen + eLen)) (sqStart m y) s3 := by
    refine h3.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩) ?_
    intro d hd
    simp only [slotsSq, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [slotsExp, VS, upd, sqStart, b2n, sInv, sCnt, sTc, sCand, sK, sDone, sOk, sE1, sE2]
  exact sqLoop_ok initial value bound inverse odd hm one neg ht count limit

end VG.Proof.Rsa.X86.Recover
end

end

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/RvCandidate.lean`, which only this module imported.
section

/-! # One complete recovery candidate -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (b2n sqStart sqIter)

def candidateState (m t r c j : Nat) : Nat × Bool × Bool :=
  sqIter m t c (sqStart m (Spec.Rsa.powMod (j + 2) r m))

theorem candBody_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m eLen dLen : Nat}
    (h : KS g s0 A liveM AW [wR] V slotsExp s) (zero : A aZ = 0)
    (value : A mBase = m) (bound : m < 2 ^ (64 * g.n))
    (inverse : (m * V sInv + 1) % 2 ^ 32 = 0) (odd : m % 2 = 1) (hm : 1 < m)
    (one : A aO = 2 ^ (64 * g.n) % m) (neg : A aNg = m - 2 ^ (64 * g.n) % m)
    (r2 : A mR2 = 2 ^ (128 * g.n) % m)
    (candidate : V sCand < 100) (baseBound : V sCand + 2 < m)
    (ae : CallArgument s0 g.B g.Z 7 (BitVec.ofNat 32 eLen))
    (ad : CallArgument s0 g.B g.Z 9 (BitVec.ofNat 32 dLen))
    (ht : V sTc ≤ 8 * (dLen + eLen)) (rb : AW wR < 2 ^ (8 * (dLen + eLen)))
    (count : 0 < 8 * (dLen + eLen)) (limit : 8 * (dLen + eLen) ≤ 16384)
    (hwide : 8 * (dLen + eLen) < 32 * g.W) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.candBody s fun t =>
      let st := candidateState m (V sTc) (AW wR) (8 * (dLen + eLen)) (V sCand)
      SI g s0 A AW (upd V sCand (V sCand + 1)) m (8 * (dLen + eLen)) 0 st t ∧
      t.zf = some (!(decide (V sCand + 1 < 100) && !st.2.2)) := by
  have positive : 0 < m := by omega
  unfold VG.Impl.Rsa.X86.RecoverRt.candBody
  simp only [seqs]
  refine WP.seq (WP.mono (candExp_ok h zero value bound inverse odd one r2 candidate baseBound
    ae ad count limit hwide rb) fun s1 hs => ?_)
  refine WP.seq (WP.mono (candSquare_ok hs value bound
    (by simpa only [upd_ne _ _ (by decide : sInv ≠ sCnt)] using inverse) odd hm one neg
    (by rw [VG.Proof.Bignum.powMod_eq]; exact Nat.mod_lt _ positive) ae ad
    (by simpa only [upd_ne _ _ (by decide : sTc ≠ sCnt)] using ht) count limit)
    fun s2 h2 => ?_)
  simp only [upd_ne _ _ (by decide : sTc ≠ sCnt)] at h2
  refine WP.mono (candNext_ok h2 (ok := (candidateState m (V sTc) (AW wR)
    (8 * (dLen + eLen)) (V sCand)).2.2) (by simp [slotsSq]) (by simp [slotsSq])
    (by simpa [candidateState, VS, upd, sCand, sK, sCnt, sDone, sOk] using candidate)
    (by simp only [VS, upd_self]; rfl)) fun t ⟨hout, zt⟩ => ?_
  refine ⟨hout.mono (fun j hj => ⟨hj, rfl⟩) (by simp) ?_, ?_⟩
  · intro d hd
    refine ⟨by simp [hd], ?_⟩
    simp only [slotsSq, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [candidateState, VS, upd, sInv, sCnt, sTc, sCand, sK, sDone, sOk]
  · simp only [VS, upd_ne _ _ (by decide : sCand ≠ sOk),
      upd_ne _ _ (by decide : sCand ≠ sDone), upd_ne _ _ (by decide : sCand ≠ sCnt),
      upd_ne _ _ (by decide : sCand ≠ sK)] at zt
    exact zt

end VG.Proof.Rsa.X86.Recover
end

end

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
