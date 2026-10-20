module
public import VerifiedGarbage.Proof.Rsa.X86.RvSquareStep
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall

import VerifiedGarbage.Proof.Rsa.X86.RvCandidateExp
import VerifiedGarbage.Proof.Rsa.X86.RvCandidateSquare
import VerifiedGarbage.Proof.Rsa.X86.RvCandidateNext
import VerifiedGarbage.Proof.Bignum.Math

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
    WP isa (candBody g.n) s fun t =>
      let st := candidateState m (V sTc) (AW wR) (8 * (dLen + eLen)) (V sCand)
      SI g s0 A AW (upd V sCand (V sCand + 1)) m (8 * (dLen + eLen)) 0 st t ∧
      t.zf = some (!(decide (V sCand + 1 < 100) && !st.2.2)) := by
  have positive : 0 < m := by omega
  unfold candBody
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
