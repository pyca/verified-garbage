module
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw

public import VerifiedGarbage.Proof.Rsa.X86.RvRestFacts
import VerifiedGarbage.Proof.Rsa.X86.RvSearchLoop
public import VerifiedGarbage.Proof.Rsa.X86.RvFinish
import VerifiedGarbage.Proof.Rsa.X86.RvMontTracked
import VerifiedGarbage.Proof.Rsa.X86.RvHalving

/-! # The complete recovery arithmetic after the initial validity test -/

@[expose] public section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Spec.Rsa (splitTwos recoverPrimes)
open VG.Proof.Rsa (pqOf)

def RestResult (g : CallGeometry) (s0 : State) (t : State) : Prop :=
  ∃ y ok tries, Finished g s0 (inputValue g s0.mem 0) y ok t ∧
    y < inputValue g s0.mem 0 ∧ (ok = true → 1 ≤ y) ∧
    ((if ok then some (pqOf (inputValue g s0.mem 0) y) else none), tries) =
      recoverPrimes (inputValue g s0.mem 0) (inputValue g s0.mem 1) (inputValue g s0.mem 2)

theorem rest_ok {g : CallGeometry} {s0 s : State} (inputs : Inputs g s0) (len : Lengths g)
    (h : KS g.toGeo s0 (fun _ => inputValue g s0.mem 0) [aN]
      (fun _ => 2 * (product g s0.mem / 2)) [wM] (fun _ => 0) [] s)
    (go : GoOn (product g s0.mem))
    (bound : inputValue g s0.mem 0 < 2 ^ (64 * g.n))
    (odd : inputValue g s0.mem 0 % 2 = 1) (large : 101 < inputValue g s0.mem 0) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.rest s (RestResult g s0) := by
  obtain ⟨ae, ad⟩ := inputArguments inputs
  obtain ⟨count, limit⟩ := inputs.countBounds
  obtain ⟨evenValue, positive, _, fit⟩ := exponent_facts go
  obtain ⟨tpos, tbound, rbound⟩ := split_facts go
  have halves : hvs (exponent g s0.mem) (countBits g) =
      ((splitTwos (exponent g s0.mem)).2, (splitTwos (exponent g s0.mem)).1) :=
    VG.Proof.Rsa.halve_done positive fit
  unfold VG.Impl.Rsa.X86.RecoverRt.rest
  simp only [seqs]
  refine WP.seq (WP.mono (halving_ok h (by simp) evenValue ae ad count limit) fun s1 h1 => ?_)
  change KS g.toGeo s0 (fun _ => inputValue g s0.mem 0) [aN]
    (AWh (exponent g s0.mem) (countBits g)) [wR]
    (Vh (countBits g) (exponent g s0.mem) (countBits g)) [sTc, sCnt] s1 at h1
  have aw : AWh (exponent g s0.mem) (countBits g) = fun _ => (splitTwos (exponent g s0.mem)).2 :=
    funext fun _ => congrArg Prod.fst halves
  rw [aw] at h1
  simp only [Vh, halves, Nat.sub_self] at h1
  refine WP.seq (WP.mono (mont_ok h1 rfl bound odd (by omega)) fun s2 ⟨h2, mr⟩ => ?_)
  obtain ⟨I, tracked, inverse⟩ := h2.trackInverse mr (by decide)
  refine WP.seq (WP.mono (candLoop_ok
    (by simp [AM, upd, aZ, aNg, aO, mXm, mR2, mBase, aOne])
    (by simp [AM, upd, mBase, aNg, aO, mXm, mR2]) bound
    (by simpa only [upd_self] using inverse) odd large
    (by simp [AM, upd, aO, aNg]) (by simp [AM, upd])
    (by simp [AM, upd, mR2, aNg, aO, mXm]) ae ad
    (by simpa [countBits, upd, sTc, sInv, sCnt] using tbound) rbound count limit inputs.countWide tracked
    (by simp [upd, sCnt, sInv]) (by simpa [upd, sTc, sInv, sCnt] using tpos))
    fun s3 ⟨j, st, _, hs, small, pos, found⟩ => ?_)
  refine WP.mono (fin_ok inputs len hs
    (by simp [AM, upd, mBase, aNg, aO, mXm, mR2])
    (by simp [AM, upd, aN, aNg, aO, mXm, mR2, mBase, aOne, aZ]) bound
    (by simpa [VJ, upd, sInv, sCand, sCnt] using inverse) odd (by omega)
    (by simp [AM, upd, aZ, aNg, aO, mXm, mR2, mBase, aOne])
    (by simp [AM, upd, aOne, aNg, aO, mXm, mR2, mBase]) small) fun t finished => ?_
  refine ⟨st.1, st.2.2, j + 1, finished, small, pos, ?_⟩
  rw [VG.Proof.Rsa.recoverPrimes_go go]
  simpa only [upd_ne _ _ (by decide : sTc ≠ sInv), upd_ne _ _ (by decide : sTc ≠ sCnt), upd_self,
    exponent, product, Spec.Rsa.recoverTries] using found

end VG.Proof.Rsa.X86.Recover
