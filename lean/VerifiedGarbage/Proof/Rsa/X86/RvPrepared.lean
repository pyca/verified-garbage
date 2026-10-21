module
public import VerifiedGarbage.Proof.Rsa.X86.RvSearchTimingState
public import VerifiedGarbage.Proof.Rsa.X86.RvNumbers

import VerifiedGarbage.Proof.Rsa.X86.RvMontTracked
import VerifiedGarbage.Proof.Rsa.X86.RvRestFacts
import VerifiedGarbage.Proof.Rsa.X86.RvHalving

/-! # Arithmetic preparation supplies the candidate search's public context -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Spec.Rsa (splitTwos recoverPrimes)

structure Prepared (g : CallGeometry) (s0 s : State) (m : Nat := inputValue g s0.mem 0) where
  context : CandidateData g.toGeo m (g.args 7).toNat (g.args 9).toNat
  baseline : context.s0 = s0
  modulus : context.A aN = m
  unit : context.A aOne = 1
  state : KS g.toGeo context.s0 context.A liveM context.AW [wR]
    context.V [sInv, sTc, sCnt] s
  counter : context.V sCnt = 0
  twos : 1 ≤ context.V sTc
  attempts : context.tries = (recoverPrimes m
    (inputValue g s0.mem 1) (inputValue g s0.mem 2)).2

theorem prepare_ok {g : CallGeometry} {s0 s : State} (inputs : Inputs g s0)
    (h : KS g.toGeo s0 (fun _ => inputValue g s0.mem 0) [aN]
      (fun _ => 2 * (product g s0.mem / 2)) [wM] (fun _ => 0) [] s)
    (go : GoOn (product g s0.mem))
    (bound : inputValue g s0.mem 0 < 2 ^ (64 * g.n))
    (odd : inputValue g s0.mem 0 % 2 = 1) (large : 101 < inputValue g s0.mem 0) :
    WP isa (.seq VG.Impl.Rsa.X86.RecoverRt.halving VG.Impl.Rsa.X86.RecoverRt.mont) s (fun t => Nonempty (Prepared g s0 t)) := by
  obtain ⟨ae, ad⟩ := inputArguments inputs
  obtain ⟨count, limit⟩ := inputs.countBounds
  obtain ⟨evenValue, positive, _, fit⟩ := exponent_facts go
  obtain ⟨tpos, tbound, rbound⟩ := split_facts go
  have halves : hvs (exponent g s0.mem) (countBits g) =
      ((splitTwos (exponent g s0.mem)).2, (splitTwos (exponent g s0.mem)).1) :=
    VG.Proof.Rsa.halve_done positive fit
  refine WP.seq (WP.mono (halving_ok h (by simp) evenValue ae ad count limit) fun s1 h1 => ?_)
  change KS g.toGeo s0 (fun _ => inputValue g s0.mem 0) [aN]
    (AWh (exponent g s0.mem) (countBits g)) [wR]
    (Vh (countBits g) (exponent g s0.mem) (countBits g)) [sTc, sCnt] s1 at h1
  have aw : AWh (exponent g s0.mem) (countBits g) = fun _ => (splitTwos (exponent g s0.mem)).2 :=
    funext fun _ => congrArg Prod.fst halves
  rw [aw] at h1
  simp only [Vh, halves, Nat.sub_self] at h1
  refine WP.mono (mont_ok h1 rfl bound odd (by omega)) fun s2 ⟨h2, mr⟩ => ?_
  obtain ⟨I, tracked, inverse⟩ := h2.trackInverse mr (by decide)
  let C : CandidateData g.toGeo (inputValue g s0.mem 0) (g.args 7).toNat (g.args 9).toNat := {
    s0 := s0
    A := AM (fun _ => inputValue g s0.mem 0) g.n (inputValue g s0.mem 0)
    AW := fun _ => (splitTwos (exponent g s0.mem)).2
    V := upd (upd (upd (fun _ => 0) sTc (splitTwos (exponent g s0.mem)).1) sCnt 0) sInv I
    zero := by simp [AM, upd, aZ, aNg, aO, mXm, mR2, mBase, aOne]
    value := by simp [AM, upd, mBase, aNg, aO, mXm, mR2]
    bound := bound
    inverse := by simpa only [upd_self] using inverse
    odd := odd
    large := large
    one := by simp [AM, upd, aO, aNg]
    neg := by simp [AM, upd]
    r2 := by simp [AM, upd, mR2, aNg, aO, mXm]
    candidate := by simp [upd, sCand, sInv, sCnt, sTc]
    baseBound := by simp [upd, sCand, sInv, sCnt, sTc]; omega
    ae := ae
    ad := ad
    tc := by simpa [countBits, upd, sTc, sInv, sCnt] using tbound
    rb := rbound
    count := count
    limit := limit
    wide := inputs.countWide }
  refine ⟨⟨C, rfl, ?_, ?_, tracked, ?_, ?_, ?_⟩⟩
  · simp [C, AM, upd, aN, aNg, aO, mXm, mR2, mBase, aOne, aZ]
  · simp [C, AM, upd, aOne, aNg, aO, mXm, mR2, mBase]
  · simp [C, upd, sCnt, sInv]
  · simpa [C, upd, sTc, sInv, sCnt] using tpos
  · rw [VG.Proof.Rsa.recoverPrimes_go go]
    simp only [CandidateData.tries, C, upd_ne _ _ (by decide : sTc ≠ sInv),
      upd_ne _ _ (by decide : sTc ≠ sCnt), upd_self, exponent, product, Spec.Rsa.recoverTries]

end VG.Proof.Rsa.X86.Recover
