module
public import VerifiedGarbage.Proof.Rsa.X86.RvTimeFusedSearch
import VerifiedGarbage.Proof.Rsa.X86.RvFusedRest
public import VerifiedGarbage.Proof.Rsa.X86.RvNumbers

import VerifiedGarbage.Proof.Rsa.X86.RvHalving
public import VerifiedGarbage.Proof.Rsa.X86.RvLoads
public import VerifiedGarbage.Proof.Rsa.X86.RvMont
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.TCB.X86.Isa

/-! # Arithmetic preparation supplies the candidate search's public context -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Spec.Rsa (splitTwos recoverPrimes)

structure FusedPrepared (g : CallGeometry) (s0 s : State) (m : Nat := inputValue g s0.mem 0) where
  context : CandidateData g.toGeo m (g.args 7).toNat (g.args 9).toNat
  modulus : context.A aN = m
  unit : context.A aOne = 1
  state : KS g.toGeo context.s0 context.A liveM context.AW [wR]
    context.V [sInv, sTc, sCnt] s
  counter : context.V sCnt = 0
  positive : 0<context.AW wR
  even : context.AW wR%2=0
  attempts : context.fusedTries = (recoverPrimes m
    (inputValue g s0.mem 1) (inputValue g s0.mem 2)).2

theorem fusedPrepareMont_ok {g : CallGeometry} {s0 s : State} (inputs : Inputs g s0)
    (h : KS g.toGeo s0 (fun _ => inputValue g s0.mem 0) [aN]
      (fun _ => 2 * (product g s0.mem / 2)) [wM] (fun _ => 0) [] s)
    (go : GoOn (product g s0.mem))
    (bound : inputValue g s0.mem 0 < 2 ^ (64 * g.n))
    (odd : inputValue g s0.mem 0 % 2 = 1) (large : 101 < inputValue g s0.mem 0) :
    WP isa (.seq VG.Impl.Rsa.X86.RecoverRt.fusedPrepare VG.Impl.Rsa.X86.RecoverRt.mont) s (fun t => Nonempty (FusedPrepared g s0 t)) := by
  obtain ⟨ae, ad⟩ := inputArguments inputs
  obtain ⟨count, limit⟩ := inputs.countBounds
  obtain ⟨evenValue, positive, even, fit⟩ := exponent_facts go
  refine WP.seq (WP.mono (fusedPrepare_ok h evenValue) fun s1 h1 => ?_)
  refine WP.mono (mont_ok h1 rfl bound odd (by omega)) fun s2 ⟨h2, mr⟩ => ?_
  obtain ⟨I, tracked, inverse⟩ := h2.trackInverse mr (by decide)
  let C : CandidateData g.toGeo (inputValue g s0.mem 0) (g.args 7).toNat (g.args 9).toNat := {
    s0 := s0
    A := AM (fun _ => inputValue g s0.mem 0) g.n (inputValue g s0.mem 0)
    AW := fun _ => exponent g s0.mem
    V := upd (fun _ => 0) sInv I
    zero := by simp [AM, upd, aZ, aNg, aO, mXm, mR2, mBase, aOne]
    value := by simp [AM, upd, mBase, aNg, aO, mXm, mR2]
    bound := bound
    inverse := by simpa only [upd_self] using inverse
    odd := odd
    large := large
    one := by simp [AM, upd, aO, aNg]
    neg := by simp [AM, upd]
    r2 := by simp [AM, upd, mR2, aNg, aO, mXm]
    candidate := by simp [upd, sCand, sInv]
    baseBound := by simp [upd, sCand, sInv]; omega
    ae := ae
    ad := ad
    tc := by simp [upd,sTc,sInv]
    rb := fit
    count := count
    limit := limit
    wide := inputs.countWide }
  refine ⟨⟨C, ?_, ?_, tracked, ?_, positive, even, ?_⟩⟩
  · simp [C, AM, upd, aN, aNg, aO, mXm, mR2, mBase, aOne, aZ]
  · simp [C, AM, upd, aOne, aNg, aO, mXm, mR2, mBase]
  · simp [C, upd, sCnt, sInv]
  · rw [VG.Proof.Rsa.recoverPrimes_go go]
    rfl

end VG.Proof.Rsa.X86.Recover
