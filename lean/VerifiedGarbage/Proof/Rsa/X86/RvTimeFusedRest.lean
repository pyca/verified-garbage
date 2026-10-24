module
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw

import VerifiedGarbage.Proof.Rsa.X86.RvFusedPrepared
import VerifiedGarbage.Proof.Rsa.X86.RvTimeRest
import VerifiedGarbage.Proof.Rsa.X86.RvTimeFusedCheck
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Rsa.X86.RvCandidateData
public import VerifiedGarbage.Proof.Rsa.X86.RvFusedSearch
public import VerifiedGarbage.Proof.Rsa.X86.RvNumbers
public import VerifiedGarbage.Proof.Rsa.X86.RvTimeBase
public import VerifiedGarbage.Proof.Rsa.X86.RvTimePrepare
import VerifiedGarbage.Proof.Rsa.X86.RvFusedRest

/-! Fused recovery leaks only the existing public geometry, modulus and attempt count. -/
@[expose] public section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Spec.Rsa (recoverPrimes)

omit rsaBatchLaw in
theorem CandidateData.fusedSearch_ok {g : Geo} {n eLen dLen : Nat} (C : CandidateData g n eLen dLen)
    (modulus : C.A aN=n) (ep : 0<C.AW wR) (even : C.AW wR%2=0)
    {s : State} (h : KS g C.s0 C.A liveM C.AW [wR] C.V [sInv,sTc,sCnt] s) (vc : C.V sCnt=0) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.fusedLoop s (FusedSearchResult g C.s0 C.A C.AW C.V n) :=
  fusedLoop_ok C.value modulus C.zero C.bound C.inverse C.odd (by have := C.large; omega)
    C.one C.neg C.ae C.ad ep even C.rb C.count C.limit C.wide h vc

theorem fusedRest_relCT (g : CallGeometry) (pg : PubG g.toGeo) (s0 t0 : State)
    (left : Inputs g s0) (right : Inputs g t0)
    (goS : GoOn (product g s0.mem)) (goT : GoOn (product g t0.mem))
    (boundS : inputValue g s0.mem 0 < 2 ^ (64 * g.n))
    (boundT : inputValue g t0.mem 0 < 2 ^ (64 * g.n))
    (oddS : inputValue g s0.mem 0 % 2 = 1) (oddT : inputValue g t0.mem 0 % 2 = 1)
    (largeS : 101 < inputValue g s0.mem 0) (largeT : 101 < inputValue g t0.mem 0)
    (modulus : inputValue g s0.mem 0 = inputValue g t0.mem 0)
    (tries : (recoverPrimes (inputValue g s0.mem 0) (inputValue g s0.mem 1) (inputValue g s0.mem 2)).2 =
      (recoverPrimes (inputValue g t0.mem 0) (inputValue g t0.mem 1) (inputValue g t0.mem 2)).2) :
    RelCT isa (fun s t => NumbersState g s0 s ∧ NumbersState g t0 t) VG.Impl.Rsa.X86.RecoverRt.fusedRest
      (fun _ _ => True) := by
  intro s t tr ur sf tf ⟨hs, ht⟩ es et
  cases es with
  | @seq _ _ _ u _ _ _ e1 er =>
  cases et with
  | @seq _ _ _ v _ _ _ f1 fr =>
  cases er with
  | @seq _ _ _ x _ _ _ e2 er =>
  cases fr with
  | @seq _ _ _ y _ _ _ f2 fr =>
  have eq1 := pub_trace pg fusedPrepareCheck hs ht e1 f1
  obtain ⟨evS,_,_,_⟩ := exponent_facts goS
  obtain ⟨evT,_,_,_⟩ := exponent_facts goT
  have is := wp_result (fusedPrepare_ok hs evS) e1
  have it := wp_result (fusedPrepare_ok ht evT) f1
  have eq2 := (mont_relCT pg (s0 := s0) (t0 := t0) (A := fun _ => inputValue g s0.mem 0)
    (B := fun _ => inputValue g t0.mem 0) rfl rfl boundS boundT oddS oddT (by omega) (by omega)
    _ _ _ _ _ _ ⟨is, it⟩ e2 f2).1
  obtain ⟨p⟩ := wp_result (fusedPrepareMont_ok left hs goS boundS oddS largeS) (Exec.seq e1 e2)
  obtain ⟨q⟩ := wp_result (fusedPrepareMont_ok right ht goT boundT oddT largeT) (Exec.seq f1 f2)
  rw [← modulus] at q
  have tries' := tries
  rw [← modulus] at tries'
  have attempts : p.context.fusedTries = q.context.fusedTries :=
    p.attempts.trans (tries'.trans q.attempts.symm)
  cases er with
  | @seq _ _ _ a _ _ _ e3 e4 =>
  cases fr with
  | @seq _ _ _ b _ _ _ f3 f4 =>
  have eq3 := (fusedLoop_relCT pg p.context q.context p.modulus q.modulus p.positive q.positive p.even q.even
    p.counter q.counter attempts _ _ _ _ _ _ ⟨p.state, q.state⟩ e3 f3).1
  obtain ⟨j, st, _, cs, smallS, _, _⟩ := wp_result (p.context.fusedSearch_ok p.modulus p.positive p.even p.state p.counter) e3
  obtain ⟨l, tt, _, ds, smallT, _, _⟩ := wp_result (q.context.fusedSearch_ok q.modulus q.positive q.even q.state q.counter) f3
  have eq4 := (fin_relCT pg p.context.value q.context.value p.modulus q.modulus p.context.bound
    (by simpa [VJ, upd, sInv, sCand, sCnt] using p.context.inverse)
    (by simpa [VJ, upd, sInv, sCand, sCnt] using q.context.inverse)
    p.context.odd (by have := p.context.large; omega) p.context.zero q.context.zero p.unit q.unit
    smallS smallT _ _ _ _ _ _ ⟨cs, ds⟩ e4 f4).1
  exact ⟨by rw [eq1, eq2, eq3, eq4], trivial⟩


end VG.Proof.Rsa.X86.Recover
