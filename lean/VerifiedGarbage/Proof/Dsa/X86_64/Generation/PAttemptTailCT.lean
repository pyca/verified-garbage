module

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructTestCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructTest
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptBlocksCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PPrimalityCTState

/-! # Return the verified p-test result to the bounded search controller -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 VG.Impl.Dsa.X86_64.Generation

def PPrimalityPublic.returnFrame (p : PPrimalityPublic) : AttemptReturnPublic :=
  ⟨p.plan.construct.hash.F, p.plan.construct.hash.S, p.plan.construct.hash.W 5⟩

theorem pAttemptTail_ready {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    (M : Mont) (K : Kernel) {n pLen qLen : Nat} {H : Spec.Mgf1.Hash}
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : G.D = qLen) {p : PPrimalityPublic} {s : State}
    (h : PPrimalityBefore n H pLen qLen p s) :
    WP isa (.seq (pConstruct G pLen qLen) (pTest M.mm K.run pLen)) s (AttemptReturnBefore p.returnFrame) := by
  obtain ⟨⟨W, hw, hs, _, hu⟩, _, hub, tape, writable, hp, hq⟩ := h
  let q := p.plan.withWords W hw
  have step := pConstructTest_ok hG hmatch hsize M K (p := q) (hd.trans hq.symm) hs
    (by simpa only [q, PPrimalityPlan.withWords, PConstructPlan.withWords, HashPlan.withWords, hq] using hhash)
    (by simpa only [q, PPrimalityPlan.withWords, PConstructPlan.withWords, HashPlan.withWords, hq] using hseedsize)
    hu hub tape (by
      simpa only [q, PPrimalityPlan.withWords, PConstructPlan.withWords, HashPlan.withWords,
        hw.1 5 (by decide)] using writable)
  change WP isa (.seq (pConstruct G p.plan.construct.len p.plan.construct.hash.len)
    (pTest M.mm K.run p.plan.construct.len)) s _ at step
  rw [hp, hq] at step
  refine WP.mono step fun t ⟨used, status, V, _, L, R, _⟩ => ?_
  refine ⟨L, V, _, R, ?_⟩
  simpa only [q, PPrimalityPlan.withWords, PConstructPlan.withWords, HashPlan.withWords,
    VG.Proof.RsaOaep.X86_64.upd, PPrimalityPublic.returnFrame,
    show ¬ (5 : Nat) = 19 by decide, show ¬ (5 : Nat) = 16 by decide, ite_false] using hw.1 5 (by decide)

theorem pAttemptTail_ct {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    (M : Mont) (K : Kernel) (n : Nat) (hn : n = 2 ∨ n = 3) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : G.D = qLen) :
    RelCT isa (Two (PPrimalityBefore n H pLen qLen))
      (.seq (.seq (pConstruct G pLen qLen) (pTest M.mm K.run pLen)) (.block searchReturn))
      (fun _ _ => True) :=
  RelCT.seq (two_post (pConstructTest_ct hG M K n hn H pLen qLen sizes hmatch hsize hhash hseedsize hd)
    (fun _ _ h => pAttemptTail_ready hG M K hmatch hsize hhash hseedsize hd h))
    (two_map PPrimalityPublic.returnFrame (fun _ _ h => h) searchReturn_ct)

end VG.Proof.Dsa.X86_64.Generation
