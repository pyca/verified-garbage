module
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PAttempt
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PPrimalityCTState

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PPrimalityReadyCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PPrimalityTestCT

/-! # Complete candidate construction, width rejection and primality testing -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 VG.Impl.Dsa.AArch64.Generation

theorem pConstructTest_ct {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    (T : PrimeTest) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : G.D = qLen) :
    RelCT isa (Two (PPrimalityBefore H pLen qLen))
      (.seq (pConstruct G pLen qLen) (pTest T.run pLen)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (two_map PPrimalityPublic.construct (fun _ _ h => pPrimality_construct h)
    (pConstruct_ct hG H pLen qLen sizes hmatch hsize hhash hseedsize hd)) ?_)
    (pPrimalityTest_ct T pLen ?_)
  · intro p s h
    exact WP.mono (pPrimality_ready hG hmatch hsize hhash hseedsize hd h)
      fun _ ht => ⟨ht, h.2.2.2.2.1⟩
  · rcases sizes with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp

end VG.Proof.Dsa.AArch64.Generation
