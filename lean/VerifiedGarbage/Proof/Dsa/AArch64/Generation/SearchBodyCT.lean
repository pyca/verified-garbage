module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchCTState

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchEntryCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PAttemptTailCT

/-! # One complete native p-search iteration has a public trace -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 VG.Impl.Dsa.AArch64.Generation

theorem searchBody_ct (G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash)
    (M : Mont) (T : PrimeTest) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen)
    (hG : Calls.StreamOK (if qLen = 20 then G1 else G256).stream)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ x, (H.hash x).length = (if qLen = 20 then G1 else G256).D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : (if qLen = 20 then G1 else G256).D = qLen) :
    RelCT isa (Two (SearchBefore pLen qLen)) (pAttempt G1 G256 T.run pLen qLen)
      (fun _ _ => True) := by
  unfold pAttempt
  refine RelCT.seq (two_post (two_map SearchPublic.pointers (fun _ _ h => searchBefore_pointers h)
    pAttemptArgs_ct) (fun _ _ h => searchEntry_ready H h)) ?_
  exact two_map SearchPublic.attempt (fun _ _ h => h)
    (pAttemptTail_ct hG M T H pLen qLen sizes hmatch hsize hhash hseedsize hd)

end VG.Proof.Dsa.AArch64.Generation
