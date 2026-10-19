module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchEntryCT

/-! # One complete native p-search iteration has a public trace -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 VG.Impl.Dsa.X86_64.Generation

theorem searchBody_ct (G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream)
    (M : Mont) (K : Kernel) (n : Nat) (hn : n = 2 ∨ n = 3) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen)
    (hG : Calls.StreamOK (if qLen = 20 then G1 else G256))
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ x, (H.hash x).length = (if qLen = 20 then G1 else G256).D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : (if qLen = 20 then G1 else G256).D = qLen) :
    RelCT isa (Two (SearchBefore n pLen qLen)) (pAttempt G1 G256 M.mm K.run pLen qLen)
      (fun _ _ => True) := by
  unfold pAttempt
  refine RelCT.seq (two_post (two_map SearchPublic.pointers (fun _ _ h => searchBefore_pointers h)
    pAttemptArgs_ct) (fun _ _ h => searchEntry_ready H h)) ?_
  exact two_map SearchPublic.attempt (fun _ _ h => h)
    (pAttemptTail_ct hG M K n hn H pLen qLen sizes hmatch hsize hhash hseedsize hd)

end VG.Proof.Dsa.X86_64.Generation
