module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchInitCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PSearchLoopCT

/-! # The complete bounded native p search has a public trace -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 VG.Impl.Dsa.X86_64.Generation

theorem primeSearch_ct (G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream)
    (T : PrimeTest) (n : Nat) (hn : n = 2 ∨ n = 3) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen)
    (hG : Calls.StreamOK (if qLen = 20 then G1 else G256))
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ x, (H.hash x).length = (if qLen = 20 then G1 else G256).D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : (if qLen = 20 then G1 else G256).D = qLen) :
    RelCT isa (Two (SearchStart n pLen qLen)) (primeSearch G1 G256 T.run pLen qLen)
      (fun _ _ => True) := by
  unfold primeSearch pSearch
  refine RelCT.seq (two_post ((two_map SearchPublic.returnFrame (fun _ _ h => searchStart_frame h)
    controlBase_ct).mono (fun _ _ h => h) (fun _ _ _ => True.intro))
    (fun _ _ h => searchBase_ready h)) (RelCT.seq (searchInit_ct n pLen qLen) ?_)
  exact pSearchLoop_ct G1 G256 T n hn H pLen qLen sizes hG hmatch hsize hhash hseedsize hd

end VG.Proof.Dsa.X86_64.Generation
