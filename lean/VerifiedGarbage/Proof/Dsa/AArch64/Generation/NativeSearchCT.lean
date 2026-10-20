module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchInitCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PSearchLoopCT

/-! # The complete bounded native p search has a public trace -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 VG.Impl.Dsa.AArch64.Generation

theorem primeSearch_ct (G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash)
    (M : Mont) (K : Kernel) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen)
    (hG : Calls.StreamOK (if qLen = 20 then G1 else G256).stream)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ x, (H.hash x).length = (if qLen = 20 then G1 else G256).D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : (if qLen = 20 then G1 else G256).D = qLen) :
    RelCT isa (Two (SearchStart pLen qLen)) (primeSearch G1 G256 M.mm K.run pLen qLen)
      (fun _ _ => True) := by
  unfold primeSearch pSearch
  refine RelCT.seq (two_post ((two_map SearchPublic.returnFrame (fun _ _ h => searchStart_frame h)
    controlBase_ct).mono (fun _ _ h => h) (fun _ _ _ => True.intro))
    (fun _ _ h => searchBase_ready h)) (RelCT.seq (searchInit_ct pLen qLen) ?_)
  exact pSearchLoop_ct G1 G256 M K H pLen qLen sizes hG hmatch hsize hhash hseedsize hd

end VG.Proof.Dsa.AArch64.Generation
