module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.CorePair
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.RetryTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.KeyPartPublic
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ScalarPublic
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DSelectTiming
import VerifiedGarbage.Proof.Framework.X86.Taint

/-! # Complete native numeric key derivation is constant time modulo the released retry status -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Rsa.X86.Keys VG.Proof.Mont.X86.Dynamic
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aD aE kEv kOk)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (KeyReady)

theorem deriveLoaded_trace (B : Addr) (Z n k e p q p' q' : Nat)
    (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0)
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * n) e p' q' = .inr ())) :
    RelCT isa (fun s t => CoreStart B Z n k e p q s ∧ CoreStart B Z n k e p' q' t ∧
      VG.X86.Taint.Agree runtimeTaint s t)
      deriveLoaded (VG.X86.Taint.Agree runtimeTaint) := by
  unfold deriveLoaded
  apply RelCT.seq (prepareReady_trace B Z n k e p q p' q' width positive even)
  apply RelCT.seq (smallMask_trace B Z n e p q p' q' release)
  apply RelCT.ite (fun _ _ P => P.2)
  · exact (public_trace retry_public).mono (fun _ _ P => P.1.1.agree) (fun _ _ P => P)
  · exact (public_trace keyPart_public).mono (fun _ _ P => P.1.1.agree) (fun _ _ P => P)

end VG.Proof.RsaKeyGen.X86.KeyRuntime
