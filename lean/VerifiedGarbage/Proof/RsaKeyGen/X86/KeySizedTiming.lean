module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyImportedPair
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputReady
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExportTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Complete native key assembly is constant time modulo its public exponent and retry result -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Rsa.X86.Keys VG.Impl.RsaKeyGen.X86.Key

theorem sized_trace (E : Environment) (e p q p' q' : Nat)
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p' q' = .inr ())) :
    RelCT isa (SizedStart E e p q p' q') (sized E.n) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold sized seqs
  apply RelCT.assoc
  apply RelCT.assoc
  apply RelCT.assoc
  exact RelCT.seq (inputReady_trace E e p q p' q')
    (RelCT.seq (deriveOutput_trace E e p q p' q' release) (writeOutputs_trace E))

end VG.Proof.RsaKeyGen.X86.Key
