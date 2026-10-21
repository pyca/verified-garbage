module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InputTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExportTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.StartPair

/-! # Shared derivation and the existing output adapters publish only the specified retry bit -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (Environment writeOutputs_trace)

theorem front_trace (E : Environment) (valid : E.Valid) (sp : BitVec 32) (e p q p' q' : Nat)
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p' q' = .inr ())) :
    RelCT isa (RuntimeStart E sp e p q p' q') front
      (VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint true)) := by
  unfold front
  exact RelCT.seq (loadInputs_front_trace E valid sp e p q p' q')
    (RelCT.seq (deriveOutput_trace E sp e p q p' q' release)
      (selectIO_trace valid (fun _ _ P => P.1) (output_keepIO E) (writeOutputs_trace E)))

end VG.Proof.RsaKeyGen.X86.KeyRuntime
