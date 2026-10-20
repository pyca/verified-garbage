module
public import VerifiedGarbage.Impl.Bignum.Arm.PdFn
public import VerifiedGarbage.Proof.Bignum.Arm.PdBodyInput
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.Arm.PdPrepareCT
import VerifiedGarbage.Proof.Bignum.Arm.PdImportCT
import VerifiedGarbage.Proof.Bignum.Arm.PdCheckedCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT

/-! # Importing and applying a packed public key preserves input secrecy -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem pdImported_ct {base dst pp ep xp : BitVec 32} {len k eLen N R : Nat} {eb xb1 xb2 : List Byte} :
    RelCT isa (fun s t => PdBodyInput base dst pp ep xp len k eLen N R eb xb1 s ∧
      PdBodyInput base dst pp ep xp len k eLen N R eb xb2 t ∧ s.sp = t.sp)
      PdFn.imported (fun _ _ => True) := by
  exact crt_seq_ct pdPrepare_ct (fun s h => pdPrepare_ready s h) (fun s h => pdPrepare_ready s h)
    (crt_seq_ct (pdImport_ct.mono (fun _ _ h => ⟨h.1.input, h.2.1.input⟩) (fun _ _ _ => trivial))
      (fun s h => pdImport_ready s h) (fun s h => pdImport_ready s h) pdChecked_ct)
end VG.Proof.Bignum.Arm
