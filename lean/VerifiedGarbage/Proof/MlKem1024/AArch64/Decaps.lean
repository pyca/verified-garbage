module

public import VerifiedGarbage.Proof.MlKem.Scrubbed
public import VerifiedGarbage.Proof.MlKem.AArch64.Decaps
public import VerifiedGarbage.Spec.MlKem.Contract1024
import VerifiedGarbage.Proof.MlKem1024.AArch64.Encaps
import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_decaps`

ML-KEM-768's proof (`Proof/MlKem/AArch64/Kem*.lean`, `Decaps*.lean`), which is
stated for any well-formed parameter set, for ML-KEM-1024's (`lay1024`); the
taint analyses of its code are decided on its literals.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.AArch64.Decaps

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem VG.Proof.MlKem.AArch64.Decaps
open VG.Impl.MlKem.AArch64 (KemLay)

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x10000 | _ => 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, 3168⟩, ⟨0x2000, 1568⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x10000, 49152⟩]

end VG.Proof.MlKem1024.AArch64.Decaps
