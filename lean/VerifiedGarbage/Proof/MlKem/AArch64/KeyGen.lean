module

public import VerifiedGarbage.Proof.MlKem.Scrubbed
public import VerifiedGarbage.Proof.MlKem.AArch64.KgEnd
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.AArch64.KgEnd
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on AArch64: `keygen`, ML-KEM-768's parameter set

ML-KEM-768's layout is well formed (`wf768`), and a state satisfying the
precondition of `keygen` (`sat`), for the functions of `Kem16/` and `KgH/`.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

/-! ## Constant time -/

variable (hP : P.Wf)
include hP

omit hP

/-! ## ML-KEM-768 -/

theorem wf768 : lay768.Wf := ⟨by decide⟩

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x10000 | _ => 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 1184⟩, ⟨0x3000, 2400⟩, ⟨0x10000, 32768⟩]

end VG.Proof.MlKem.AArch64.KeyGen
