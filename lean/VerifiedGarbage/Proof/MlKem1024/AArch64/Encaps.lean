module

public import VerifiedGarbage.Proof.MlKem.Scrubbed
public import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
import VerifiedGarbage.Proof.MlKem1024.AArch64.Args
public import VerifiedGarbage.Spec.MlKem.Contract1024
meta import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.Args
meta import VerifiedGarbage.Spec.MlKem.Contract1024

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_encaps`

ML-KEM-768's proof (`Proof/MlKem/AArch64/Kem*.lean`, `Encaps.lean`), which is
stated for any well-formed parameter set, for ML-KEM-1024's (`lay1024`),
whose compression functions at the widths 11 and 5 are ML-KEM-1024's own
(`calls1024`); the taint analyses of its code are decided on its literals.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.AArch64.Encaps

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem VG.Proof.MlKem.AArch64.Encaps
open VG.Proof.MlKem1024.AArch64 (compressEncode1024_call decodeDecompress1024_call)
open VG.Impl.MlKem.AArch64 (KemLay)

theorem calls1024 : Calls lay1024 :=
  ⟨fun h0 h1 h2 h3 hd => compressEncode1024_call h0 h1 h2 h3 (by rcases hd with rfl | rfl <;> decide),
    fun h0 h1 h2 h3 hd => decodeDecompress1024_call h0 h1 h2 h3 (by rcases hd with rfl | rfl <;> decide)⟩

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | .x4 => 0x10000 | _ => 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, 1568⟩, ⟨0x2000, 32⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 1568⟩, ⟨0x10000, 49152⟩]

end VG.Proof.MlKem1024.AArch64.Encaps
