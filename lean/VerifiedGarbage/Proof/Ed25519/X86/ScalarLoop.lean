module

public import VerifiedGarbage.Proof.Ed25519.X86.ScalarBody
import VerifiedGarbage.Proof.Ed25519.Scalar

@[expose] public section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86
open VG.Spec.Ed25519 (L decodeLE)

def scalarInput (m : Mem) (x : BitVec 32) : List Byte :=
  (List.range 64).map fun i => m (addr x (128 + i))

theorem scalarInput_length (m : Mem) (x : BitVec 32) : (scalarInput m x).length = 64 := by
  simp only [scalarInput, List.length_map, List.length_range]

end VG.Proof.Ed25519.X86
