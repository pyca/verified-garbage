module

public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.MillerRabin.X86.Context

/-! # Every candidate API size fits the shared prepared i686 arithmetic -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateGeometry
open VG VG.X86 VG.Proof.MillerRabin.X86

def geometry (workspace : Addr) (length capacity : Nat) : Geometry := ⟨workspace, 8 * capacity, length / 8⟩

theorem length_eq {length : Nat} (valid : Spec.RsaKeyGen.primeLenValid length) :
    8 * (length / 8) = length := by
  obtain ⟨_, _, multiple⟩ := valid
  omega

theorem width_bounds {length : Nat} (valid : Spec.RsaKeyGen.primeLenValid length) :
    4 ≤ length / 8 ∧ length / 8 ≤ 64 := by
  obtain ⟨lo, hi, _⟩ := valid
  omega

theorem geometry_valid {workspace : Addr} {length capacity : Nat}
    (valid : Spec.RsaKeyGen.primeLenValid length)
    (space : Spec.Rsa.scratchWords length ≤ capacity) : (geometry workspace length capacity).Valid := by
  have lo := (width_bounds valid).1
  have hi := (width_bounds valid).2
  have len := length_eq valid
  refine ⟨lo, by change length / 8 ≤ 128; omega, ?_⟩
  change Proof.Rsa.Mont.arrAt (length / 8) 28 ≤ 8 * capacity
  unfold Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes
  unfold Spec.Rsa.scratchWords at space
  omega

theorem native_length_bound {length : Nat} (valid : Spec.RsaKeyGen.primeLenValid length) : length < 2 ^ 32 := by
  obtain ⟨_, hi, _⟩ := valid
  omega

end VG.Proof.RsaKeyGen.X86.CandidateGeometry
