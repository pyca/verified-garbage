module

public import VerifiedGarbage.Proof.Dsa.X86.ShapeModuli
public import VerifiedGarbage.Proof.Dsa.PackedBytes

/-! # The selected byte prefix has the exact digest value required by DSA -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG

theorem shape_digest_width {p q : Nat} (H : shapeValid p q) :
    Spec.Dsa.bitLength q = 8 * (Spec.Dsa.bitLength q / 8) ∧ Spec.Dsa.bitLength q / 8 ≤ 32 := by
  have S := H.1
  unfold Spec.Dsa.supportedSizes at S
  omega

theorem bytesAt_prefix (mem : Mem) (ptr : Addr) (total count : Nat) :
    Spec.Rsa.bytesAt mem ptr (min total count) = (Spec.Rsa.bytesAt mem ptr total).take count := by
  apply List.ext_getElem
  · simp only [Spec.Rsa.bytesAt, List.length_take, List.length_map, List.length_range]
    omega
  · intro i hi hj
    simp only [List.getElem_take, Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]

end VG.Proof.Dsa.X86
