module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExponentFrame
import VerifiedGarbage.Proof.Rsa.WordRanges
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs

/-! # Frames for the modulus-width inverse fallback -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem exponent_keep_frame {m m' : Mem} {B : Addr} {n : Nat} {js ds : List Nat}
    (arrays : ∀ j ∈ js, j < 15 ∨ j ∈ exponentArrays)
    (scalars : ∀ d ∈ ds, kOk ≤ d ∧ d + 4 ≤ kOk + 68) (O : Keep B n js ds m m') :
    Outs B (exponentRanges n) m m' := by
  apply VG.Proof.Rsa.outs_cover O
  intro r hr
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, hj, rfl⟩ | ⟨d, hd, rfl⟩
  · rcases arrays j hj with temp | result
    · refine ⟨(hdr, 15 * S n), by simp [exponentRanges, exponentTemps], ?_, ?_⟩
      · exact Nat.le_add_right ..
      · have endN := arr_end (w := n) temp
        change arr n j + S n ≤ arr n 15
        exact endN
    · exact ⟨(arr n j, S n), List.mem_append_right _
        (List.mem_append_left _ (List.mem_map.mpr ⟨j, result, rfl⟩)), Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨(kOk, 68), by simp [exponentRanges, exponentTemps], (scalars d hd).1, (scalars d hd).2⟩

end VG.Proof.RsaKeyGen.X86.Key
