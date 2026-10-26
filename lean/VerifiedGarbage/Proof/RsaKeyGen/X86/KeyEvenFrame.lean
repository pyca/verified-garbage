module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExponentFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArrayDivision
import VerifiedGarbage.Proof.Rsa.WordRanges
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.Prop
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.ToAdditive

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

theorem arrayDivision_preserves_header {m m' : Mem} {B : Addr} {n q r d count : Nat}
    (bound : d + 4 * count ≤ hdr)
    (O : Outs B (arrayDivisionRanges n q r) m m') : val32 m' B d count = val32 m B d count := by
  apply O.val32 _ (by unfold hdr at bound; omega)
  intro region mem
  simp only [arrayDivisionRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · exact Or.inl bound
  · exact Or.inl (Nat.le_trans bound (show hdr ≤ arr n q from Nat.le_add_right ..))
  · exact Or.inl (Nat.le_trans bound (show hdr ≤ arr n r from Nat.le_add_right ..))

theorem arrayDivision_preserves_slot {m m' : Mem} {B : Addr} {n q r d : Nat}
    (bound : d + 4 ≤ hdr)
    (O : Outs B (arrayDivisionRanges n q r) m m') : slot m' B d = slot m B d := by
  have H := arrayDivision_preserves_header (count := 1) bound O
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using H

end VG.Proof.RsaKeyGen.X86.Key
