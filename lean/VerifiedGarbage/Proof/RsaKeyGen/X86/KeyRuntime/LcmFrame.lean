module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Lcm
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLcmFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageCover
import VerifiedGarbage.Proof.Rsa.WordRanges

/-! # The complete native LCM leaves the factors and public exponent intact -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key
open VG.Proof.RsaKeyGen.X86.Key (lcmArrays stageRanges gcdPartRanges gcdRanges gcdPartArrays
  inverseRanges StageCovers stage_cover_array stage_cover_header stage_cover_temp stage_cover_bank)

theorem lcm_stage_frame {m m' : Mem} {B : Addr} {n k : Nat} (width : k ≤ n)
    (O : Outs B (lcmRanges n k) m m') : Outs B (stageRanges n lcmArrays) m m' := by
  apply VG.Proof.Rsa.outs_cover O
  intro r hr
  change r ∈ ranges n halveArrays [kFlag] ++ (gcdPartRanges n k ++ lcmDivisionRanges n) at hr
  rcases List.mem_append.mp hr with half | other
  · simp only [ranges, List.mem_append, List.mem_map] at half
    rcases half with ⟨j, hj, rfl⟩ | ⟨d, hd, rfl⟩
    · have included : ∀ j ∈ halveArrays, j ∈ lcmArrays := by decide
      exact stage_cover_array (included j hj) (Nat.le_refl _)
    · obtain rfl := List.mem_singleton.mp hd
      exact stage_cover_header (by decide) (by decide)
  · rcases List.mem_append.mp other with gcd | division
    · change r ∈ gcdRanges n k ++ ranges n gcdPartArrays [kFlag] at gcd
      rcases List.mem_append.mp gcd with inv | other
      · change r ∈ inverseRanges k invSlots ++ [(arr n aDen, S n)] at inv
        rcases List.mem_append.mp inv with bank | den
        · simp only [inverseRanges, invSlots, List.map_cons, List.map_nil,
            List.mem_cons, List.not_mem_nil, or_false] at bank
          rcases bank with rfl | rfl | rfl | rfl
          · exact stage_cover_bank width
          all_goals exact stage_cover_header (by decide) (by decide)
        · obtain rfl := List.mem_singleton.mp den
          exact stage_cover_array (by decide) (Nat.le_refl _)
      · simp only [ranges, List.mem_append, List.mem_map] at other
        rcases other with ⟨j, hj, rfl⟩ | ⟨d, hd, rfl⟩
        · have included : ∀ j ∈ gcdPartArrays, j < 15 ∨ j ∈ lcmArrays := by decide
          rcases included j hj with temp | array
          · exact stage_cover_temp (Nat.le_add_right ..) (arr_end (w := n) temp)
          · exact stage_cover_array array (Nat.le_refl _)
        · obtain rfl := List.mem_singleton.mp hd
          exact stage_cover_header (by decide) (by decide)
    · simp only [lcmDivisionRanges, arrayDivisionRanges, List.mem_cons, List.not_mem_nil, or_false] at division
      rcases division with rfl | rfl | rfl | rfl | rfl
      · exact stage_cover_temp (Nat.le_refl _) (by unfold S; omega)
      · exact stage_cover_header (by decide) (by decide)
      · exact stage_cover_header (by decide) (by decide)
      · exact stage_cover_array (by decide) (by unfold S; omega)
      · have last := arr_end (w := n) (show aT1 < 15 by decide)
        change arr n aT1 + S n ≤ hdr + 15 * S n at last
        exact stage_cover_temp (Nat.le_add_right ..) (by unfold S at last ⊢; omega)

end VG.Proof.RsaKeyGen.X86.KeyRuntime
