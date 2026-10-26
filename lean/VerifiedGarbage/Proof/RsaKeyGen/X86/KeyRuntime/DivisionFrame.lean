module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ArrayDivision
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageCover
import VerifiedGarbage.Proof.Rsa.WordRanges
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Defs.Prop
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ToAdditive

/-! # Runtime division preserves the key's persistent values and header -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key
open VG.Proof.RsaKeyGen.X86.Key (stageRanges StageCovers stage_cover_temp
  stage_cover_header stage_cover_array exponentRanges exponentTemps exponentArrays)

theorem stage_division {m m' : Mem} {B : Addr} {n q r : Nat} {js : List Nat}
    (hq : q ∈ js) (hr : r ∈ js) (O : Outs B (arrayDivisionRanges n q r) m m') :
    Outs B (stageRanges n js) m m' := by
  apply VG.Proof.Rsa.outs_cover O
  intro region mem
  simp only [arrayDivisionRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl
  · exact stage_cover_temp (Nat.le_refl _) (by unfold S; omega)
  · exact stage_cover_header (by decide) (by decide)
  · exact stage_cover_header (by decide) (by decide)
  · exact stage_cover_array hq (by unfold S; omega)
  · exact stage_cover_array hr (by unfold S; omega)

theorem exponent_division_frame {m m' : Mem} {B : Addr} {n : Nat}
    (O : Outs B (arrayDivisionRanges n aU aV) m m') : Outs B (exponentRanges n) m m' :=
  stage_division (by decide) (by decide) O

theorem arrayDivision_preserves_slot {m m' : Mem} {B : Addr} {n q r d : Nat}
    (bound : d + 4 ≤ 128) (O : Outs B (arrayDivisionRanges n q r) m m') :
    slot m' B d = slot m B d := by
  have value : val32 m' B d 1 = val32 m B d 1 := by
    apply O.val32 _ (by omega)
    intro region mem
    simp only [arrayDivisionRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl
    all_goals simp only [arr, hdr] <;> omega
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using value

end VG.Proof.RsaKeyGen.X86.KeyRuntime
