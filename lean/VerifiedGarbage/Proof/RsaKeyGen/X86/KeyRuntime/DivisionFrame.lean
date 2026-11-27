module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ArrayDivision
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageCover
import VerifiedGarbage.Proof.Rsa.WordRanges

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
  · exact stage_cover_temp (Nat.le_refl _) (by unfold S; omega_using [])
  · exact stage_cover_header (by decide) (by decide)
  · exact stage_cover_header (by decide) (by decide)
  · exact stage_cover_array hq (by unfold S; omega_using [])
  · exact stage_cover_array hr (by unfold S; omega_using [])

theorem exponent_division_frame {m m' : Mem} {B : Addr} {n : Nat}
    (O : Outs B (arrayDivisionRanges n aU aV) m m') : Outs B (exponentRanges n) m m' :=
  stage_division (by decide) (by decide) O

theorem arrayDivision_preserves_slot {m m' : Mem} {B : Addr} {n q r d : Nat}
    (bound : d + 4 ≤ 128) (O : Outs B (arrayDivisionRanges n q r) m m') :
    slot m' B d = slot m B d := by
  have value : val32 m' B d 1 = val32 m B d 1 := by
    apply O.val32 _ (by omega_using [bound])
    intro region mem
    simp only [arrayDivisionRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl
    all_goals simp only [arr, hdr] <;> omega_using [bound]
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using value

/-- A persistent array keeps its value through a division, called. -/
theorem Ws.div_num {s : VG.X86.State} {B : Addr} {Z n N q r j : Nat} {m m' : Mem} (W : Ws s B Z n N) (hj : j < N)
    (persistent : 4 ≤ j) (jq : j ≠ q) (jr : j ≠ r) (fit : arr n j + S n ≤ 2 ^ 64)
    (O : OutsS B (s.gpr .esp) (arrayDivisionRanges n q r) m m') : num m' B n j = num m B n j :=
  W.read_num hj O fun O' => arrayDivision_preserves_num persistent jq jr fit O'

/-- A header word keeps its value through a division, called. -/
theorem Ws.div_slot {s : VG.X86.State} {B : Addr} {Z n N q r d : Nat} {m m' : Mem} (W : Ws s B Z n N)
    (bound : d + 4 ≤ 128) (O : OutsS B (s.gpr .esp) (arrayDivisionRanges n q r) m m') :
    slot m' B d = slot m B d := by
  have value : val32 m' B d 1 = val32 m B d 1 := by
    refine W.read_val32 (by simp only [hdr]; omega_using [bound]) O fun O' => ?_
    apply O'.val32 _ (by omega_using [bound])
    intro region mem
    simp only [arrayDivisionRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl
    all_goals simp only [arr, hdr] <;> omega_using [bound]
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using value

end VG.Proof.RsaKeyGen.X86.KeyRuntime
