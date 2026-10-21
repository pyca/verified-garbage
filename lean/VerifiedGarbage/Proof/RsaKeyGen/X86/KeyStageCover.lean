module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageFrame

/-! # Small ranges are covered by the native stage header and array bank -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def StageCovers (n : Nat) (js : List Nat) (d count : Nat) : Prop :=
  ∃ r ∈ stageRanges n js, r.1 ≤ d ∧ d + count ≤ r.1 + r.2

theorem stage_cover_header {n d count : Nat} {js : List Nat}
    (lower : kOk ≤ d) (upper : d + count ≤ kOk + 44) : StageCovers n js d count :=
  ⟨(kOk, 44), List.mem_append_left _ (List.mem_cons_self ..), lower, upper⟩

theorem stage_cover_temp {n d count : Nat} {js : List Nat}
    (lower : hdr ≤ d) (upper : d + count ≤ hdr + 15 * S n) : StageCovers n js d count :=
  ⟨(hdr, 15 * S n), List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), lower, upper⟩

theorem stage_cover_bank {n k : Nat} {js : List Nat} (width : k ≤ n) :
    StageCovers n js hdr (4 * (15 * (k + 2))) :=
  stage_cover_temp (Nat.le_refl _) (by unfold S; omega)

theorem stage_cover_array {n j count : Nat} {js : List Nat} (member : j ∈ js) (bound : count ≤ S n) :
    StageCovers n js (arr n j) count :=
  ⟨(arr n j, S n), List.mem_append_right _
    (List.mem_append_left _ (List.mem_map.mpr ⟨j, member, rfl⟩)), Nat.le_refl _, Nat.add_le_add_left bound _⟩

end VG.Proof.RsaKeyGen.X86.Key
