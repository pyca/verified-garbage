module

public import VerifiedGarbage.Proof.MillerRabin.X86.StageMemory
public import VerifiedGarbage.Proof.Bignum.MemoryFrame

/-! # Lift individual workspace writes into the round's shared frame -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Spec.Rsa.Mont (arrAt)

namespace Stage

theorem workspace_member {base : Addr} {w : Nat} {sp : BitVec 32} {p : Nat × Nat}
    (hp : p ∈ workingRanges w) : ⟨off base p.1, p.2⟩ ∈ stageAreas base w sp :=
  List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩)

theorem workspace_frame {base : Addr} {w d n : Nat} {sp : BitVec 32} {m m' : Mem}
    (F : Frame [⟨off base d, n⟩] m m')
    (mutable : ∃ p ∈ workingRanges w, Region.Sub ⟨off base d, n⟩ ⟨off base p.1, p.2⟩) :
    Frame (stageAreas base w sp) m m' := by
  obtain ⟨p, hp, sub⟩ := mutable
  apply F.sub
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact ⟨_, workspace_member hp, sub⟩

theorem after_workspace {σ s t : State} {base : Addr} {bytes w d n : Nat} {rs : List Reg}
    (h : Stage base bytes w σ s) (K : Keeps rs s t)
    (F : Frame [⟨off base d, n⟩] s.mem t.mem)
    (mutable : ∃ p ∈ workingRanges w, Region.Sub ⟨off base d, n⟩ ⟨off base p.1, p.2⟩)
    (di : .edi ∉ rs := by decide) (esp : .esp ∉ rs := by decide) : Stage base bytes w σ t :=
  h.after K (workspace_frame F mutable) di esp

theorem after_array {σ s t : State} {base : Addr} {bytes w j : Nat} {rs : List Reg}
    (h : Stage base bytes w σ s) (K : Keeps rs s t)
    (F : Frame [⟨off base (arrAt w j), 8 * w⟩] s.mem t.mem)
    (hj : j = 5 ∨ j = 6 ∨ j = 8 ∨ (11 ≤ j ∧ j < 27))
    (di : .edi ∉ rs := by decide) (esp : .esp ∉ rs := by decide) : Stage base bytes w σ t :=
  h.after_workspace K F (mutable_array hj base) di esp

theorem after_header {σ s t : State} {base : Addr} {bytes w d : Nat} {rs : List Reg}
    (h : Stage base bytes w σ s) (K : Keeps rs s t)
    (F : Frame [⟨off base d, 4⟩] s.mem t.mem)
    (hd : d ∈ [184, 188, 212, 232, 236, 240, 244])
    (di : .edi ∉ rs := by decide) (esp : .esp ∉ rs := by decide) : Stage base bytes w σ t :=
  h.after_workspace K F (mutable_header hd base) di esp

end Stage
end VG.Proof.MillerRabin.X86
