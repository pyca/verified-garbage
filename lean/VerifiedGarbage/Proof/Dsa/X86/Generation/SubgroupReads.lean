module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.SubgroupFrame
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ControlKeeps
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleRoundFrame
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Offset

/-! Preserve tape metadata during seed hashing and saved candidates during primality testing. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86

theorem subgroup_enclose {s t : State} {base : Addr} {bytes : Nat}
    (F : SubgroupCandidateFrame base (s.gpr .esp) s t) (capacity : 40960 ≤ bytes)
    (room : RoundRoom (s.gpr .esp) base bytes) :
    Frame [⟨base, bytes⟩, below (s.gpr .esp) 1184] s.mem t.mem := by
  apply F.sub
  intro region hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨base, bytes⟩, by simp, Offset.sub_base base (by unfold Layout.hash; omega)⟩
  · exact ⟨⟨base, bytes⟩, by simp, Offset.sub_base base (by unfold Layout.q; omega)⟩
  · exact ⟨below (s.gpr .esp) 1184, by simp, below_sub (by decide) room.low⟩

theorem subgroup_control {s t : State} {base : Addr} {bytes : Nat}
    (F : SubgroupCandidateFrame base (s.gpr .esp) s t) (capacity : 40960 ≤ bytes)
    (room : RoundRoom (s.gpr .esp) base bytes) : ControlKeeps base s.mem t.mem := by
  intro d lo hi
  apply F.readW (r := ⟨off base d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint base (.inr (by unfold Layout.hash Layout.control at *; omega))
      (by unfold Layout.control at lo hi; omega) (by decide)
  · exact Offset.disjoint base (.inr (by unfold Layout.q Layout.control at *; omega))
      (by unfold Layout.control at lo hi; omega) (by decide)
  · exact ((room.apart.sub_left (below_sub (by decide) room.low)).sub_right
      (Offset.sub_base base (by unfold Layout.control at lo hi; omega))).symm

theorem sample_saved_bytes {s t : State} {base : Addr} {bytes len d size : Nat}
    (F : SampleRoundFrame base (s.gpr .esp) len s t) (capacity : 40960 ≤ bytes)
    (room : RoundRoom (s.gpr .esp) base bytes)
    (lower : montgomeryBytes ≤ d) (upper : d + size ≤ Layout.witness) (length : len ≤ 384) :
    Spec.Rsa.bytesAt t.mem (off base d) size = Spec.Rsa.bytesAt s.mem (off base d) size := by
  apply VG.Proof.Dsa.Generation.frame_bytesAt F ?_ (by unfold Layout.witness at upper; omega)
  intro region hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Offset.disjoint_base base lower (by unfold Layout.witness at upper; omega)
  · exact Offset.disjoint base (.inl (by unfold Layout.arithmetic Layout.witness at *; omega))
      (by unfold Layout.witness at upper; omega) (by decide)
  · exact Offset.disjoint base (.inl upper) (by unfold Layout.witness at upper; omega)
      (by unfold Layout.witness; omega)
  · exact Offset.disjoint base (.inl (by unfold Layout.control Layout.witness at *; omega))
      (by unfold Layout.witness at upper; omega) (by decide)
  · exact (room.apart.sub_right (Offset.sub_base base (by unfold Layout.witness at upper; omega))).symm

end VG.Proof.Dsa.X86.Generation
