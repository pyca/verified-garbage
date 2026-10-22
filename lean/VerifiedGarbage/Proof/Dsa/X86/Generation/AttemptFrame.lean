module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ConstructionFrame
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleRoundFrame
import VerifiedGarbage.Proof.Framework.Offset

/-! Candidate construction and primality testing leave the search metadata outside their writes. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86

def AttemptFrame (base : Addr) (sp : BitVec 32) (len : Nat) (s t : State) : Prop :=
  Frame [⟨base, montgomeryBytes⟩, ⟨off base Layout.hash, Layout.q - Layout.hash⟩,
    ⟨off base Layout.p, 768⟩, ⟨off base Layout.arithmetic, Layout.arithmeticBytes⟩,
    ⟨off base Layout.witness, len⟩, ⟨off base Layout.control, 512⟩, below sp 1184] s.mem t.mem

theorem attempt_construction_frame {s t : State} {base : Addr} {len : Nat}
    (F : ConstructionFrame base (s.gpr .esp) s t) (low : 1184 ≤ (s.gpr .esp).toNat) :
    AttemptFrame base (s.gpr .esp) len s t := by
  apply F.sub
  intro region hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨base, montgomeryBytes⟩, by simp, fun _ h => h⟩
  · exact ⟨⟨off base Layout.hash, Layout.q - Layout.hash⟩, by simp, fun _ h => h⟩
  · exact ⟨⟨off base Layout.p, 768⟩, by simp, fun _ h => h⟩
  · exact ⟨⟨off base Layout.arithmetic, Layout.arithmeticBytes⟩, by simp, fun _ h => h⟩
  · exact ⟨below (s.gpr .esp) 1184, by simp, below_sub (by decide) low⟩

theorem attempt_sample_frame {s t : State} {base : Addr} {len : Nat}
    (F : SampleRoundFrame base (s.gpr .esp) len s t) : AttemptFrame base (s.gpr .esp) len s t := by
  exact F.mono (by simp [Layout.arithmeticBytes])

theorem attempt_metadata {s t : State} {base : Addr} {bytes len d : Nat}
    (F : AttemptFrame base (s.gpr .esp) len s t) (capacity : 40960 ≤ bytes)
    (room : RoundRoom (s.gpr .esp) base bytes) (length : len ≤ 384)
    (lower : Layout.packed ≤ d) (upper : d + 4 ≤ Layout.control) :
    t.mem.readW (off base d) 32 = s.mem.readW (off base d) 32 := by
  apply F.readW (r := ⟨off base d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Offset.disjoint_base base (by unfold Layout.packed montgomeryBytes at *; omega)
      (by unfold Layout.control at upper; omega)
  · exact Offset.disjoint base (.inr (by unfold Layout.hash Layout.q Layout.packed at *; omega))
      (by unfold Layout.control at upper; omega) (by decide)
  · exact Offset.disjoint base (.inr (by unfold Layout.p Layout.packed at *; omega))
      (by unfold Layout.control at upper; omega) (by decide)
  · exact Offset.disjoint base (.inl (by unfold Layout.arithmetic Layout.control at *; omega))
      (by unfold Layout.control at upper; omega) (by decide)
  · exact Offset.disjoint base (.inr (by unfold Layout.witness Layout.packed at *; omega))
      (by unfold Layout.control at upper; omega) (by unfold Layout.witness; omega)
  · exact Offset.disjoint base (.inl upper) (by unfold Layout.control at upper; omega) (by decide)
  · exact (room.apart.sub_right (Offset.sub_base base (by unfold Layout.control at upper; omega))).symm

end VG.Proof.Dsa.X86.Generation
