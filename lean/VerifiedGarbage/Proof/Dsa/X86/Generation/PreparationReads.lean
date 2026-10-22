module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.PreparePrime
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateTrial
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleRoundFrame
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ControlKeeps
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.Offset

/-! Candidate filtering and preparation retain saved parameters and tape-control words. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86

theorem trial_candidate_keep {s t : State} {base : Addr} {bytes n : Nat}
    (F : Frame [⟨off base trialTableOffset, 2048⟩, below (s.gpr .esp) 40] s.mem t.mem)
    (capacity : 40960 ≤ bytes) (room : CallRoom (s.gpr .esp) base bytes) (upper : n ≤ 48) :
    wordsVal t.mem base (slot n 0) n = wordsVal s.mem base (slot n 0) n := by
  rw [← read_eq_wordsVal, ← read_eq_wordsVal]
  apply congrArg BitVec.toNat
  apply F.read (r := ⟨off base (slot n 0), 8 * n⟩) (Region.contains_self _ _) ?_ (by omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint base (.inl (by simp only [slot, stride, trialTableOffset]; omega))
      (by simp only [slot, stride]; omega) (by decide)
  · exact (room.apart.sub_right (Offset.sub_base base (by simp only [slot, stride]; omega))).symm

theorem trial_preparation_frame {s t : State} {base : Addr}
    (F : Frame [⟨off base trialTableOffset, 2048⟩, below (s.gpr .esp) 40] s.mem t.mem) :
    PreparationFrame base (s.gpr .esp) s t := by
  apply F.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨⟨base, montgomeryBytes⟩, by simp, Offset.sub_base base (by decide)⟩
  · exact ⟨below (s.gpr .esp) 40, by simp, fun _ h => h⟩

theorem preparation_round_frame {s t : State} {base : Addr} {len : Nat}
    (F : PreparationFrame base (s.gpr .esp) s t) (low : 1184 ≤ (s.gpr .esp).toNat) :
    SampleRoundFrame base (s.gpr .esp) len s t := by
  apply F.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨base, montgomeryBytes⟩, by simp, fun _ h => h⟩
  · exact ⟨⟨off base Layout.arithmetic, 12288⟩, by simp,
      Region.sub_prefix (by decide : Layout.arithmeticBytes ≤ 12288)⟩
  · exact ⟨below (s.gpr .esp) 1184, by simp, below_sub (by decide) low⟩

theorem preparation_middle_read {s t : State} {base : Addr} {bytes d size : Nat}
    (F : PreparationFrame base (s.gpr .esp) s t) (capacity : 40960 ≤ bytes)
    (room : CallRoom (s.gpr .esp) base bytes) (lower : montgomeryBytes ≤ d) (fit : d + size ≤ Layout.arithmetic) :
    t.mem.read (off base d) size = s.mem.read (off base d) size := by
  apply F.read (r := ⟨off base d, size⟩) (Region.contains_self _ _) ?_ (by unfold Layout.arithmetic at fit; omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint_base base lower (by unfold Layout.arithmetic at fit; omega)
  · exact Offset.disjoint base (.inl fit) (by unfold Layout.arithmetic at fit; omega) (by decide)
  · exact (room.apart.sub_right (Offset.sub_base base (by unfold Layout.arithmetic at fit; omega))).symm

theorem preparation_control {s t : State} {base : Addr} {bytes : Nat}
    (F : PreparationFrame base (s.gpr .esp) s t) (capacity : 40960 ≤ bytes)
    (room : CallRoom (s.gpr .esp) base bytes) : ControlKeeps base s.mem t.mem := by
  intro d lo hi
  unfold Mem.readW
  rw [preparation_middle_read (d := d) (size := 4) F capacity room
    (Nat.le_trans (by decide : montgomeryBytes ≤ Layout.control) lo) (Nat.le_trans hi (by decide))]

end VG.Proof.Dsa.X86.Generation
