module

public import VerifiedGarbage.Proof.MillerRabin.X86.Snapshot
public import VerifiedGarbage.Proof.MillerRabin.X86.RestoreStage
import VerifiedGarbage.Proof.Framework.Offset

/-! # Bound all writes by the workspace and the function's reserved stack -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt wOf)

def bodyAreas (s : State) : List Region :=
  [⟨wsOf s, bytesOf s⟩, entryFrame s,
    below ((allocFrame VG.Impl.MillerRabin.X86.frameBytes s).gpr .esp) 40]

theorem SnapshotReady.stage_frame {s σ t : State} {w : Nat}
    (ready : SnapshotReady s σ) (stage : Stage (wsOf s) (bytesOf s) w σ t)
    (fit : arrAt w 28 ≤ bytesOf s) : Frame (bodyAreas s) s.mem t.mem := by
  have priorFrame : Frame (bodyAreas s) s.mem σ.mem := ready.frame.mono (by simp [bodyAreas])
  apply priorFrame.trans
  apply stage.changed.sub
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    exact ⟨⟨wsOf s, bytesOf s⟩, by simp [bodyAreas], Offset.sub_base _
      (Nat.le_trans (working_bounds w p hp) fit)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨entryFrame s, by simp [bodyAreas], ?_⟩
      rw [ready.sp]
      exact Offset.sub_base _ (by decide)
    · exact ⟨_, by rw [ready.sp]; simp [bodyAreas], fun _ hc => hc⟩

theorem restore_body_frame {s u t : State} {w : Nat}
    (fit : arrAt w 28 ≤ bytesOf s)
    (priorFrame : Frame (bodyAreas s) s.mem u.mem)
    (restored : Frame [⟨off (wsOf s) (scratch w), 32⟩, ⟨off (wsOf s) (arrAt w 4), 8 * w⟩] u.mem t.mem) :
    Frame (bodyAreas s) s.mem t.mem := by
  apply priorFrame.trans
  apply restored.sub
  intro r hr
  refine ⟨⟨wsOf s, bytesOf s⟩, by simp [bodyAreas], ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · apply Offset.sub_base
    have := scratch_start w
    have := array_monotone w (show 2 ≤ 28 by decide)
    omega
  · apply Offset.sub_base
    have := array_fits_bytes fit (show 4 < 28 by decide)
    omega

theorem RoundABI.return_above_frame {s : State} (A : RoundABI s) :
    (s.gpr .esp).setWidth 64 = off (entryFrame s).base VG.Impl.MillerRabin.X86.frameBytes := by
  have low := A.stackLow
  have bound := (s.gpr .esp).isLt
  apply BitVec.eq_of_toNat_eq
  simp only [off, allocFrame_esp, byteAddr, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub,
    BitVec.toNat_ofNat, VG.Impl.MillerRabin.X86.frameBytes]
  change 1172 ≤ (s.gpr .esp).toNat at low
  omega

theorem RoundABI.return_unchanged {s t : State} (A : RoundABI s)
    (F : Frame (bodyAreas s) s.mem t.mem) :
    t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
  refine F.readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [bodyAreas, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact A.retScratch
  · rw [A.return_above_frame]
    exact Offset.disjoint_base _ (Nat.le_refl _) (by decide)
  · rw [A.return_above_frame]
    change Region.Disjoint ⟨off (entryFrame s).base VG.Impl.MillerRabin.X86.frameBytes, 4⟩
      ⟨(((allocFrame VG.Impl.MillerRabin.X86.frameBytes s).gpr .esp) - BitVec.ofNat 32 40).setWidth 64, 40⟩
    rw [Taint.sub_setWidth (A.call_room (t := allocFrame VG.Impl.MillerRabin.X86.frameBytes s) rfl).low]
    exact Offset.disjoint_below _ (by decide)

end VG.Proof.MillerRabin.X86
