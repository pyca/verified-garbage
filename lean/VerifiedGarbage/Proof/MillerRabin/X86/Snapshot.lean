module

public import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceCongruence
public import VerifiedGarbage.Proof.MillerRabin.X86.SaveProtected
import VerifiedGarbage.Proof.Framework.Offset

/-! # Retain the protected bytes and establish the arithmetic snapshot -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt wOf)

structure SnapshotReady (s σ : State) : Prop where
  context : ProtectedContext σ (wsOf s) (bytesOf s)
  room : CallRoom (σ.gpr .esp) (wsOf s) (bytesOf s)
  sp : σ.gpr .esp = (allocFrame VG.Impl.MillerRabin.X86.frameBytes s).gpr .esp
  wr : σ.wr = (allocFrame VG.Impl.MillerRabin.X86.frameBytes s).wr
  frame : Frame [entryFrame s] s.mem σ.mem
  saved : Spill.Saved σ.mem (off (byteAddr (σ.gpr .esp)))
    (allocFrame VG.Impl.MillerRabin.X86.frameBytes s).gpr savedRegisters
  length : σ.mem.readW (off (byteAddr (σ.gpr .esp)) savedLength) 32 = arg s 1
  layout : Spec.MillerRabin.Layout Spec.MillerRabin.compact σ.mem (wsOf s) (arg s 1).toNat
  prepared : Spec.MillerRabin.Prepared Spec.MillerRabin.compact σ.mem (wsOf s)
  width : wOf σ.mem (wsOf s) = wOf s.mem (wsOf s)
  tail : σ.mem.read (off (byteAddr (σ.gpr .esp)) savedTail) 32 =
    σ.mem.read (off (wsOf s) (scratch (wOf s.mem (wsOf s)))) 32
  array : σ.mem.read (off (byteAddr (σ.gpr .esp)) savedArray) (8 * wOf s.mem (wsOf s)) =
    σ.mem.read (off (wsOf s) (arrAt (wOf s.mem (wsOf s)) 4)) (8 * wOf s.mem (wsOf s))

theorem snapshot_ok {s u : State} (A : RoundABI s) (entry : EntryReady s u) :
    WP isa saveProtected u (SnapshotReady s) := by
  obtain ⟨layoutU, preparedU, widthU⟩ := workspace_congr (frame_workspace_same A entry.frame) A.layout A.prepared
  have facts := round_facts_of (bytes := bytesOf s) rfl widthU layoutU preparedU entry.length
  have spU := entry.keeps.1 .esp (by decide)
  refine WP.mono (saveProtected_ok entry.context facts.lower facts.upper facts.fit facts.width) ?_
  rintro σ ⟨tail, array, frame, keeps⟩
  have spσ : σ.gpr .esp = u.gpr .esp := keeps.1 _ (by decide)
  have wide : Frame [⟨byteAddr (u.gpr .esp), VG.Impl.MillerRabin.X86.frameBytes⟩] u.mem σ.mem := by
    apply frame.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (saved_array_fits_frame facts.upper)⟩
  have full : Frame [entryFrame s] s.mem σ.mem := by
    have wide' := wide
    rw [spU] at wide'
    exact entry.frame.trans wide'
  have stackWord (d : Nat) (hd : d + 4 ≤ savedTail) :
      σ.mem.readW (off (byteAddr (u.gpr .esp)) d) 32 = u.mem.readW (off (byteAddr (u.gpr .esp)) d) 32 := by
    refine frame.readW (r := ⟨off (byteAddr (u.gpr .esp)) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (.inl hd) (by change d + 4 ≤ 2 ^ 64; change d + 4 ≤ 64 at hd; omega) (by decide)
    · exact Offset.disjoint _ (.inl (by change d + 4 ≤ 96; change d + 4 ≤ 64 at hd; omega))
        (by change d + 4 ≤ 2 ^ 64; change d + 4 ≤ 64 at hd; omega)
        (by have := saved_array_fits_frame facts.upper; change 96 + 8 * _ ≤ 1132 at this
            change 96 + 8 * _ ≤ 2 ^ 64
            omega)
  have sameWS (d n : Nat) (hd : d + n ≤ bytesOf s) :
      σ.mem.read (off (wsOf s) d) n = u.mem.read (off (wsOf s) d) n := by
    have wide0 : Frame [⟨off (byteAddr (u.gpr .esp)) 0, VG.Impl.MillerRabin.X86.frameBytes⟩] u.mem σ.mem := by
      rw [show off (byteAddr (u.gpr .esp)) 0 = byteAddr (u.gpr .esp) from BitVec.add_zero _]
      exact wide
    exact entry.context.stack_frame_read (Nat.le_refl _) wide0 hd
  obtain ⟨layoutσ, preparedσ, widthσ⟩ := workspace_congr (frame_workspace_same A full) A.layout A.prepared
  refine ⟨entry.context.of_keeps keeps, by rw [spσ]; exact entry.room, spσ.trans spU, keeps.2.2.trans entry.keeps.2.2, full, ?_, ?_,
    layoutσ, preparedσ, widthσ, ?_, ?_⟩
  · rw [spσ]
    exact entry.saved.of_readW fun p hp => stackWord p.2 (by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide)
  · rw [spσ, stackWord savedLength (by decide), entry.length]
  · rw [spσ, tail]
    apply Eq.symm
    apply sameWS
    have := facts.fit
    have := scratch_start (wOf s.mem (wsOf s))
    have := array_monotone (wOf s.mem (wsOf s)) (show 2 ≤ 28 by decide)
    omega
  · rw [spσ, array]
    apply Eq.symm
    apply sameWS
    have := array_fits_bytes facts.fit (show 4 < 28 by decide)
    omega

end VG.Proof.MillerRabin.X86
