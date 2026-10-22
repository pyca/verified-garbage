module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundCall
public import VerifiedGarbage.Proof.Dsa.X86.Generation.WitnessPrepared
import VerifiedGarbage.Proof.Framework.Offset

/-! Retain caller constants, tape counters, and saved q/p buffers across a round. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation
open VG.Proof.Mont VG.Proof.Mont.X86

theorem RoundRoom.callRoom {sp : BitVec 32} {base : Addr} {bytes : Nat}
    (room : RoundRoom sp base bytes) : CallRoom sp base bytes :=
  ⟨by have := room.low; omega, room.apart.sub_left (below_sub (by decide) room.low)⟩

theorem round_context {s t : State} {base : Addr} {bytes n candidate : Nat}
    (C : WitnessContext base n candidate s) (capacity : 40960 ≤ bytes)
    (room : RoundRoom (s.gpr .esp) base bytes)
    (F : Frame [⟨off base Layout.arithmetic, 12288⟩, below (s.gpr .esp) 1184] s.mem t.mem)
    (K : Keeps [.eax, .ecx, .edx] s t) : WitnessContext base n candidate t := by
  apply C.frame_keep K (by decide) (by decide) F
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.base_disjoint base (by decide : montgomeryBytes ≤ Layout.arithmetic) (by decide)
  · exact (room.apart.sub_right (Region.sub_prefix (by unfold montgomeryBytes; omega))).symm

theorem round_middle_read {s t : State} {base : Addr} {bytes d size : Nat}
    (capacity : 40960 ≤ bytes) (room : RoundRoom (s.gpr .esp) base bytes)
    (F : Frame [⟨off base Layout.arithmetic, 12288⟩, below (s.gpr .esp) 1184] s.mem t.mem)
    (fit : d + size ≤ Layout.arithmetic) :
    t.mem.read (off base d) size = s.mem.read (off base d) size := by
  apply F.read (r := ⟨off base d, size⟩) (Region.contains_self _ _) ?_
    (by unfold Layout.arithmetic at fit; omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint base (.inl fit) (by unfold Layout.arithmetic at fit; omega) (by decide)
  · exact (room.apart.sub_right (Offset.sub_base base (by
      unfold Layout.arithmetic at fit; omega))).symm

theorem witness_middle_read {s t : State} {base : Addr} {bytes n d size : Nat}
    (capacity : 40960 ≤ bytes) (room : CallRoom (s.gpr .esp) base bytes) (upper : n ≤ 48)
    (F : WitnessFrame base (s.gpr .esp) n s t)
    (lower : montgomeryBytes ≤ d) (fit : d + size ≤ Layout.arithmetic) :
    t.mem.read (off base d) size = s.mem.read (off base d) size := by
  apply F.read (r := ⟨off base d, size⟩) (Region.contains_self _ _) ?_
    (by unfold Layout.arithmetic at fit; omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint base (.inr (by
      simp only [VG.Impl.Mont.X86.Dynamic.slot, VG.Impl.Mont.X86.Dynamic.stride, montgomeryBytes] at lower ⊢; omega))
      (by unfold Layout.arithmetic at fit; omega)
      (by simp only [VG.Impl.Mont.X86.Dynamic.slot, VG.Impl.Mont.X86.Dynamic.stride]; omega)
  · exact Offset.disjoint base (.inr (by
      simp only [montgomeryScratch, Spec.Rsa.MontMul.scratchBytes, montgomeryBytes] at lower ⊢; omega))
      (by unfold Layout.arithmetic at fit; omega)
      (by simp only [montgomeryScratch, Spec.Rsa.MontMul.scratchBytes]; omega)
  · exact Offset.disjoint base (.inl (by have : Layout.arithmetic ≤ Layout.arithmetic + Spec.Rsa.Mont.arrAt n 5 := Nat.le_add_right _ _; omega))
      (by unfold Layout.arithmetic at fit; omega)
      (by simp only [Layout.arithmetic, Spec.Rsa.Mont.arrAt, Spec.Rsa.Mont.hdrBytes]; omega)
  · exact (room.apart.sub_right (Offset.sub_base base (by
      unfold Layout.arithmetic at fit; omega))).symm

end VG.Proof.Dsa.X86.Generation
