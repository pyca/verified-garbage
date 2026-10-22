module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.PHashFrame
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PReduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.Generation.Memory

/-! Modulus construction retains q, the controller, and all external randomness tapes. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86

def ConstructionFrame (base : Addr) (sp : BitVec 32) (s t : State) : Prop :=
  Frame [⟨base, montgomeryBytes⟩, ⟨off base Layout.hash, Layout.q - Layout.hash⟩,
    ⟨off base Layout.p, 768⟩, ⟨off base Layout.arithmetic, Layout.arithmeticBytes⟩, below sp 52] s.mem t.mem

theorem construction_hash_frame {s t : State} {base : Addr}
    (F : PHashFrame base (s.gpr .esp) s t) : ConstructionFrame base (s.gpr .esp) s t := by
  apply F.sub
  intro region hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨⟨off base Layout.hash, Layout.q - Layout.hash⟩, by simp,
      Offset.sub base (by decide) (by decide)⟩
  · exact ⟨⟨off base Layout.hash, Layout.q - Layout.hash⟩, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨⟨off base Layout.hash, Layout.q - Layout.hash⟩, by simp,
      Offset.sub base (by decide) (by decide)⟩
  · exact ⟨below (s.gpr .esp) 52, by simp, fun _ h => h⟩

theorem construction_shape_frame {s t : State} {base : Addr} {len : Nat}
    (F : Frame [⟨off base Layout.shaped, len⟩] s.mem t.mem) (length : len ≤ 384) :
    ConstructionFrame base (s.gpr .esp) s t := by
  apply F.sub
  intro region hr
  rw [List.mem_singleton.mp hr]
  exact ⟨⟨off base Layout.hash, Layout.q - Layout.hash⟩, by simp,
    Offset.sub base (by decide) (by unfold Layout.hash Layout.q Layout.shaped; omega)⟩

theorem construction_reduction_frame {s t : State} {base : Addr} {n : Nat}
    (F : PReductionFrame base (s.gpr .esp) n s t) (upper : n ≤ 48) (low : 52 ≤ (s.gpr .esp).toNat) :
    ConstructionFrame base (s.gpr .esp) s t := by
  apply F.sub
  intro region hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨base, montgomeryBytes⟩, by simp, fun _ h => h⟩
  · exact ⟨⟨off base Layout.arithmetic, Layout.arithmeticBytes⟩, by simp, fun _ h => h⟩
  · exact ⟨⟨off base Layout.p, 768⟩, by simp, Region.sub_prefix (by omega)⟩
  · exact ⟨⟨off base Layout.p, 768⟩, by simp,
      Offset.sub base (by decide) (by unfold Layout.p Layout.exponent; omega)⟩
  · exact ⟨below (s.gpr .esp) 52, by simp, below_sub (by decide) low⟩

theorem construction_q_bytes {s t : State} {base : Addr} {bytes len : Nat}
    (F : ConstructionFrame base (s.gpr .esp) s t) (capacity : 40960 ≤ bytes)
    (room : RoundRoom (s.gpr .esp) base bytes) (length : len ≤ 32) :
    Spec.Rsa.bytesAt t.mem (off base Layout.q) len = Spec.Rsa.bytesAt s.mem (off base Layout.q) len := by
  apply VG.Proof.Dsa.Generation.frame_bytesAt F ?_ (by omega)
  intro region hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Offset.disjoint_base base (by decide) (by unfold Layout.q; omega)
  · exact Offset.disjoint base (.inr (by decide)) (by unfold Layout.q; omega) (by decide)
  · exact Offset.disjoint base (.inl (by unfold Layout.q Layout.p; omega)) (by unfold Layout.q; omega) (by decide)
  · exact Offset.disjoint base (.inl (by unfold Layout.q Layout.arithmetic; omega)) (by unfold Layout.q; omega) (by decide)
  · exact ((room.apart.sub_left (below_sub (by decide) room.low)).sub_right
      (Offset.sub_base base (by unfold Layout.q; omega))).symm

theorem construction_enclose {s t : State} {base : Addr} {bytes : Nat}
    (F : ConstructionFrame base (s.gpr .esp) s t) (capacity : 40960 ≤ bytes)
    (room : RoundRoom (s.gpr .esp) base bytes) :
    Frame [⟨base, bytes⟩, below (s.gpr .esp) 1184] s.mem t.mem := by
  apply F.sub
  intro region hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨base, bytes⟩, by simp, Region.sub_prefix (by unfold montgomeryBytes; omega)⟩
  · exact ⟨⟨base, bytes⟩, by simp, Offset.sub_base base (by unfold Layout.hash Layout.q; omega)⟩
  · exact ⟨⟨base, bytes⟩, by simp, Offset.sub_base base (by unfold Layout.p; omega)⟩
  · exact ⟨⟨base, bytes⟩, by simp, Offset.sub_base base (by unfold Layout.arithmetic Layout.arithmeticBytes; omega)⟩
  · exact ⟨below (s.gpr .esp) 1184, by simp, below_sub (by decide) room.low⟩

theorem construction_control {s t : State} {base : Addr} {bytes : Nat}
    (F : ConstructionFrame base (s.gpr .esp) s t) (capacity : 40960 ≤ bytes)
    (room : RoundRoom (s.gpr .esp) base bytes) : ControlKeeps base s.mem t.mem := by
  intro d lo hi
  apply F.readW (r := ⟨off base d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Offset.disjoint_base base (by unfold Layout.control montgomeryBytes at *; omega)
      (by unfold Layout.control at hi; omega)
  · exact Offset.disjoint base (.inr (by unfold Layout.hash Layout.q Layout.control at *; omega))
      (by unfold Layout.control at hi; omega) (by decide)
  · exact Offset.disjoint base (.inr (by unfold Layout.p Layout.control at *; omega))
      (by unfold Layout.control at hi; omega) (by decide)
  · exact Offset.disjoint base (.inl (by unfold Layout.arithmetic Layout.control at *; omega))
      (by unfold Layout.control at hi; omega) (by decide)
  · exact ((room.apart.sub_left (below_sub (by decide) room.low)).sub_right
      (Offset.sub_base base (by unfold Layout.control at hi; omega))).symm

end VG.Proof.Dsa.X86.Generation
