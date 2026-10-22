module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.PHashOne
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ControlKeeps
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Offset

/-! Hash contributions retain all controller fields and previously written contributions. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86

def PHashFrame (base : Addr) (sp : BitVec 32) (s t : State) : Prop :=
  Frame [⟨off base Layout.wrappedSeed, 32⟩, ⟨off base Layout.hash, 8192⟩,
    ⟨off base Layout.hashes, 384⟩, below sp 52] s.mem t.mem

theorem contribution_fit {count j len : Nat} (fit : (count + 1) * len ≤ 384) :
    (count - j) * len + len ≤ 384 := by
  have h := Nat.mul_le_mul_right len (show count - j + 1 ≤ count + 1 by omega)
  rw [Nat.add_mul, Nat.one_mul] at h
  omega

theorem p_hash_frame {s t : State} {base : Addr} {len destination digestLen : Nat}
    (F : PHashOneFrame base (s.gpr .esp) len destination digestLen s t)
    (length : len ≤ 32) (lower : Layout.hashes ≤ destination) (upper : destination + digestLen ≤ Layout.hashes + 384) :
    PHashFrame base (s.gpr .esp) s t := by
  apply F.sub
  intro region hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨⟨off base Layout.wrappedSeed, 32⟩, by simp, Region.sub_prefix length⟩
  · exact ⟨⟨off base Layout.hash, 8192⟩, by simp, fun _ h => h⟩
  · exact ⟨⟨off base Layout.hashes, 384⟩, by simp, Offset.sub base lower upper⟩
  · exact ⟨below (s.gpr .esp) 52, by simp, fun _ h => h⟩

theorem p_hash_enclose {s t : State} {base : Addr} {bytes : Nat}
    (F : PHashFrame base (s.gpr .esp) s t) (capacity : 40960 ≤ bytes) (room : RoundRoom (s.gpr .esp) base bytes) :
    Frame [⟨base, bytes⟩, below (s.gpr .esp) 1184] s.mem t.mem := by
  apply F.sub
  intro region hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨⟨base, bytes⟩, by simp, Offset.sub_base base (by unfold Layout.wrappedSeed; omega)⟩
  · exact ⟨⟨base, bytes⟩, by simp, Offset.sub_base base (by unfold Layout.hash; omega)⟩
  · exact ⟨⟨base, bytes⟩, by simp, Offset.sub_base base (by unfold Layout.hashes; omega)⟩
  · exact ⟨below (s.gpr .esp) 1184, by simp, below_sub (by decide) room.low⟩

theorem p_hash_control {s t : State} {base : Addr} {bytes : Nat}
    (F : PHashFrame base (s.gpr .esp) s t) (capacity : 40960 ≤ bytes) (room : RoundRoom (s.gpr .esp) base bytes) :
    ControlKeeps base s.mem t.mem := by
  intro d lo hi
  apply F.readW (r := ⟨off base d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint base (.inr (by unfold Layout.wrappedSeed Layout.control at *; omega))
      (by unfold Layout.control at lo hi; omega) (by decide)
  · exact Offset.disjoint base (.inr (by unfold Layout.hash Layout.control at *; omega))
      (by unfold Layout.control at lo hi; omega) (by decide)
  · exact Offset.disjoint base (.inr (by unfold Layout.hashes Layout.control at *; omega))
      (by unfold Layout.control at lo hi; omega) (by decide)
  · exact ((room.apart.sub_left (below_sub (by decide) room.low)).sub_right
      (Offset.sub_base base (by unfold Layout.control at lo hi; omega))).symm

theorem p_hash_metadata {s t : State} {base : Addr} {bytes d : Nat}
    (F : PHashFrame base (s.gpr .esp) s t) (capacity : 40960 ≤ bytes) (room : RoundRoom (s.gpr .esp) base bytes)
    (lower : Layout.packed ≤ d) (upper : d + 4 ≤ Layout.control) :
    t.mem.readW (off base d) 32 = s.mem.readW (off base d) 32 := by
  apply F.readW (r := ⟨off base d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint base (.inr (by unfold Layout.wrappedSeed Layout.packed at *; omega))
      (by unfold Layout.control at upper; omega) (by decide)
  · exact Offset.disjoint base (.inr (by unfold Layout.hash Layout.packed at *; omega))
      (by unfold Layout.control at upper; omega) (by decide)
  · exact Offset.disjoint base (.inr (by unfold Layout.hashes Layout.packed at *; omega))
      (by unfold Layout.control at upper; omega) (by decide)
  · exact ((room.apart.sub_left (below_sub (by decide) room.low)).sub_right
      (Offset.sub_base base (by unfold Layout.control at upper; omega))).symm

theorem p_hash_previous {s t : State} {base : Addr} {bytes len count j i width : Nat}
    (F : PHashOneFrame base (s.gpr .esp) len (Layout.hashes + (count - j) * width) width s t)
    (capacity : 40960 ≤ bytes) (room : RoundRoom (s.gpr .esp) base bytes)
    (length : len ≤ 32) (fit : (count + 1) * width ≤ 384) (previous : i < j) (index : j ≤ count) :
    Spec.Rsa.bytesAt t.mem (off base (Layout.hashes + (count - i) * width)) width =
      Spec.Rsa.bytesAt s.mem (off base (Layout.hashes + (count - i) * width)) width := by
  have one := contribution_fit (j := i) fit
  have two := contribution_fit (j := j) fit
  have separate := Nat.mul_le_mul_right width (show count - j + 1 ≤ count - i by omega)
  rw [Nat.add_mul, Nat.one_mul] at separate
  apply VG.Proof.Dsa.Generation.frame_bytesAt F ?_ (by omega)
  intro region hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint base (.inr (by unfold Layout.hashes Layout.wrappedSeed; omega))
      (by unfold Layout.hashes; omega) (by unfold Layout.wrappedSeed; omega)
  · exact Offset.disjoint base (.inr (by unfold Layout.hashes Layout.hash; omega))
      (by unfold Layout.hashes; omega) (by decide)
  · exact Offset.disjoint base (.inr (by omega)) (by unfold Layout.hashes; omega) (by unfold Layout.hashes; omega)
  · exact ((room.apart.sub_left (below_sub (by decide) room.low)).sub_right
      (Offset.sub_base base (by unfold Layout.hashes; omega))).symm

end VG.Proof.Dsa.X86.Generation
