module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashWorkspace
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashFrame
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Offset

/-! Shared frames for retaining a copied digest and restoring the workspace pointer. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

def hashCopyAreas {H : Hash} (ok : HashOK H) (s : State) (destination : Nat) : List Region :=
  hashAreas ok (s.gpr .edi + BitVec.ofNat 32 Layout.hash)
    (s.gpr .edi + BitVec.ofNat 32 subgroupHashDigest)
    (s.gpr .edi + BitVec.ofNat 32 subgroupHashScratch) (pushed [.edi] s) ++
    [⟨(s.gpr .edi + BitVec.ofNat 32 destination).setWidth 64, H.D⟩]

def HashCopyFrame (base : Addr) (sp : BitVec 32) (destination count : Nat) (s t : State) : Prop :=
  Frame [⟨off base Layout.hash, 8192⟩, ⟨off base destination, count⟩, below sp 52] s.mem t.mem

theorem hash_saved_apart {H : Hash} (ok : HashOK H) {s : State} {base : Addr} {bytes destination : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (room : RoundRoom (s.gpr .esp) base bytes)
    (destinationFit : destination + H.D ≤ bytes) :
    ∀ region ∈ hashCopyAreas ok s destination, Region.Disjoint
      ⟨((pushed [.edi] s).gpr .esp).setWidth 64, 4⟩ region := by
  have stack : Region.Sub ⟨((pushed [.edi] s).gpr .esp).setWidth 64, 4⟩ (below (s.gpr .esp) 1184) := by
    rw [pushed_esp]
    exact below_sub (by decide : 4 ≤ 1184) room.low
  have disjoint := room.apart.sub_left stack
  have sizes : H.S ≤ 256 ∧ H.F ≤ 64 ∧ ok.Wb ≤ 512 :=
    ⟨ok.hSB, ok.hF, Nat.le_trans ok.hWb (Nat.mul_le_mul_left 8 ok.hW)⟩
  intro region hr
  simp only [hashCopyAreas, hashAreas, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [workspace_pointer_address scr (by unfold Layout.hash; omega)]
    exact disjoint.sub_right (Offset.sub_base base (by unfold Layout.hash; omega))
  · rw [workspace_pointer_address scr (by unfold subgroupHashDigest subgroupHashScratch Layout.hash; omega)]
    exact disjoint.sub_right (Offset.sub_base base (by unfold subgroupHashDigest subgroupHashScratch Layout.hash; omega))
  · rw [workspace_pointer_address scr (by unfold subgroupHashScratch Layout.hash; omega)]
    exact disjoint.sub_right (Offset.sub_base base (by unfold subgroupHashScratch Layout.hash; omega))
  · have low : 48 ≤ ((pushed [.edi] s).gpr .esp).toNat := by
      rw [pushed_esp, VG.X86.sub_toNat (by simpa only [List.length_cons, List.length_nil] using
        (show 4 ≤ (s.gpr .esp).toNat by have := room.low; omega))]
      simp only [List.length_cons, List.length_nil]
      have := room.low
      omega
    change Region.Disjoint _ (below ((pushed [.edi] s).gpr .esp) 48)
    unfold below
    rw [Taint.sub_setWidth low]
    exact (Offset.below_disjoint _ (by decide : 48 + 4 ≤ 2 ^ 64)).symm
  · rw [workspace_pointer_address scr (by have := ok.hD0; omega)]
    exact disjoint.sub_right (Offset.sub_base base (by have := ok.hD0; omega))

theorem hash_destination_frame {H : Hash} (ok : HashOK H) {s t : State} {base : Addr} {bytes destination : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (room : RoundRoom (s.gpr .esp) base bytes)
    (destinationFit : destination + H.D ≤ bytes) (F : Frame (below (s.gpr .esp) 4 :: hashCopyAreas ok s destination) s.mem t.mem) :
    HashCopyFrame base (s.gpr .esp) destination H.D s t := by
  have sizes : H.S ≤ 256 ∧ H.F ≤ 64 ∧ ok.Wb ≤ 512 :=
    ⟨ok.hSB, ok.hF, Nat.le_trans ok.hWb (Nat.mul_le_mul_left 8 ok.hW)⟩
  apply F.sub
  intro region hr
  simp only [hashCopyAreas, hashAreas, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨below (s.gpr .esp) 52, by simp, below_sub (by decide) (by have := room.low; omega)⟩
  · rw [workspace_pointer_address scr (by unfold Layout.hash; omega)]
    exact ⟨⟨off base Layout.hash, 8192⟩, by simp,
      Region.sub_prefix (Nat.le_trans ok.hSB (by decide))⟩
  · rw [workspace_pointer_address scr (by unfold subgroupHashDigest subgroupHashScratch Layout.hash; omega)]
    exact ⟨⟨off base Layout.hash, 8192⟩, by simp, Offset.sub base
      (by unfold subgroupHashDigest subgroupHashScratch; omega)
      (by unfold subgroupHashDigest subgroupHashScratch; omega)⟩
  · rw [workspace_pointer_address scr (by unfold subgroupHashScratch Layout.hash; omega)]
    exact ⟨⟨off base Layout.hash, 8192⟩, by simp, Offset.sub base
      (by unfold subgroupHashScratch; omega) (by unfold subgroupHashScratch; omega)⟩
  · exact ⟨below (s.gpr .esp) 52, by simp, pushed_hash_stack52⟩
  · rw [workspace_pointer_address scr (by have := ok.hD0; omega)]
    exact ⟨⟨off base destination, H.D⟩, by simp, fun _ h => h⟩

end VG.Proof.Dsa.X86.Generation
