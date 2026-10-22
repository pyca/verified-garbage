module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashDestinationFrame
import VerifiedGarbage.Proof.Framework.Offset

/-! The subgroup candidate occupies the reserved 32-byte q buffer. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

def subgroupAreas {H : Hash} (ok : HashOK H) (s : State) : List Region := hashCopyAreas ok s Layout.q

def SubgroupCandidateFrame (base : Addr) (sp : BitVec 32) (s t : State) : Prop :=
  Frame [⟨off base Layout.hash, 8192⟩, ⟨off base Layout.q, 32⟩, below sp 52] s.mem t.mem

theorem subgroup_saved_apart {H : Hash} (ok : HashOK H) {s : State} {base : Addr} {bytes : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (room : RoundRoom (s.gpr .esp) base bytes)
    (width : H.D ≤ 32) :
    ∀ region ∈ subgroupAreas ok s, Region.Disjoint
      ⟨((pushed [.edi] s).gpr .esp).setWidth 64, 4⟩ region :=
  hash_saved_apart ok scr capacity room (by unfold Layout.q; omega)

theorem subgroup_candidate_frame {H : Hash} (ok : HashOK H) {s t : State} {base : Addr} {bytes : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (room : RoundRoom (s.gpr .esp) base bytes)
    (width : H.D ≤ 32) (F : Frame (below (s.gpr .esp) 4 :: subgroupAreas ok s) s.mem t.mem) :
    SubgroupCandidateFrame base (s.gpr .esp) s t := by
  apply (hash_destination_frame ok scr capacity room (by unfold Layout.q; omega) F).sub
  intro region hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨off base Layout.hash, 8192⟩, by simp, fun _ h => h⟩
  · exact ⟨⟨off base Layout.q, 32⟩, by simp, Region.sub_prefix width⟩
  · exact ⟨below (s.gpr .esp) 52, by simp, fun _ h => h⟩

end VG.Proof.Dsa.X86.Generation
