module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashWorkspacePointers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers

/-! Supply the existing hash geometry from the reserved generation workspace. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

theorem hash_workspace {H : Hash} (ok : HashOK H) {s : State} {base : Addr} {bytes len : Nat}
    {data : BitVec 32} (scr : Scr s base bytes) (capacity : 40960 ≤ bytes)
    (room : RoundRoom (s.gpr .esp) base bytes)
    (small : len < 2 ^ 32) (dataFit : data.toNat + len ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (data.setWidth 64) len)
    (dataHash : Region.Disjoint ⟨data.setWidth 64, len⟩ ⟨off base Layout.hash, 8192⟩)
    (dataStack : Region.Disjoint (below (s.gpr .esp) 1184) ⟨data.setWidth 64, len⟩) :
    HashGeometry ok (s.gpr .edi + BitVec.ofNat 32 Layout.hash) data
      (s.gpr .edi + BitVec.ofNat 32 subgroupHashDigest)
      (s.gpr .edi + BitVec.ofNat 32 subgroupHashScratch) len (pushed [.edi] s) := by
  have sizes : H.S ≤ 256 ∧ H.F ≤ 64 ∧ ok.Wb ≤ 512 :=
    ⟨ok.hSB, ok.hF, Nat.le_trans ok.hWb (Nat.mul_le_mul_left 8 ok.hW)⟩
  have stAddr := workspace_pointer_address scr (d := Layout.hash) (by unfold Layout.hash; omega)
  have dgAddr := workspace_pointer_address scr (d := subgroupHashDigest)
    (by unfold subgroupHashDigest subgroupHashScratch Layout.hash; omega)
  have scAddr := workspace_pointer_address scr (d := subgroupHashScratch)
    (by unfold subgroupHashScratch Layout.hash; omega)
  have stSmall : Layout.hash + H.S ≤ 40960 := by unfold Layout.hash; omega
  have dgSmall : subgroupHashDigest + H.F ≤ 40960 := by unfold subgroupHashDigest subgroupHashScratch Layout.hash; omega
  have scSmall : subgroupHashScratch + ok.Wb ≤ 40960 := by unfold subgroupHashScratch Layout.hash; omega
  have stackSub := pushed_hash_stack room
  have stackWorkspace := room.apart.sub_left stackSub
  have stFit : Layout.hash + H.S ≤ bytes := by unfold Layout.hash; omega
  have dgFit : subgroupHashDigest + H.F ≤ bytes := by unfold subgroupHashDigest subgroupHashScratch Layout.hash; omega
  have scFit : subgroupHashScratch + ok.Wb ≤ bytes := by unfold subgroupHashScratch Layout.hash; omega
  refine ⟨small, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, dataFit, ?_, ?_⟩
  · rw [pushed_esp, VG.X86.sub_toNat (by simpa only [List.length_cons, List.length_nil] using
      (show 4 ≤ (s.gpr .esp).toNat by have := room.low; omega))]
    simp only [List.length_cons, List.length_nil]
    have := room.low
    omega
  · apply Covers.one
    rw [pushed_rd, pushed_wr]
    obtain ⟨region, hr, hc⟩ := read
    refine ⟨region, ?_, hc⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  · rw [stAddr, dgAddr, scAddr]
    intro address count ⟨region, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have write (d size : Nat) (fit : d + size ≤ bytes) : InRegions (pushed [.edi] s).wr (off base d) size := by
      rw [pushed_wr]
      obtain ⟨r, h, c⟩ := scr.write fit
      exact ⟨r, List.mem_cons_of_mem _ h, c⟩
    rcases hr with rfl | rfl | rfl
    · exact Covers.one (write _ _ stFit) address count ⟨_, List.mem_singleton_self _, hc⟩
    · exact Covers.one (write _ _ dgFit) address count ⟨_, List.mem_singleton_self _, hc⟩
    · exact Covers.one (write _ _ scFit) address count ⟨_, List.mem_singleton_self _, hc⟩
  · rw [stAddr, dgAddr]
    exact Offset.disjoint base (.inl (by unfold subgroupHashDigest subgroupHashScratch Layout.hash; omega)) (by omega) (by omega)
  · rw [stAddr, scAddr]
    exact Offset.disjoint base (.inl (by unfold subgroupHashScratch Layout.hash; omega)) (by omega) (by omega)
  · rw [dgAddr, scAddr]
    exact Offset.disjoint base (.inr (by unfold subgroupHashDigest; omega)) (by omega) (by omega)
  · rw [stAddr]; exact dataHash.sub_right (Region.sub_prefix (Nat.le_trans ok.hSB (by decide)))
  · rw [dgAddr]; exact dataHash.sub_right (Offset.sub base
      (by decide)
      (Nat.le_trans (Nat.add_le_add_left ok.hF subgroupHashDigest) (by decide)))
  · rw [scAddr]; exact dataHash.sub_right (Offset.sub base
      (by decide)
      (Nat.le_trans (Nat.add_le_add_left sizes.2.2 subgroupHashScratch) (by decide)))
  · rw [stAddr]; exact stackWorkspace.sub_right (Offset.sub_base base stFit)
  · exact dataStack.sub_left stackSub
  · rw [dgAddr]; exact stackWorkspace.sub_right (Offset.sub_base base dgFit)
  · rw [scAddr]; exact stackWorkspace.sub_right (Offset.sub_base base scFit)
  · exact workspace_pointer_fit scr (by unfold Layout.hash; omega)
  · exact workspace_pointer_fit scr (by unfold subgroupHashDigest subgroupHashScratch Layout.hash; omega)
  · exact workspace_pointer_fit scr (by unfold subgroupHashScratch Layout.hash; omega)

end VG.Proof.Dsa.X86.Generation
