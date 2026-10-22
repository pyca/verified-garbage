module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashDigest
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashDestinationFrame
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Offset

/-! The same reserved hash workspace serves external seeds and internally wrapped seeds. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

theorem hash_digest_workspace {H : Hash} (ok : HashOK H) {s : State} {base : Addr}
    {bytes len destination : Nat} {data : BitVec 32} {input : List Byte}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (room : RoundRoom (s.gpr .esp) base bytes)
    (source : s.gpr .esi = data) (small : len < 2 ^ 32) (dataFit : data.toNat + len ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (data.setWidth 64) len)
    (dataHash : Region.Disjoint ⟨data.setWidth 64, len⟩ ⟨off base Layout.hash, 8192⟩)
    (dataStack : Region.Disjoint (below (s.gpr .esp) 1184) ⟨data.setWidth 64, len⟩)
    (seedBytes : Spec.Sha256.bytesAt s.mem (data.setWidth 64) len = input)
    (destinationLow : Layout.wrappedSeed ≤ destination) (destinationFit : destination + H.D < bytes) :
    WP isa (hashDigest H len destination) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base destination) H.D = ok.SH.H.hash input ∧
      HashCopyFrame base (s.gpr .esp) destination H.D s t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := by
  have sizes : H.D ≤ 64 := Nat.le_trans ok.hDF ok.hF
  have geometry := hash_workspace ok scr capacity room small dataFit read dataHash dataStack
  have seedPushed : Spec.Sha256.bytesAt (pushed [.edi] s).mem (data.setWidth 64) len = input := by
    change Spec.Rsa.bytesAt (pushed [.edi] s).mem (data.setWidth 64) len = input
    rw [VG.Proof.Dsa.Generation.frame_bytesAt
      (pushed_frame (s := s) (rs := [.edi]) (by decide)
        (by change 4 ≤ (s.gpr .esp).toNat; have := room.low; omega))
      (by intro region hr; rw [List.mem_singleton.mp hr]; exact dataStack.symm.sub_right (below_sub (by decide) room.low))
      (by omega)]
    exact seedBytes
  have dstAddr := workspace_pointer_address scr (d := destination) (by omega)
  have digestAddr := workspace_pointer_address scr (d := subgroupHashDigest)
    (by unfold subgroupHashDigest subgroupHashScratch Layout.hash; omega)
  have write : InRegions (pushed [.edi] s).wr (off base destination) H.D := by
    rw [pushed_wr]
    obtain ⟨r, hr, hc⟩ := scr.write (d := destination) (n := H.D) (by omega)
    exact ⟨r, List.mem_cons_of_mem _ hr, hc⟩
  refine WP.mono (hash_digest (ok := ok) (destination := destination)
    (dst := s.gpr .edi + BitVec.ofNat 32 destination)
    (scratch := s.gpr .edi + BitVec.ofNat 32 subgroupHashScratch)
    (digest := s.gpr .edi + BitVec.ofNat 32 subgroupHashDigest) rfl source rfl
    (by rw [BitVec.add_assoc]; rfl)
    (by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by
        unfold subgroupHashScratch Layout.hash Layout.wrappedSeed at *; omega)])
    geometry seedPushed (workspace_pointer_fit scr destinationFit)
    (by rw [dstAddr]; exact write)
    (by
      rw [digestAddr, dstAddr]
      exact Offset.disjoint base (.inl (by unfold subgroupHashDigest subgroupHashScratch Layout.hash Layout.wrappedSeed at *; omega))
        (by unfold subgroupHashDigest subgroupHashScratch Layout.hash; omega) (by have := scr.nowrap; omega))
    (hash_saved_apart ok scr capacity room (by omega)) (by have := room.low; omega))
    fun t ⟨value, F, K⟩ => ?_
  rw [dstAddr] at value
  exact ⟨value, hash_destination_frame ok scr capacity room (by omega) F, K⟩

end VG.Proof.Dsa.X86.Generation
