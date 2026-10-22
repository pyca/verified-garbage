module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.SubgroupCandidate
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SubgroupFrame
public import VerifiedGarbage.Proof.Dsa.X86.Generation.WitnessTape
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Offset

/-! The subgroup hash wrapper runs in the generation workspace with an external seed tape. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

theorem subgroup_hash {H : Hash} (ok : HashOK H) {s : State} {base : Addr} {bytes bits : Nat} {seed : List Byte}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (room : RoundRoom (s.gpr .esp) base bytes)
    (tape : WitnessTape base bytes (s.gpr .esp) (s.gpr .esi) seed s)
    (positive : seed ≠ []) (small : seed.length < 2 ^ 32)
    (hash : ok.SH.H.hash seed = Spec.Dsa.seedHash bits seed)
    (digestLength : (Spec.Dsa.seedHash bits seed).length = H.D)
    (width : 8 * H.D = bits) (lower : 2 ≤ H.D) (upper : H.D ≤ 32) :
    WP isa (subgroupCandidate H seed.length) s fun t =>
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem (off base Layout.q) H.D) = Spec.Dsa.qCandidate bits seed ∧
      SubgroupCandidateFrame base (s.gpr .esp) s t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := by
  have geometry := hash_workspace ok scr capacity room small tape.fit (tape.read positive)
    (tape.workspace.sub_right (Offset.sub_base base (by unfold Layout.hash; omega))) tape.stack.symm
  have seedBytes : Spec.Sha256.bytesAt (pushed [.edi] s).mem ((s.gpr .esi).setWidth 64) seed.length = seed := by
    change Spec.Rsa.bytesAt (pushed [.edi] s).mem ((s.gpr .esi).setWidth 64) seed.length = seed
    rw [VG.Proof.Dsa.Generation.frame_bytesAt
      (pushed_frame (s := s) (rs := [.edi]) (by decide)
        (by change 4 ≤ (s.gpr .esp).toNat; have := room.low; omega))
      (by intro region hr; rw [List.mem_singleton.mp hr]; exact tape.stack.sub_right (below_sub (by decide) room.low))
      (by omega)]
    exact tape.data
  have dstAddr := workspace_pointer_address scr (d := Layout.q) (by unfold Layout.q; omega)
  have digestAddr := workspace_pointer_address scr (d := subgroupHashDigest)
    (by unfold subgroupHashDigest subgroupHashScratch Layout.hash; omega)
  have write : InRegions (pushed [.edi] s).wr (off base Layout.q) H.D := by
    rw [pushed_wr]
    obtain ⟨r, hr, hc⟩ := scr.write (d := Layout.q) (n := H.D) (by unfold Layout.q; omega)
    exact ⟨r, List.mem_cons_of_mem _ hr, hc⟩
  refine WP.mono (subgroup_candidate (ok := ok) (bits := bits)
    (dst := s.gpr .edi + BitVec.ofNat 32 Layout.q)
    (scratch := s.gpr .edi + BitVec.ofNat 32 subgroupHashScratch)
    (digest := s.gpr .edi + BitVec.ofNat 32 subgroupHashDigest) rfl rfl rfl
    (by rw [BitVec.add_assoc]; rfl) (by rw [BitVec.add_assoc]; rfl)
    geometry seedBytes hash digestLength width lower
    (workspace_pointer_fit scr (by unfold Layout.q; omega))
    (by rw [dstAddr]; exact write)
    (by
      rw [digestAddr, dstAddr]
      exact Offset.disjoint base
        (.inl (by unfold subgroupHashDigest subgroupHashScratch Layout.hash Layout.q; omega))
        (by unfold subgroupHashDigest subgroupHashScratch Layout.hash; omega) (by unfold Layout.q; omega))
    (subgroup_saved_apart ok scr capacity room upper) (by have := room.low; omega))
    fun t ⟨value, F, K⟩ => ?_
  rw [dstAddr] at value
  exact ⟨value, subgroup_candidate_frame ok scr capacity room upper F, K⟩

end VG.Proof.Dsa.X86.Generation
