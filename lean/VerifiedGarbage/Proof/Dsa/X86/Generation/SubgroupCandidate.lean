module

import VerifiedGarbage.Proof.Dsa.X86.Generation.SubgroupArguments
import VerifiedGarbage.Proof.Dsa.X86.Generation.SubgroupNoSp
import VerifiedGarbage.Proof.Dsa.X86.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.X86.Generation.RestoreWorkspace
import VerifiedGarbage.Proof.Framework.OffsetBelow
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashFrame
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Subgroup
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashGeometry
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hash

/-! Save and restore the caller's workspace around the existing hash and byte shaper. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

theorem subgroup_candidate {H : Hash} {ok : HashOK H} {s : State}
    {base data digest scratch dst : BitVec 32} {seedLen bits : Nat} {seed : List Byte}
    (pointer : s.gpr .edi = base) (source : s.gpr .esi = data)
    (scratchPosition : base + BitVec.ofNat 32 subgroupHashScratch = scratch)
    (digestPosition : scratch + 512#32 = digest)
    (candidatePosition : scratch + BitVec.ofNat 32
      (VG.Impl.Dsa.Generation.Layout.q - subgroupHashScratch) = dst)
    (G : HashGeometry ok (base + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.hash)
      data digest scratch seedLen (pushed [.edi] s))
    (seedBytes : Spec.Sha256.bytesAt (pushed [.edi] s).mem (data.setWidth 64) seedLen = seed)
    (hash : ok.SH.H.hash seed = Spec.Dsa.seedHash bits seed)
    (digestLength : (Spec.Dsa.seedHash bits seed).length = H.D)
    (width : 8 * H.D = bits) (lower : 2 ≤ H.D)
    (dstFit : dst.toNat + H.D ≤ 2 ^ 32)
    (write : InRegions (pushed [.edi] s).wr (dst.setWidth 64) H.D)
    (apart : Region.Disjoint ⟨digest.setWidth 64, H.D⟩ ⟨dst.setWidth 64, H.D⟩)
    (savedApart : ∀ region ∈ hashAreas ok
      (base + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.hash) digest scratch (pushed [.edi] s) ++
      [⟨dst.setWidth 64, H.D⟩], Region.Disjoint
        ⟨((pushed [.edi] s).gpr .esp).setWidth 64, 4⟩ region)
    (low : 4 ≤ (s.gpr .esp).toNat) :
    WP isa (subgroupCandidate H seedLen) s fun t =>
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem (dst.setWidth 64) H.D) = Spec.Dsa.qCandidate bits seed ∧
      Frame (below (s.gpr .esp) 4 :: (hashAreas ok
        (base + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.hash) digest scratch (pushed [.edi] s) ++
        [⟨dst.setWidth 64, H.D⟩])) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := by
  unfold subgroupCandidate
  refine WP.frame (by decide) (by decide) (by decide)
    (by simpa only [List.length_cons, List.length_nil] using low) (subgroup_body_noSp ok seedLen) ?_
  refine WP.seq (WP.mono (subgroup_arguments (base := base) (s := pushed [.edi] s) (seedLen := seedLen)
    (by rw [pushed_gpr _ _ (by decide)]; exact pointer)) fun a ⟨R, memory, K⟩ => ?_)
  have geometry := G.of_regions K.2.1 K.2.2 (K.1 .esp (by decide))
  have registers : HashRegisters (base + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.hash)
      data scratch seedLen a := by
    rw [pushed_gpr _ _ (by decide), source, scratchPosition] at R
    exact R
  refine WP.mono (q_candidate geometry registers digestPosition candidatePosition
    (by rw [memory]; exact seedBytes) hash digestLength width lower dstFit
    (by rw [K.2.2]; exact write) apart) fun u ⟨value, F, KU⟩ => ?_
  have frame : Frame (hashAreas ok
      (base + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.hash) digest scratch (pushed [.edi] s) ++
      [⟨dst.setWidth 64, H.D⟩]) (pushed [.edi] s).mem u.mem := by
    rw [memory] at F
    simpa only [hashAreas, stk, K.1 .esp (by decide)] using F
  have stack : u.gpr .esp = (pushed [.edi] s).gpr .esp :=
    (KU.1 .esp (by decide)).trans (K.1 .esp (by decide))
  obtain ⟨regs, frameOut⟩ := restore_workspace low stack (KU.2.1.trans K.2.1)
    (KU.2.2.trans K.2.2) frame savedApart
  exact ⟨by rw [popped_mem]; exact value, frameOut, regs⟩

end VG.Proof.Dsa.X86.Generation
