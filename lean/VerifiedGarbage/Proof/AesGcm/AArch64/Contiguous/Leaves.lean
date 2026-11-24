module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.LeafContract
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.PreparedFrame
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Medium
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.ShortCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.StandaloneFrame
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.LeafCT
import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved

/-! Register preservation and stack high-water bounds of the contiguous record
frames, including the called CPU-specific counter and hash functions. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous

open VG VG.AArch64 VG.AArch64.Scrub VG.Impl.Scrub.AArch64
open VG.Impl.AesGcm.AArch64 (Calls)
open VG.Impl.AesGcm.AArch64.Fn (own)
open VG.Impl.AesGcm.AArch64.Contiguous
open VG.Impl.StackScratch.AArch64 (withStackArgScratch)

theorem shortSide : scrubSide shortFrame 368 0 own [] = true := by lit_decide

/-- The selected cipher and hashing implementation supplies these facts once at
registration. All memory and timing proofs below work for every selection. -/
structure BackendFacts (v : GcmImpl) (g : GhashWithImpl) : Prop where
  sizes : 768 ≤ v.calls.pwWn ∧ v.calls.pwWn ≤ 2560 ∧ v.calls.pwWn % 16 = 0
  scratch : v.ctr.scratch ≤ v.calls.pwWn-512
  fallbackOk : Standalone.BodyOk v
  fallbackRel : Standalone.BodyRel v
  fallbackSide : scrubSide (Standalone.frame v.calls) (v.calls.pwWn+32) 0
    (Impl.AesGcm.AArch64.Contiguous.Standalone.clear v.calls) [] = true
  fallbackVectors : (withStackArgScratch (v.calls.pwWn+32) 2
    (Impl.AesGcm.AArch64.Contiguous.Standalone.bodyWith v.calls false)).allInstrs keepsV = true
  prepared (f : Bool) : scrubSide (preparedFrame v.calls g.fn f) (v.calls.pwWn+32) 0 (preparedClear f (!v.calls.stitch)) [] = true
  vectors (f : Bool) : (withStackArgScratch (v.calls.pwWn+32) 3 (preparedBody v.callees g.fn f false)).allInstrs keepsV = true
  mediumSide : scrubSide (Impl.AesGcm.AArch64.Contiguous.MediumDirect.frame v.callees) 752 0 own [] = true
  hash16 : DirectGather.Hash16WithOk
  hash : DirectGather.HashEightWithOk
  stitch : VG.Proof.Gcm.AArch64.Stitch.Gh8Ok
  mul : VG.Proof.Gcm.AArch64.Pmull.MulKey
  preparedKey : ∀ H, VG.Proof.Gcm.AArch64.Pmull.keyV H = VG.Proof.Gcm.AArch64.Pmull.pp H 1

end VG.Proof.AesGcm.AArch64.Contiguous

/-! ## Correctness, trace equality and erasure of each public-length specialization.
All leaves read the plaintext from the source in the caller's initial state. -/

namespace VG.Proof.AesGcm.AArch64.Contiguous
open VG VG.AArch64 VG.AArch64.Scrub VG.Impl.Scrub.AArch64
open VG.Impl.AesGcm.AArch64.Contiguous
open VG.Impl.AesGcm.AArch64.Fn (own)

def standard (s : State) : Prop := (s.gpr .x3).toNat=12 ∧ (s.gpr .x5).toNat≤16
def prepared (fused : Bool) (s : State) : Prop := standard s ∧ (fused=true → 128 ≤ (stackArg s 0).toNat)
def bounded (s : State) : Prop := standard s ∧ (stackArg s 0).toNat ≤ 224
def short (s : State) : Prop := standard s ∧ (stackArg s 0).toNat ≤ 96

theorem generalLeaf {v : GcmImpl} {g : GhashWithImpl} (facts : BackendFacts v g) (sat : ∃ s, (leafContract (fun _ => True)).pre s) :
    VerifiedScrubbed target (Impl.AesGcm.AArch64.Contiguous.Standalone.prog v.calls) (leafContract (fun _ => True)) 0 :=
  Standalone.standaloneLeaf v facts.fallbackOk facts.fallbackRel facts.sizes facts.fallbackVectors facts.fallbackSide sat

theorem shortLeaf (hash : DirectGather.HashEightWithOk) (sat : ∃ s, (leafContract short).pre s) :
    VerifiedScrubbed target (scrubAll 368 0 own shortFrame) (leafContract short) 0 := by
  apply scrubLeaf (by decide) shortSide
  refine ⟨fun _ h => Short.frame_ok hash h.1 h.2.1 h.2.2.1.1 h.2.2.1.2 h.2.2.2
    (DirectGather.keepsV_of_gatherSide shortSide),ct_of ?_,sat⟩
  intro a b pa pb pub
  exact Short.frame_rel hash pa.1 pb.1 pa.2.1 pb.2.1 pa.2.2.1.1 pb.2.2.1.1 pa.2.2.1.2 pb.2.2.1.2
    pa.2.2.2 pb.2.2.2 pub.1

theorem preparedLeaf {v : GcmImpl} {g : GhashWithImpl} (facts : BackendFacts v g) (f : Bool) (sat : ∃ s, (leafContract (prepared f)).pre s) :
    VerifiedScrubbed target (scrubAll (v.calls.pwWn+32) 0 (preparedClear f (!v.calls.stitch)) (preparedFrame v.calls g.fn f))
      (leafContract (prepared f)) 0 := by
  have sz := facts.sizes
  have hv := facts.scratch
  have side := facts.prepared f
  apply scrubLeaf (by omega) side
  refine ⟨fun _ h => Prepared.frame_ok v g f facts.stitch facts.mul facts.preparedKey h.1 h.2.1 h.2.2.1.1 h.2.2.1.2 h.2.2.2
    sz.1 sz.2.1 sz.2.2 hv (facts.vectors f),ct_of ?_,sat⟩
  intro a b pa pb pub
  exact Prepared.frame_rel v g f facts.stitch facts.mul facts.preparedKey pa.1 pb.1 pa.2.1 pb.2.1 pa.2.2.1.1 pb.2.2.1.1
    pa.2.2.1.2 pb.2.2.1.2 pa.2.2.2 sz.1 sz.2.1 sz.2.2 hv pub.1

end VG.Proof.AesGcm.AArch64.Contiguous

namespace VG.Proof.AesGcm.AArch64.Contiguous
open VG VG.AArch64 VG.AArch64.Scrub VG.Impl.Scrub.AArch64 VG.Impl.AesGcm.AArch64.Contiguous
open VG.Impl.AesGcm.AArch64.Fn (own)
theorem boundedLeaf {v : GcmImpl} {g : GhashWithImpl} (facts : BackendFacts v g) (z : v.calls.ctr.scratch=0)
    (sat : ∃ s, (leafContract bounded).pre s) :
    VerifiedScrubbed target (scrubAll 752 0 own (Impl.AesGcm.AArch64.Contiguous.MediumDirect.frame v.calls.callees)) (leafContract bounded) 0 := by
  have zero : v.ctr.scratch=0 := v.ctr.scratch_eq.symm.trans z
  apply scrubLeaf (by decide) facts.mediumSide
  refine ⟨fun _ h => MediumDirect.frame_ok v zero facts.hash16 h.1 h.2.1 h.2.2.1.1 h.2.2.1.2 h.2.2.2
    (DirectGather.keepsV_of_gatherSide facts.mediumSide),ct_of ?_,sat⟩
  intro a b pa pb pub
  exact MediumDirect.frame_rel v zero facts.hash16 pa.1 pb.1 pa.2.1 pb.2.1 pa.2.2.1.1 pb.2.2.1.1
    pa.2.2.1.2 pb.2.2.1.2 pa.2.2.2 pb.2.2.2 pub.1

end VG.Proof.AesGcm.AArch64.Contiguous
