module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.PreparedFrame
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.ShortCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Record
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
  gather : Verified target (Impl.AesGcm.AArch64.DirectGather.framed v.calls) DirectGather.sharedGatherContract
  sizes : 768 ≤ v.calls.pwWn ∧ v.calls.pwWn ≤ 2560 ∧ v.calls.pwWn % 16 = 0
  scratch : v.ctr.scratch ≤ v.calls.pwWn-512
  general : scrubSide (generalFrame v.calls) (v.calls.pwWn+80) 0 own [] = true
  depth : 16*(Impl.AesGcm.AArch64.DirectGather.framed v.calls).aarch64Depth < 2^64
  prepared (f : Bool) : scrubSide (preparedFrame v.calls g.fn f) (v.calls.pwWn+32) 0 (preparedClear f (!v.calls.stitch)) [] = true
  vectors (f : Bool) : (withStackArgScratch (v.calls.pwWn+32) 3 (preparedBody v.callees g.fn f false)).allInstrs keepsV = true
  hash : DirectGather.HashEightWithOk
  stitch : VG.Proof.Gcm.AArch64.Stitch.Gh8Ok
  mul : VG.Proof.Gcm.AArch64.Pmull.MulKey

end VG.Proof.AesGcm.AArch64.Contiguous

/-! ## Correctness, trace equality and erasure of each public-length specialization.
All leaves read the plaintext from the source in the caller's initial state. -/

namespace VG.Proof.AesGcm.AArch64.Contiguous
open VG VG.AArch64 VG.AArch64.Scrub VG.Impl.Scrub.AArch64
open VG.Impl.AesGcm.AArch64.Contiguous
open VG.Impl.AesGcm.AArch64.Fn (own)

def leafContract (extra : State → Prop) : Contract isa where
  pre s := Caller s ∧ Prepared.Powers s ∧ extra s
  post := result
  pub a b := onePub 3 a b ∧ a.dit=b.dit

def standard (s : State) : Prop := (s.gpr .x3).toNat=12 ∧ (s.gpr .x5).toNat≤16
def prepared (fused : Bool) (s : State) : Prop := standard s ∧ (fused=true → 128 ≤ (stackArg s 0).toNat)
def short (s : State) : Prop := standard s ∧ (stackArg s 0).toNat ≤ 96

private theorem scrubLeaf {cl : Clear} {p : State → Prop} {code : Prog isa} {W : Nat}
    (sizes : 0<W ∧ W≤2640 ∧ W%16=0)
    (side : scrubSide code W 0 cl [] = true) (raw : Verified target code (leafContract p)) :
    VerifiedScrubbed target (scrubAll W 0 cl code) (leafContract p) 0 := by
  have hk : ScrubAllOk (leafContract p) W 0 := by
    refine ⟨fun s hs => Nat.le_trans sizes.2.1 hs.1.room,?_,fun _ _ hp => hp.1.2.2.2.2.2.2.2.2.1⟩
    intro s t u hs post mem _
    apply result_frame hs.1 sizes.2.1 post
    intro a ha
    exact mem a fun bad => ha _ (List.mem_singleton_self _) (by
      change (a-(s.sp-BitVec.ofNat 64 W)).toNat+1 ≤ W
      exact bad)
  obtain ⟨wf,kp,dit,rb⟩ := keeps_of_side side
  refine ⟨Verified.scrubAllOfV raw hk side,?_,fun ty _ h => by cases ty <;> cases h⟩
  simp only [scrubSide,Nat.ne_of_gt sizes.1,↓reduceIte,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at side
  refine noResidue_scrubAll wf kp raw ⟨sizes.1,by omega,sizes.2.2⟩ hk.sp side.1.1.1.1.1.2 dit ?_ rb
  intro _ _ _ n hn
  exact False.elim (List.not_mem_nil (of_decide_eq_true (List.all_eq_true.mp side.1.1.1.1.2 n hn)))

theorem generalLeaf {v : GcmImpl} {g : GhashWithImpl} (facts : BackendFacts v g) (sat : ∃ s, (leafContract (fun _ => True)).pre s) :
    VerifiedScrubbed target (scrubAll (v.calls.pwWn+80) 0 own (generalFrame v.calls))
      (leafContract (fun _ => True)) 0 := by
  have sz := facts.sizes
  have side := facts.general
  apply scrubLeaf (by omega) side
  refine ⟨fun _ h => general_ok v facts.gather h.1 (DirectGather.keepsV_of_gatherSide side) facts.depth,
    ct_of (fun _ _ pa pb pub => general_rel v facts.gather pa.1 pb.1 pub.1 pub.2),sat⟩

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
  refine ⟨fun _ h => Prepared.frame_ok v g f facts.stitch facts.mul h.1 h.2.1 h.2.2.1.1 h.2.2.1.2 h.2.2.2
    sz.1 sz.2.1 sz.2.2 hv (facts.vectors f),ct_of ?_,sat⟩
  intro a b pa pb pub
  exact Prepared.frame_rel v g f facts.stitch facts.mul pa.1 pb.1 pa.2.1 pb.2.1 pa.2.2.1.1 pb.2.2.1.1
    pa.2.2.1.2 pb.2.2.1.2 pa.2.2.2 sz.1 sz.2.1 sz.2.2 hv pub.1

end VG.Proof.AesGcm.AArch64.Contiguous
