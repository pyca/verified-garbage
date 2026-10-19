module
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedLow
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLowState
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedDecodeTiming

import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedR0
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedR0
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZTiming
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.Conv
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowCallTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Batch
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotMemoryValues
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSliceComposition
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableConstants
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversalCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeccakMix
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Layout
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryOuterPass
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemorySchedule
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallee
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttOutVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductRepresentation
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorb
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorbWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentParse
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRestoreG
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowMath
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseMath
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableDecode
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Loop
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChallenge
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZ
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseC
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseDCT
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Chi
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.ChiWord
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Correction
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Cycle
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwLanes
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRounds
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Pair
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rho
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.RhoStep
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rotate
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rounds
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Row
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.SaveRow
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Batch
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotBank
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotMemoryValues
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveInit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRoots
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSliceComposition
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableConstants
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversalCorrect
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeccakMix
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Layout
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryOuterPass
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemorySchedule
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallee
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttOutVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductRepresentation
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorb
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorbWord
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskCall
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentParse
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRestoreG
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseInit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowMath
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowWord
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseMath
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZMemory
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableDecode
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalCorrect
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Loop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChallenge
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZ
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseC
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseDCT
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
meta import VerifiedGarbage.Proof.MlDsa.Pack.Stream
meta import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
meta import VerifiedGarbage.Proof.MlDsa.Verify.Mem
meta import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
meta import VerifiedGarbage.Proof.MlKem.AArch64.Shared
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Chi
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.ChiWord
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Correction
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Cycle
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwLanes
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRounds
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Pair
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rho
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.RhoStep
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rotate
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Round
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rounds
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Row
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.SaveRow
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Round
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
meta import VerifiedGarbage.Proof.Sha3.Arith

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc seqR)
open VG.Proof.MlDsa.AArch64.Optimized

private theorem inB_bases {p : Params} {a : Ptr} {n : Nat} (h : inB (sgB p) a n=true) :
    a.1∈bases := by
  obtain ⟨len,hm,_⟩ := inB_spec h
  exact sgB_bases p (a.1,len) hm

private theorem inB_argOk {p : Params} {a : Ptr} {n : Nat} (h : inB (sgB p) a n=true) :
    (VG.Impl.MlDsa.AArch64.Call.Arg.ptr a).Ok := ptr_ok (bases_kept _ (inB_bases h))

/-- Trace equality uses only public layout and artifact addresses; all r0 checks
run before the signer can branch on the accumulated rejection result. -/
theorem optimizedR0_trace {p : Params} {S : Nat} (hp : Ok3 p) {t r : Nat} (hr : r<p.k)
    {E : State → State → Prop} :
    RelCT isa (RootRS p S E (PositiveIR p S · t r))
      (Impl.MlDsa.AArch64.Sign.Optimized.r0R p r) fun _ _=>True := by
  have hc := optimizedR0Chk_ok hp r hr
  simp only [optimizedR0Chk,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨cl,hgb⟩,rp⟩,wp⟩,_⟩,_⟩,_⟩,_⟩,hwp⟩ := hc
  simp only [subLowNormChk,Bool.and_eq_true] at cl
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hwr,hcr⟩,hlr⟩,hww⟩,hwl⟩,hwc⟩,hwo⟩,hco⟩,_⟩ := cl
  let I := fun tab s => (∃σ,PositiveIR p S σ t r s) ∧ s.syms "VG_MLDSA_INV_FOLDED"=tab
  let J := fun s => (∃σ,PositiveIRb p S σ t r s) ∧ RawReduced s.mem (pa s t1P)
  have ht (tab : Addr) : RelCT isa (fun x y=>LRel S (sgR p) (sgW p) x y ∧ I tab x ∧ I tab y)
      (Impl.MlDsa.AArch64.Sign.Optimized.r0R p r) fun _ _=>True := by
    unfold Impl.MlDsa.AArch64.Sign.Optimized.r0R
    refine seqL (I := I tab) (J := J) ?_ ?_ (seqL (J := fun _=>True) ?_ ?_ ?_)
    · apply responseProduct_tr (responseProductChk_r0 hp r hr)
      intro x y ⟨L,⟨⟨σ,hx⟩,ex⟩,⟨⟨τ,hy⟩,ey⟩⟩
      exact ⟨L,⟨σ,hx.1.b.l.st,hx.1.b.l.k.d.roots⟩,⟨τ,hy.1.b.l.st,hy.1.b.l.k.d.roots⟩,
        hx.1.b.c.bound,(hx.1.b.l.k.d.s2 r hr).bound,
        hy.1.b.c.bound,(hy.1.b.l.k.d.s2 r hr).bound,ex.trans ey.symm⟩
    · rintro x L ⟨⟨σ,hx⟩,_⟩
      refine WP.mono_syms (responseProduct_ok ⟨hx.1.b.l.st,hx.1.b.l.k.d.roots⟩
        (responseProductChk_r0 hp r hr) hx.1.b.c (hx.1.b.l.k.d.s2 r hr)) fun a ⟨hpa,_,hprod⟩ hsa => ?_
      refine ⟨⟨_,hpa⟩,⟨σ,hx.1.step hpa hsa rp wp hwp⟩,?_⟩
      rw [hpa.pa (by decide)]
      exact hprod.1
    · apply Response.subLowNormAt_tr (S := S) (inB_argOk hwr) (inB_argOk hcr) (inB_argOk hlr)
      intro x y ⟨L,⟨⟨σ,hx⟩,rx⟩,⟨⟨τ,hy⟩,ry⟩⟩
      have fx : Reduced x.mem (pa x (wP p r)) := by
        have h := (hx.w 0 (by omega)).1
        simpa only [Nat.add_zero] using h
      have fy : Reduced y.mem (pa y (wP p r)) := by
        have h := (hy.w 0 (by omega)).1
        simpa only [Nat.add_zero] using h
      exact ⟨subLowNormReady_layout L.lx hwr hcr hlr hww hwl hwc hwo hco fx rx hgb.1 hgb.2.1 hgb.2.2,
        subLowNormReady_layout L.ly hwr hcr hlr hww hwl hwc hwo hco fy ry hgb.1 hgb.2.1 hgb.2.2,
        L.pa (inB_bases hwr),L.pa (inB_bases hcr),L.pa (inB_bases hlr),L.sp⟩
    · rintro x L ⟨⟨σ,hx⟩,rx⟩
      have fx : Reduced x.mem (pa x (wP p r)) := by
        have h := (hx.w 0 (by omega)).1
        simpa only [Nat.add_zero] using h
      exact WP.mono (subLowNormAt_layout L hwr hcr hlr
        (subLowNormReady_layout L hwr hcr hlr hww hwl hwc hwo hco fx rx hgb.1 hgb.2.1 hgb.2.2))
        fun _ h=>⟨⟨_,h.1⟩,trivial⟩
    · exact lrel_tr (fun _ _ h=>h.1) (by taint_decide)
  apply RelCT.mono (RelCT.exists_ ht) ?_ (fun _ _ h=>h)
  intro x y h
  have L := h.1.lrel (fun _ _ h=>h.1.b.l.st)
  obtain ⟨σ,τ,_,_,_,_,hx,hy⟩ := h.1
  exact ⟨x.syms "VG_MLDSA_INV_FOLDED",L,⟨⟨σ,hx⟩,rfl⟩,⟨⟨τ,hy⟩,h.2.2.symm⟩⟩

theorem optimizedR0_tr {p : Params} {S : Nat} (hp : Ok3 p) {t r : Nat} (hr : r<p.k)
    {E : State → State → Prop} :
    RelCT isa (RootRS p S E (PositiveIR p S · t r))
      (Impl.MlDsa.AArch64.Sign.Optimized.r0R p r) (RootRS p S E (PositiveIR p S · t (r+1))) :=
  liftRootR (fun _ _ _ h=>optimizedR0_ok hp hr h) (optimizedR0_trace hp hr)

theorem optimizedR0_vector_tr {p : Params} {S : Nat} (hp : Ok3 p) {t : Nat}
    {E : State → State → Prop} :
    RelCT isa (RootRS p S E (PositiveIR p S · t 0))
      (seqR (Impl.MlDsa.AArch64.Sign.Optimized.r0R p) 0 p.k)
      (RootRS p S E (PositiveIR p S · t p.k)) := by
  simpa only [Nat.zero_add] using seqR_tr (Q := fun r=>RootRS p S E (PositiveIR p S · t r)) p.k 0
    (fun r _ hr=>optimizedR0_tr hp (by omega))

end VG.Proof.MlDsa.AArch64.Sign
