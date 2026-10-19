module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopEndTiming
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopEndTiming
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.Conv
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopInit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChecksTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChecksTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentTiming
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
import VerifiedGarbage.Proof.Framework.AArch64.Syms
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
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Batch
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CanonicalizeVerified
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
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFinish
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseMath
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableDecode
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Loop
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.MaskPairTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedOutputPack
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCTBase
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseDCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseKCT
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
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
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
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Batch
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CanonicalizeVerified
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
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFinish
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseInit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseMath
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZMemory
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableDecode
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalCorrect
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Loop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.MaskPairTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopCorrect
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedOutputPack
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCTBase
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseDCT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseKCT
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
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Spec.MlDsa
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

/-- Timing of the full rejection-check phase, including the public success branch. -/
def PositiveChecksCT (p : Params) (D : Nat) (checks : Prog isa) : Prop :=
  ∀t,t<814 → RelCT isa
    (RootRS p D (LeakEq p t) fun σ s=>PositiveIB p D σ t s ∧ (s.gpr .x0).setWidth 32=1)
    checks (RootRS p D (LeakEq p t) fun σ s=>PositiveEP p D σ t s ∨ PositiveEF p D σ t s)

theorem positiveIter_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params}
    (h3 : Ok3 p) {checks : Prog isa} (hchecks : PositiveChecksCT p D checks)
    {t : Nat} (ht : t<814) :
    RelCT isa (RootRS p D (LeakEq p t) (PositiveIL p D · t))
      (Impl.MlDsa.AArch64.Sign.Optimized.iterWith keccak.callee P p checks) (PositiveIX p D t) := by
  have hp := paramsOk h3
  have hc2 := bChk_ok h3
  have hc2' := hc2
  simp only [bChk,Bool.and_eq_true,decide_eq_true_eq] at hc2'
  obtain ⟨⟨⟨c1,_⟩,_⟩,hbp⟩ := hc2'
  unfold Impl.MlDsa.AArch64.Sign.Optimized.iterWith
  refine RelCT.seq (positiveCommit_tr hP h3) ?_
  refine RelCT.seq (R := fun x y=>RootRS p D (LeakEq p t) (PositiveIB p D · t) x y ∧
    (x.gpr .x0).setWidth 32=(y.gpr .x0).setWidth 32) ?_ ?_
  · refine RelCT.mono (liftRootQ (G := fun _ _=>True) (J := fun σ s=>PositiveIB p D σ t s) (F := fun _ _=>True)
      (fun _ _ _ h=>WP.mono (positiveBall_ok hP h3 hc2 h) fun _ h=>⟨h,trivial⟩)
      (RelCT.mono (ballCall_tr hP hbp c1) (fun x y ⟨h,_⟩=>⟨h.1.lrel (fun _ _ h=>h.c.masks.l.st),by
        obtain ⟨σ,τ,_,_,_,he,hx,hy⟩ := h.1
        rw [hx.ct,hy.ct]; exact leq_ct he ht⟩) (fun _ _ h=>h))
      (fun σ τ x y x' y' ps pt pub he _ _ _ jx jy _ _ eq roots=>
        ⟨⟨⟨σ,τ,ps,pt,pub,he,jx,jy⟩,roots⟩,eq⟩))
      (fun _ _ h=>⟨h,trivial⟩) (fun _ _ h=>h)
  refine RelCT.seq (R := fun x y=>
      (RootRS p D (LeakEq p t) (fun σ s=>PositiveEP p D σ t s ∨ PositiveEF p D σ t s) x y ∧ True) ∨
      (RootRS p D (LeakEq p t) (PositiveEB p D · t) x y ∧ True))
    (RelCT.ite ?_ ?_ ?_) (relOr (positiveEndPF_tr h3 hp (lChk_ok h3)) (positiveEndB_tr h3 hp (lChk_ok h3)))
  · rintro x y ⟨_,he⟩; rw [eval_w0,eval_w0,he]
  · refine RelCT.mono (hchecks t ht) ?_ (fun _ _ h=>.inl ⟨h,trivial⟩)
    rintro x y ⟨⟨⟨⟨σ,τ,ps,pt,pub,he,hx,hy⟩,roots⟩,eq⟩,hb⟩
    have h1 := x0_one hx.r01 hb
    exact ⟨⟨σ,τ,ps,pt,pub,he,⟨hx,h1⟩,⟨hy,eq.symm.trans h1⟩⟩,roots⟩
  · refine RelCT.mono (positiveBallFailure_tr h3 (lChk_ok h3)) ?_ (fun _ _ h=>.inr ⟨h,trivial⟩)
    rintro x y ⟨⟨⟨⟨σ,τ,ps,pt,pub,he,hx,hy⟩,roots⟩,eq⟩,hb⟩
    have h0 := x0_zero hb
    exact ⟨⟨σ,τ,ps,pt,pub,he,⟨hx,h0⟩,⟨hy,eq.symm.trans h0⟩⟩,roots⟩

/-- The optimized loop retains the existing bounded-iteration leakage policy. -/
theorem positiveSignLoop_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params}
    (h3 : Ok3 p) {checks : Prog isa} (hchecks : PositiveChecksCT p D checks) :
    RelCT isa (RootRS p D (LeakEq p 0) (PositiveIK p D))
      (Impl.MlDsa.AArch64.Sign.Optimized.signLoopWith keccak.callee P p checks) (PositiveOX p D) := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.signLoopWith
  refine RelCT.seq (liftRootT (J := fun σ s=>PositiveIL p D σ 0 s) (fun _ _ h=>⟨h.d.im.st,h.d.roots⟩)
    (fun _ _ _ h=>positiveLoopInit_ok (lChk_ok h3) h)
    (lrel_tr (fun _ _ h=>h.1) (by taint_decide))) ?_
  refine RelCT.mono (RelCT.loop (M := isa)
    (fun n x y=>∃t,n=814-t ∧ RootRS p D (LeakEq p t) (PositiveIL p D · t) x y)
    (fun n=>?_) 814) (fun _ _ h=>⟨0,rfl,h⟩) (fun _ _ h=>h)
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨t,hn,hr⟩ e₁ e₂
  have ht : t<814 := by obtain ⟨_,_,_,_,_,_,i₁,_⟩ := hr.1; exact i₁.t_lt
  obtain ⟨htr,hz,hc,ho⟩ := positiveIter_tr hP h3 hchecks ht _ _ _ _ _ _ hr e₁ e₂
  exact ⟨htr,by rw [eval_x9,eval_x9,hz],fun h=>ho (x9_zero h),
    fun h=>⟨814-(t+1),by omega,t+1,rfl,hc (x9_ne h)⟩⟩

end VG.Proof.MlDsa.AArch64.Sign
