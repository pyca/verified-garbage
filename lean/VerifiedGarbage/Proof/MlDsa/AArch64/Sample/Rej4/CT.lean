module

import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CTLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CTLoop
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Top
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rel
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Lit
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.Conv
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Squeeze
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Squeeze
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Setup
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Setup
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Init
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Init
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Sponge
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Sponge
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Absorb
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbPair
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Advance
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Env
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pad
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadMem
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadStore
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SeedFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqAdvance
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqPair
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Tail
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Zero
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Sha3.AArch64.Call
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Chi
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.ChiWord
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Correction
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Cycle
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
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Absorb
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbPair
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbWord
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Advance
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Env
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pad
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadMem
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadStore
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SeedFrame
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqAdvance
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqFrame
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqPair
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Tail
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Zero
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
meta import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.Sha3.AArch64.Call
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Chi
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.ChiWord
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Correction
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Cycle
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
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
meta import VerifiedGarbage.TCB.Axioms

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Sample (Rel2 relStep relTaintStep relTaint vectorRelTaintStep)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (sample epi init setup squeezeStepWith rejNTT4With)
open VG.Impl.MlDsa.AArch64.Sample (rnLoop retZ zeroPoly)

theorem sample_ctFor {k : Nat} (hk : k < 4) {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (hcheck : (taint.check (Taint.ofRegs [.x19,.x21])
      (.block ([.addImm .x .x25 .x19 (1008*k),.addImm .x .x26 .x21 (1024*k)] : List Instr)) hint).isSome = true) :
    RelCT isa (Rel2 r4K.pre r4K.pub Ready) (sample k) fun _ _ => True := by
  unfold sample
  refine RelCT.seq (relTaintStep (J' := fun σ => ArgReady σ k) [.x19,.x21]
    (fun _ _ hp h => args_ready hk hp h) (fun σ τ s t _ _ hq hs ht => ?_) hcheck) ?_
  · refine ⟨by rw [hs.env.sp,ht.env.sp,hq.2.2.2.1],fun r hr => ?_⟩
    rcases mem2 hr with rfl | rfl
    · rw [hs.env.x19,ht.env.x19,hq.2.2.1]
    · rw [hs.env.x21,ht.env.x21,hq.2.1]
  refine RelCT.seq (relTaintStep (J' := fun σ => ZeroReady σ k) [.x26]
    (fun _ _ hp h => zero_ready hk hp h) (fun σ τ s t _ _ hq hs ht =>
      ⟨by rw [hs.ready.env.sp,ht.ready.env.sp,hq.2.2.2.1],fun r hr => by
        rw [List.mem_singleton.mp hr,hs.x26,ht.x26,poly_pub hq]⟩) (by taint_decide)) ?_
  refine RelCT.seq (relStep (J' := Ready) (fun _ _ hp h => loop_ready hp hk h) (loop_ct hk)) ?_
  exact relTaint [] (fun _ _ _ _ _ _ hq hs ht =>
    ⟨by rw [hs.env.sp,ht.env.sp,hq.2.2.2.1],by simp⟩) (by taint_decide)

theorem sample_ct {k : Nat} (hk : k < 4) :
    RelCT isa (Rel2 r4K.pre r4K.pub Ready) (sample k) fun _ _ => True := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
    exact sample_ctFor (by decide) (by taint_decide)

theorem init_ct : RelCT isa (Rel2 r4K.pre r4K.pub (fun σ s => s = σ))
    (.block (init++setup)) (Rel2 r4K.pre r4K.pub (fun σ => Phase σ 0 0)) := by
  refine vectorRelTaintStep [.x0,.x1,.x2] (fun σ s hp hs => ?_)
    (fun _ _ _ _ _ _ hq hs ht => ?_) (by taint_decide)
  · subst s
    rw [WP.block_append_iff]
    exact WP.mono (init_ok hp) fun _ ⟨he,h0,h1⟩ => setup_ok he h0 h1
  · subst hs ht
    exact ⟨hq.2.2.2.1,fun r hr => by
      rcases mem3 hr with rfl | rfl | rfl
      · exact hq.1
      · exact hq.2.1
      · exact hq.2.2.1⟩

theorem squeeze_ctFor (sha3 : Bool) {hint : VG.Taint.Hint VectorTaint.T}
    (hcheck : (VectorTaint.taint.check (VectorTaint.ofRegs [.x19,.x22,.x23,.x24,.x25,.x26,.x27,.x28])
      (.loop (squeezeStepWith sha3) (.nonzero .x .x28)) hint).isSome = true) : RelCT isa (Rel2 r4K.pre r4K.pub (fun σ => Phase σ 0 0))
    (.loop (squeezeStepWith sha3) (.nonzero .x .x28)) (Rel2 r4K.pre r4K.pub Ready) := by
  refine vectorRelTaintStep (hc := hint) [.x19,.x22,.x23,.x24,.x25,.x26,.x27,.x28]
    (fun _ _ hp h => WP.mono (squeeze_ok sha3 hp h) fun _ ht =>
      ⟨ht.env,fun k hk j hj => ht.out k hk j (by simpa using hj)⟩)
    (fun σ τ s t _ _ hq hs ht => ?_) ?_
  · refine ⟨by rw [hs.env.sp,ht.env.sp,hq.2.2.2.1],fun r hr => ?_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hs.env.x19,ht.env.x19,hq.2.2.1]
    · rw [hs.x22,ht.x22]; unfold stateP at'; rw [hq.2.2.1]
    · rw [hs.x23,ht.x23]; unfold stateP at'; rw [hq.2.2.1]
    · change s.gpr (bReg 0) = t.gpr (bReg 0)
      rw [hs.ptrs 0 (by decide),ht.ptrs 0 (by decide)]; unfold bufAt at'; rw [hq.2.2.1]
    · change s.gpr (bReg 1) = t.gpr (bReg 1)
      rw [hs.ptrs 1 (by decide),ht.ptrs 1 (by decide)]; unfold bufAt at'; rw [hq.2.2.1]
    · change s.gpr (bReg 2) = t.gpr (bReg 2)
      rw [hs.ptrs 2 (by decide),ht.ptrs 2 (by decide)]; unfold bufAt at'; rw [hq.2.2.1]
    · change s.gpr (bReg 3) = t.gpr (bReg 3)
      rw [hs.ptrs 3 (by decide),ht.ptrs 3 (by decide)]; unfold bufAt at'; rw [hq.2.2.1]
    · exact BitVec.eq_of_toNat_eq (hs.count.trans ht.count.symm)
  · exact hcheck
theorem squeeze_ct (sha3 : Bool) : RelCT isa (Rel2 r4K.pre r4K.pub (fun σ => Phase σ 0 0))
    (.loop (squeezeStepWith sha3) (.nonzero .x .x28)) (Rel2 r4K.pre r4K.pub Ready) := by
  cases sha3 <;> exact squeeze_ctFor _ (by taint_decide)
end VG.Proof.MlDsa.AArch64.Sample.Rej4
