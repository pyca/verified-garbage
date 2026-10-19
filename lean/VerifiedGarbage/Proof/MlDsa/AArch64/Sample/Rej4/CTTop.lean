module
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Top
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rel

import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CT
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.Conv
meta import Mathlib.Tactic.SplitIfs
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
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CTLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Env
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Init
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pad
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadMem
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadStore
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SeedFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Setup
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
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CTLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Env
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Init
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pad
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadMem
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadStore
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SeedFrame
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Setup
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
open VG.Proof.MlDsa.AArch64.Sample (Rel2 relStep relTaintStep vectorRelTaint)
open VG.Proof.MlKem.AArch64 (wp_movz wp_nil)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (sample epi rejNTT4With)

theorem start_parsed {σ s : State} (hp : Pre σ) (h : Ready σ s) :
    WP isa (.block [.movz .x .x27 1 0]) s (Parsed σ 0) := by
  refine wp_movz fun t ht et => wp_nil ⟨?_,?_,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  · exact h.polyStep hp (k := 0) (by decide) (by rw [ht.mem]; exact Frame.refl _ _)
      ht.rd ht.wr ht.sp (fun r hr => ht.get r (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide))
  · rw [et]; rfl

theorem parsed_ct {k : Nat} (hk : k < 4) : RelCT isa (Rel2 r4K.pre r4K.pub (fun σ => Parsed σ k))
    (sample k) (Rel2 r4K.pre r4K.pub (fun σ => Parsed σ (k+1))) :=
  relStep (fun _ _ hp h => parsed_step hp hk h)
    (RelCT.mono (sample_ct hk) (fun _ _ ⟨σ,τ,hp,hp',hq,h,h'⟩ =>
      ⟨σ,τ,hp,hp',hq,h.ready,h'.ready⟩) (fun _ _ _ => trivial))

theorem body_ct : RelCT isa (Rel2 r4K.pre r4K.pub Ready)
    (.seq (.block [.movz .x .x27 1 0])
      (.seq (sample 0) (.seq (sample 1) (.seq (sample 2) (.seq (sample 3) (.block epi))))))
    fun _ _ => True := by
  refine RelCT.seq (relTaintStep (J' := fun σ => Parsed σ 0) []
    (fun _ _ hp h => start_parsed hp h) (fun _ _ _ _ _ _ hq hs ht =>
      ⟨by rw [hs.env.sp,ht.env.sp,hq.2.2.2.1],by simp⟩) (by taint_decide)) ?_
  refine RelCT.seq (parsed_ct (by decide : 0 < 4)) ?_
  refine RelCT.seq (parsed_ct (by decide : 1 < 4)) ?_
  refine RelCT.seq (parsed_ct (by decide : 2 < 4)) ?_
  refine RelCT.seq (parsed_ct (by decide : 3 < 4)) ?_
  exact vectorRelTaint [.x19] (fun _ _ _ _ _ _ hq hs ht =>
    ⟨by rw [hs.ready.env.sp,ht.ready.env.sp,hq.2.2.2.1],fun r hr => by
      rw [List.mem_singleton.mp hr,hs.ready.env.x19,ht.ready.env.x19,hq.2.2.1]⟩) (by taint_decide)

theorem ct (sha3 : Bool) : ConstantTime isa r4K.pre r4K.pub (rejNTT4With sha3) := by
  refine RelCT.constantTime (Q := fun _ _ => True)
    (RelCT.mono (Q := fun _ _ => True) (P := Rel2 r4K.pre r4K.pub (fun σ s => s = σ)) ?_
      (fun s t h => ⟨s,t,h.1,h.2.1,h.2.2,rfl,rfl⟩) (fun _ _ _ => trivial))
  exact RelCT.seq init_ct (RelCT.seq (squeeze_ct sha3) body_ct)
end VG.Proof.MlDsa.AArch64.Sample.Rej4
