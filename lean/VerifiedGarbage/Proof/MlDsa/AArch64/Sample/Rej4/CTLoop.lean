module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CTBase
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rel
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CTBase
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.Conv
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.MlKem.AArch64.Sample
meta import VerifiedGarbage.Proof.MlKem.AArch64.Sample
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Absorb
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbPair
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Env
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Init
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pad
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadMem
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadStore
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SeedFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Setup
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Tail
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Zero
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.MlKem.Mem16Bytes
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
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Absorb
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbPair
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbWord
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Env
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Init
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pad
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadMem
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadStore
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SeedFrame
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Setup
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Tail
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Zero
meta import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.MlKem.Mem16Bytes
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
open VG.Proof.MlDsa.AArch64.Sample (Rel2 relMem byte_zero)
open VG.Proof.MlDsa.Sample (polyR coeff_contains G_length)
open VG.Impl.MlDsa.AArch64.Sample (rnLoop)
open VG.Proof.MlKem.AArch64 (ptr_zero)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (oBuf)

def lrd (σ : State) (k : Nat) : List Region := [⟨bufP σ k,1008⟩]
def lwr (σ : State) (k : Nat) : List Region := [polyR (polyP σ k)]

theorem buf_pub {σ τ : State} (hq : r4K.pub σ τ) (k : Nat) : bufP σ k = bufP τ k := by
  unfold bufP at'
  rw [hq.2.2.1]

theorem poly_pub {σ τ : State} (hq : r4K.pub σ τ) (k : Nat) : polyP σ k = polyP τ k := by
  unfold polyP
  rw [hq.2.1]

theorem loop_ct {k : Nat} (hk : k < 4) :
    RelCT isa (Rel2 r4K.pre r4K.pub (fun σ => ZeroReady σ k)) rnLoop fun _ _ => True := by
  refine relMem (fun σ => lrd σ k) (fun σ => lwr σ k) [.x25,.x26]
    (fun σ τ _ _ hq => by simp only [lrd,lwr,buf_pub hq,poly_pub hq]; exact ⟨trivial,trivial⟩)
    (fun σ s hp h => ?_) (fun σ s hp h => ?_)
    (fun σ τ s t _ _ hq hs ht => ?_) (by taint_decide)
  · rw [h.ready.env.rd,h.ready.env.wr,hp.rd,hp.wr]
    refine ⟨Covers.of_sub (fun r hr => ?_),Covers.of_sub (fun r hr => ?_)⟩
    · simp only [lrd,lwr,List.mem_append,List.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact ⟨scrR σ,by simp,VG.Impl.MlDsa.AArch64.Sample.Rej4.oBuf+1008*k,rfl,
          by dsimp only [oBuf,scrR]; omega⟩
      · exact ⟨aR σ,by simp,1024*k,rfl,by dsimp only [aR,polyR]; omega⟩
    · rw [List.mem_singleton.mp hr]
      exact ⟨aR σ,by simp,1024*k,rfl,by dsimp only [aR,polyR]; omega⟩
  · have h := zero_lpre hp hk h
    obtain ⟨tr,u,he,_⟩ := VG.Proof.MlDsa.AArch64.Sample.RejNtt.loop_ok (G_length _ _)
      (s₀ := s.withRegions (lrd σ k) (lwr σ k))
      ⟨h.buf,fun j hj => VG.Proof.MlKem.AArch64.in_rd (VG.Proof.MlKem.AArch64.in_regions
        (List.mem_singleton_self _) (Offset.contains_base _ (by omega) (by omega))),
        fun i hi => VG.Proof.MlKem.AArch64.in_regions (List.mem_singleton_self _) (coeff_contains _ hi),
        h.disj,h.x25,h.x26⟩
    exact ⟨tr,u,he⟩
  · refine ⟨by rw [hs.ready.env.sp,ht.ready.env.sp,hq.2.2.2.1],fun r hr => ?_,fun x hx => ?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · rw [hs.x25,ht.x25]
        unfold at'
        rw [hq.2.2.1]
      · rw [hs.x26,ht.x26,poly_pub hq]
    · obtain ⟨r,hr,hc⟩ := hx
      simp only [lrd,lwr,List.mem_append,List.mem_singleton] at hr
      rcases hr with rfl | rfl
      · obtain ⟨j,hj,rfl⟩ := VG.Proof.MlKem.AArch64.Sample.at_off hc
        rw [hs.ready.out k hk j hj,buf_pub hq,ht.ready.out k hk j hj]
        exact congrArg (fun b : List Byte => b.getD j 0) (X_pub hq hk)
      · rw [byte_zero hs.zero hc,byte_zero ht.zero (by rw [← poly_pub hq]; exact hc)]
end VG.Proof.MlDsa.AArch64.Sample.Rej4
