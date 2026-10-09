import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedHashTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedHashSetup
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentTiming

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)

/-- Loading the nonce does not make its value public; only the scratch
address contributes to this straight-line block's trace. -/
theorem hashSetup_tr {p : Params} {S : Nat} {P : State→State→Prop}
    (hP : ∀x y,P x y→LRel S (sgR p) (sgW p) x y) :
    RelCT isa P (.block [.ldr .x .x9 .x28 oKAP,.addImm .x .x9 .x9 (2*p.ℓ-1)])
      fun _ _=>True :=
  lrel_tr (hc:=.block []) hP rfl

/-- The complete commitment-plus-cache call has no data-dependent trace. -/
theorem hash_tr {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87)
    {S : Nat} (hS : S<2^64) :
    RelCT isa (LRel S (sgR p) (sgW p)) (Impl.MlDsa.AArch64.Sign.Cached.hash p)
      fun _ _=>True := by
  have hp3 : Ok3 p := by rcases hp with rfl|rfl <;> simp [Ok3]
  have hr : inB (sgB p) (sc oKAP) 8=true := by rcases hp with rfl|rfl <;> decide
  have ht := seqL (p:=p) (D:=S) (I:=fun _=>True) (J:=fun _=>True)
    (hashSetup_tr (fun _ _ h=>h.1))
    (fun s L _=>WP.mono (hashSetup_run hp3 s (L.inR hr)) fun t ⟨hk,_⟩=>
      ⟨⟨[],postB_of_keep hk.keep (by decide) (by rw [hk.mem]; exact Frame.refl _ _)⟩,trivial⟩)
    (hashReady_tr hp hS (fun _ _ h=>⟨h.1.lx,h.1.ly,h.1.regs,h.1.sp⟩))
  exact RelCT.mono ht (fun _ _ h=>⟨h,trivial,trivial⟩) (fun _ _ h=>h)

end VG.Proof.MlDsa.AArch64.Sign.Cached
