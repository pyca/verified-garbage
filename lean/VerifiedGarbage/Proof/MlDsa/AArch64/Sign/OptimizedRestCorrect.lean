import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedRest
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Correct

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

/-- Once the matrix is sampled, the optimized phases establish the same
signMu success/failure contract as the original signer. -/
theorem positiveRest_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) {checks : Prog isa}
    (hchecks : ∀σ s t,PositiveIB p S σ t s → (s.gpr .x0).setWidth 32=1 →
      WP isa checks s fun u => PositiveEP p S σ t u ∨ PositiveEF p S σ t u)
    {σ s : State} (h : IM p S σ s) (ht : StaticRoots S s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.restWith keccak.callee P p checks) s (FS p S σ) := by
  have hA := expandA_max h.ok
  unfold Impl.MlDsa.AArch64.Sign.Optimized.restWith
  refine WP.seq (WP.mono (positiveInitialization_ok hP hp h ht) fun a ha => ?_)
  refine WP.seq (WP.mono (positiveSignLoop_ok hP hp (bChk_ok hp) hchecks ha) fun b hb => ?_)
  unfold ifOk
  refine ifOkElse_ok (fun hne => ?_) fun he => ?_
  · have h1 := x24_one hb.r01 hne
    obtain ⟨t,hlt,hrej,hsampled,hpass,hct,hz,hh⟩ := hb.pass h1
    have ready : AcceptedConversion p S σ (p.ℓ*t) (-(q:Int)+1) ((q:Int)-1) 0 b :=
      ⟨⟨⟨hb.k.d.im.st,hb.k.d.roots⟩,by intro j hj; omega,fun j _ hj => hz j hj,h1⟩,hct,hh⟩
    refine WP.mono (optimizedOutput_ok hP hp ready (by omega) (by omega) hpass)
      fun u ⟨hu,hbytes,hflag⟩ => ?_
    exact ⟨hu,.inr hflag,fun _ => by rw [hbytes]; exact signMu_max (paramsOk hp) hA hlt hrej hsampled hpass,
      fun h0 => absurd (h0.symm.trans hflag) (by decide)⟩
  · have h0 := x24_zero hb.r01 he
    exact WP.block_nil ⟨hb.k.d.im.st,.inl h0,fun h1 => absurd (h1.symm.trans h0) (by decide),
      fun _ => signMu_min_L hA (hb.fail h0)⟩

end VG.Proof.MlDsa.AArch64.Sign
