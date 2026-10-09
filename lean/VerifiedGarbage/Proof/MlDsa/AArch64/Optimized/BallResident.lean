import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallVerified
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.ResidentBackend
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.BallDispatch

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Sha3.ResidentBackend

taint_summary residentFirstSponge : VectorTaint.taint SpongePublic
  (Impl.MlDsa.AArch64.Sample.spongeWith callee 136 136)
  using RSums.absorb RSums.pad RSums.squeeze

theorem resident_spongeCursor : SpongeCursor callee := by
  obtain ⟨hint,τ,hcheck,hpost,_⟩ := residentFirstSponge SpongePublic (by decide)
  have hlo : VectorTaint.taint.le (VectorTaint.ofRegs [.x0]) τ=true :=
    Taint.Mono.le_R (A := VectorTaint.taint) (by decide) hpost
  intro s t ts tt u v hp hs ht
  obtain ⟨he,ha⟩ := Taint.check_sound hcheck hp hs ht
  have hh := VectorTaint.taint.le_sound hlo ha
  exact ⟨he,hh.1.2 .x0 (by decide)⟩

theorem resident_prefixTiming : PrefixTiming callee := by
  have hh : ∃hint,(VectorTaint.taint.check (VectorTaint.ofRegs [.x0,.x25]) (secondPrefix callee) hint).isSome=true := by sponge_taint_decide RSums
  obtain ⟨hint,hh⟩ := hh
  exact RelCT.taint (A := VectorTaint.taint) _ (fun _ _ h => h) hh

theorem resident_verified : Verified AArch64.target
    (Impl.MlDsa.AArch64.Optimized.Ball.codeWith Impl.MlDsa.AArch64.Optimized.Ball.residentCallee)
    (Spec.MlDsa.sampleInBallContract AArch64.abi 16) :=
  sampleInBall_verifiedWith backend resident_spongeCursor resident_prefixTiming
end VG.Proof.MlDsa.AArch64.Optimized.Ball
