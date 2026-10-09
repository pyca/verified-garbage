import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallChecks

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64

abbrev SpongePublic : VectorTaint.T := VectorTaint.ofRegs [.x25,.x26,.x27,.x3,.x4]

/-- The public cursor returned by the first block is retained for a possible
second squeeze. This is a relational fact proved by the existing taint checker. -/
def SpongeCursor (c : Impl.Sha3.AArch64.Callee) : Prop :=
  RelCT isa (VectorTaint.Agree SpongePublic) (Impl.MlDsa.AArch64.Sample.spongeWith c 136 136)
    (fun s t => s.gpr .x0=t.gpr .x0)

 theorem sha3_spongeCursor : SpongeCursor Proof.Sha3.AArch64.Sha3.callee := by
  obtain ⟨hint,τ,hcheck,hpost,_⟩ := firstSponge SpongePublic (by decide)
  have hlo : VectorTaint.taint.le (VectorTaint.ofRegs [.x0]) τ=true :=
    Taint.Mono.le_R (A := VectorTaint.taint) (by decide) hpost
  intro s t ts tt u v hp hs ht
  obtain ⟨he,ha⟩ := Taint.check_sound hcheck hp hs ht
  have hh := VectorTaint.taint.le_sound hlo ha
  exact ⟨he,hh.1.2 .x0 (by decide)⟩
end VG.Proof.MlDsa.AArch64.Optimized.Ball
