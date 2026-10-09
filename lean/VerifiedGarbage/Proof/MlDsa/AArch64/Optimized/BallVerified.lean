import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (H)
open VG.Spec.Sha3 (bytesAt)

theorem sampleInBall_verifiedWith (v : Proof.Sha3.AArch64.Permutation) (hc : SpongeCursor v.callee) (ht : PrefixTiming v.callee) : Verified AArch64.target (Impl.MlDsa.AArch64.Optimized.Ball.codeWith v.callee)
    (Spec.MlDsa.sampleInBallContract AArch64.abi 16) :=
  Verified.of_correct (correctWith v) (ctWith v hc ht)
    { pre := by sig_implies_pre [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, sbK,
        AArch64.abi, AArch64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, sbK, AArch64.abi,
          AArch64.argRegs]
        dsimp only [sbK] at h
        obtain ⟨hr, hp⟩ := h
        by_cases hf : (ballFold (tauOf s) (H (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) 272)).2 = 256
        · rw [ifT hf] at hr
          obtain ⟨hred, hpoly⟩ := hp hf
          exact ⟨fun _ => hred, .inl ⟨hr, { Spec.MlDsa.minBounds with ball := 272 }, by
            show Option.map _ (Spec.MlDsa.sampleInBall _ 272 _) = _
            rw [sampleInBall_some _ (by decide) hf, hpoly]; rfl⟩⟩
        · rw [ifF hf] at hr
          exact ⟨fun h1 => absurd (hr.symm.trans h1) (by decide),
            .inr ⟨hr, by
              show Option.map _ (Spec.MlDsa.sampleInBall _ Spec.MlDsa.minBounds.ball _) = none
              rw [sampleInBall_none (B := 272) _ (by decide) (by decide) hf]; rfl⟩⟩
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, sbK, AArch64.abi,
          AArch64.argRegs] at h
        obtain ⟨hsp, hb, hx0, hx1, hx2, hx3, hx4⟩ := h
        exact ⟨hx0, hx1, hx2, hx3, hx4, hsp, VG.Proof.MlKem.map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, sbK,
        AArch64.abi, AArch64.argRegs] [sbSat] using sbSat }

/-- The optimized sampler has the unchanged public SampleInBall contract. -/
theorem sampleInBall_verified : Verified AArch64.target
    (Impl.MlDsa.AArch64.Optimized.Ball.codeWith Proof.Sha3.AArch64.Sha3.callee)
    (Spec.MlDsa.sampleInBallContract AArch64.abi 16) :=
  sampleInBall_verifiedWith Proof.Sha3.AArch64.Sha3.backend sha3_spongeCursor sha3_prefixTiming
end VG.Proof.MlDsa.AArch64.Optimized.Ball
