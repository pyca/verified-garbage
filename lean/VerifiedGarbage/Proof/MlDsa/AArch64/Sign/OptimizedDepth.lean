import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedRest
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedChecks

namespace VG.Proof.MlDsa.AArch64.Message
open VG VG.AArch64

section
variable (c : Impl.Sha3.AArch64.Callee) (P : Impl.MlDsa.AArch64.Sign.Prims) (p : Spec.MlDsa.Params)
    (ha : DLe 1 (Impl.Sha3.AArch64.Stream.absorbWith c)) (hp : DLe 1 (Impl.Sha3.AArch64.Stream.padWith c))
    (hs : DLe 1 (Impl.Sha3.AArch64.Stream.squeezeWith c))
    (h1 : DLe 1 P.ntt) (h2 : DLe 1 P.invNtt) (h3 : DLe 1 P.mul) (h4 : DLe 1 P.mulAdd) (h5 : DLe 1 P.add)
    (h6 : DLe 1 P.sub) (h7 : DLe 1 P.rejNTT) (h8 : DLe 1 P.expandMask) (h9 : DLe 1 P.ball)
    (h10 : DLe 1 P.highBits) (h11 : DLe 1 P.lowBits) (h12 : DLe 1 P.normLt) (h13 : DLe 1 P.makeHint)
    (h14 : DLe 1 P.simpleBitPack) (h15 : DLe 1 P.bitPack) (h16 : DLe 1 P.bitUnpack) (h17 : DLe 1 P.hintBitPack) (h18 : DLe 1 P.rej4)
    (h19 : DLe 1 (P.highPack p.γ₂)) (h20 : DLe 1 P.expandMaskPair)
    (hn : DLe 1 Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt)
    (hno : DLe 1 Impl.MlDsa.AArch64.Optimized.Ntt.outNtt)
    (hdot : DLe 1 (Impl.MlDsa.AArch64.Optimized.DotInverse.staticCode p.ℓ))
    (hchecks : DLe 1 (Impl.MlDsa.AArch64.Sign.Optimized.checks p))
    (hcanon : DLe 1 Impl.MlDsa.AArch64.Optimized.Response.canonicalize)
include ha hp hs h7 h8 h9 h15 h16 h17 h18 h19 h20 hn hno hdot hchecks hcanon in
theorem optimizedSign_dle : DLe 1 (Impl.MlDsa.AArch64.Sign.Optimized.signWith c P p
    (Impl.MlDsa.AArch64.Sign.Optimized.checks p)) := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.signWith
  dle_tac
  all_goals unfold Impl.MlDsa.AArch64.Sign.Optimized.masks
  all_goals split <;> dle_tac
end


theorem optimizedChecks_dle (p : Spec.MlDsa.Params) :
    DLe 1 (Impl.MlDsa.AArch64.Sign.Optimized.checks p) := by
  have hn : DLe 1 Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt := ⟨by decide +kernel⟩
  have hm : DLe 1 (Impl.MlDsa.AArch64.Optimized.MultiplyInverse.staticCode true) := ⟨by decide +kernel⟩
  have hz : DLe 1 Impl.MlDsa.AArch64.Optimized.Response.addNorm := ⟨by decide +kernel⟩
  have hl : DLe 1 Impl.MlDsa.AArch64.Optimized.Response.subLowNorm := ⟨by decide +kernel⟩
  have hh : DLe 1 Impl.MlDsa.AArch64.Optimized.Response.hintNorm := ⟨by decide +kernel⟩
  unfold Impl.MlDsa.AArch64.Sign.Optimized.checks
  dle_tac

theorem optimizedSignWith_dle (v : Proof.Sha3.AArch64.Permutation)
    {p : Spec.MlDsa.Params} (hp3 : Proof.MlDsa.AArch64.Sign.Ok3 p) :
    DLe 1 (Impl.MlDsa.AArch64.Sign.Optimized.signWith v.callee (Sign.primsWith v.callee) p
      (Impl.MlDsa.AArch64.Sign.Optimized.checks p)) := by
  have C := Sign.prims_okWith (keccak := v)
  obtain ⟨ha,hp,hs⟩ := keccak_dle v
  apply optimizedSign_dle _ _ p ha hp hs (.of_fd C.rejNTT.fd) (.of_fd C.expandMask.fd)
    (.of_fd C.ball.fd) (.of_fd C.bitPack.fd) (.of_fd C.bitUnpack.fd)
    (.of_fd C.hintBitPack.fd) (.of_fd C.rej4.fd)
  · dsimp only [Sign.primsWith,Impl.MlDsa.AArch64.Optimized.HighPack.code]; dle_tac
  · exact .of_fd C.expandMaskPair.fd
  · exact ⟨by decide +kernel⟩
  · exact ⟨by decide +kernel⟩
  · rcases hp3 with rfl|rfl|rfl <;> exact ⟨by decide +kernel⟩
  · exact optimizedChecks_dle p
  · exact ⟨by decide +kernel⟩

end VG.Proof.MlDsa.AArch64.Message
