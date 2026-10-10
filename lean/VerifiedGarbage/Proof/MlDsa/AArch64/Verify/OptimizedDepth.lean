import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inst
import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.OptimizedTop
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedSamplesDepth
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallee
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSingleCall

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Message

/-- The selected arithmetic kernels have no nested stack frame; only the
existing sponge calls need the 16-byte stack reservation. -/
theorem verify_dle (v : Proof.Sha3.AArch64.Permutation) {P : Prims}
    (hP : PrimsOk P 16) (p : Params) :
    DLe 1 (Impl.MlDsa.AArch64.Verify.Optimized.verifyWith v.callee P p) := by
  obtain ⟨ha,hpad,hs⟩ := keccak_dle v
  have hh := DLe.of_fd hP.hintUnpack.fd
  have hu := DLe.of_fd hP.bitUnpack.fd
  have ht := DLe.of_fd hP.unpackT1.fd
  have hnorm := DLe.of_fd hP.normLt.fd
  have hsample := DLe.of_fd (OptimizedSamples.samples_depth hP p)
  have hn := DLe.of_fd (VG.Proof.MlDsa.AArch64.Optimized.positiveNtt_callee 16).fd
  have hi := DLe.of_fd (VG.Proof.MlDsa.AArch64.Optimized.Inverse.inverseSingle_callee 16).fd
  have hd : DLe 1 (Impl.MlDsa.AArch64.Optimized.MontDot.dot p.ℓ) := by
    unfold Impl.MlDsa.AArch64.Optimized.MontDot.dot
    dle_tac
  have hm : DLe 1 Impl.MlDsa.AArch64.Optimized.MontProduct.code := by
    unfold Impl.MlDsa.AArch64.Optimized.MontProduct.code
    dle_tac
  have hsub : DLe 1 (Impl.MlDsa.AArch64.Optimized.AddSub.code true) := by
    unfold Impl.MlDsa.AArch64.Optimized.AddSub.code
    dle_tac
  have hpack : DLe 1 Impl.MlDsa.AArch64.Optimized.UseHintPack.prog := by
    unfold Impl.MlDsa.AArch64.Optimized.UseHintPack.prog
      Impl.MlDsa.AArch64.Round.zext Impl.MlDsa.AArch64.Round.onGamma
      Impl.MlDsa.AArch64.Optimized.UseHintPack.code
    dle_tac
  unfold Impl.MlDsa.AArch64.Verify.Optimized.verifyWith
    Impl.MlDsa.AArch64.Verify.Optimized.bodyWith
    Impl.MlDsa.AArch64.Verify.Optimized.computeWith
  repeat' (first
    | with_reducible assumption
    | (apply DLe.call; with_reducible assumption)
    | apply DLe.seq
    | apply DLe.ite
    | apply DLe.loop
    | (apply DLe.seqR; intro)
    | apply DLe.block)

/-- Every standard optimized raw verifier fits the existing stack budget,
for either verified Keccak permutation. -/
theorem verifyWith_dle (v : Proof.Sha3.AArch64.Permutation) (p : Params) :
    DLe 1 (Impl.MlDsa.AArch64.Verify.Optimized.verifyWith v.callee (primsWith v.callee) p) :=
  verify_dle v (KeyGen.prims_okWith (keccak:=v)) p

end VG.Proof.MlDsa.AArch64.Verify.Optimized
