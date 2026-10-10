import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Inst
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.DepthBase

/-!
# ML-DSA on AArch64: how deep the frames of verification nest

Untrusted: everything here is checked by Lean. As `Depth.lean` for signing:
frames nest at most once in `vg_mldsa*_verify`, with any implementation of
the Keccak permutation (`verify_dle`, `verifyWith_dle`).
-/

namespace VG.Proof.MlDsa.AArch64.Message
open VG VG.AArch64

section
variable (c : Impl.Sha3.AArch64.Callee) (P : Impl.MlDsa.AArch64.KeyGen.Prims) (p : Spec.MlDsa.Params)
    (ha : DLe 1 (Impl.Sha3.AArch64.Stream.absorbWith c)) (hp : DLe 1 (Impl.Sha3.AArch64.Stream.padWith c))
    (hs : DLe 1 (Impl.Sha3.AArch64.Stream.squeezeWith c))
    (h1 : DLe 1 P.ntt) (h2 : DLe 1 P.invNtt) (h3 : DLe 1 P.mul) (h4 : DLe 1 P.mulAdd)
    (h6 : DLe 1 P.sub) (h7 : DLe 1 P.rejNtt) (h9 : DLe 1 P.ball)
    (h11 : DLe 1 P.useHint) (h12 : DLe 1 P.normLt) (h13 : DLe 1 P.simpleBitPack) (h15 : DLe 1 P.bitUnpack) (h16 : DLe 1 P.unpackT1) (h17 : DLe 1 P.hintUnpack) (h18 : DLe 1 P.rej4)

include ha hp hs h1 h2 h3 h4 h6 h7 h9 h11 h12 h13 h15 h16 h17 h18 in
theorem verify_dle : DLe 1 (Impl.MlDsa.AArch64.Verify.verifyWith c P p) := by
  unfold Impl.MlDsa.AArch64.Verify.verifyWith
  dle_tac
end

section
variable (v : Proof.Sha3.AArch64.Permutation)

/-- `vg_mldsa*_verify`, with the Keccak permutation of `v`. -/
theorem verifyWith_dle (p : Spec.MlDsa.Params) :
    DLe 1 (Impl.MlDsa.AArch64.Verify.verifyWith v.callee (Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p) := by
  have C := KeyGen.prims_okWith (keccak := v)
  obtain ⟨ha, hp, hs⟩ := keccak_dle v
  exact verify_dle _ _ p ha hp hs (.of_fd C.ntt.fd) (.of_fd C.invNtt.fd) (.of_fd C.mul.fd) (.of_fd C.mulAdd.fd)
    (.of_fd C.sub.fd) (.of_fd C.rejNtt.fd) (.of_fd C.ball.fd) (.of_fd C.useHint.fd) (.of_fd C.normLt.fd)
    (.of_fd C.simpleBitPack.fd) (.of_fd C.bitUnpack.fd) (.of_fd C.unpackT1.fd) (.of_fd C.hintUnpack.fd) (.of_fd C.rej4.fd)


end

end VG.Proof.MlDsa.AArch64.Message
