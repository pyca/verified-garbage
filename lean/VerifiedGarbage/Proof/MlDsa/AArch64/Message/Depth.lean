import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Verified
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.DepthBase

/-!
# ML-DSA on AArch64: how deep the frames of signing and verification nest

Untrusted: everything here is checked by Lean. Frames nest at most once in
`vg_mldsa*_sign`, with any implementation of the Keccak permutation
(`sign_dle`; `DepthVerify.lean`: `vg_mldsa*_verify`): their own code has no frames,
and those of the functions they call nest at most once (`DLe`, from the
structure of the code, `dle_tac`). So their calls use the 16 bytes of stack
below the stack pointer.
-/

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
include ha hp hs h1 h2 h3 h4 h5 h6 h7 h8 h9 h11 h12 h13 h15 h16 h17 h18 h19 h20 in
theorem sign_dle : DLe 1 (Impl.MlDsa.AArch64.Sign.signWith c P p) := by
  unfold Impl.MlDsa.AArch64.Sign.signWith
  dle_tac
end


section
variable (v : Proof.Sha3.AArch64.Permutation)

/-- `vg_mldsa*_sign`, with the Keccak permutation of `v`. -/
theorem signWith_dle (p : Spec.MlDsa.Params) :
    DLe 1 (Impl.MlDsa.AArch64.Sign.signWith v.callee (Sign.primsWith v.callee) p) := by
  have C := Sign.prims_okWith (keccak := v)
  obtain ⟨ha, hp, hs⟩ := keccak_dle v
  exact sign_dle _ _ p ha hp hs (.of_fd C.ntt.fd) (.of_fd C.invNtt.fd) (.of_fd C.mul.fd) (.of_fd C.mulAdd.fd)
    (.of_fd C.add.fd) (.of_fd C.sub.fd) (.of_fd C.rejNTT.fd) (.of_fd C.expandMask.fd) (.of_fd C.ball.fd)
    (.of_fd C.lowBits.fd) (.of_fd C.normLt.fd) (.of_fd C.makeHint.fd)
    (.of_fd C.bitPack.fd) (.of_fd C.bitUnpack.fd) (.of_fd C.hintBitPack.fd) (.of_fd C.rej4.fd)
    (by dsimp only [Sign.primsWith, Impl.MlDsa.AArch64.Optimized.HighPack.code]; dle_tac)
    (.of_fd C.expandMaskPair.fd)

end

end VG.Proof.MlDsa.AArch64.Message
