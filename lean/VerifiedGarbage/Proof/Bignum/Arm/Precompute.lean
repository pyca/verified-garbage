module
public import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeLaw
public import VerifiedGarbage.Proof.Bignum.Arm.R2Kernel
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Bignum.Arm.Precompute
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopState

import VerifiedGarbage.Proof.Bignum.Arm.ImportModulus
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeInverse
import VerifiedGarbage.Proof.Bignum.Arm.R2
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Framework.Block

/-! # RSA precomputation from modulus bytes, entirely in proved ARMv7 code -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt wOf Layout)
open VG.Proof.X25519.Arm (Rest)

theorem precomputeWith_ok (kernel : R2Kernel) : PrecomputeLaw (precomputeWith kernel.code) := by
  intro s base src len w k ws layout width hk fit srcFit read sep ptr source count
    stackRead stackSep saved large odd countFits
  rw [precomputeWith, WP.seq_iff]
  refine WP.mono (importModulus_ok s ws layout width hk fit srcFit read sep ptr source count
    stackRead stackSep saved) ?_
  rintro u ⟨layoutU, widthU, ptrU, modulus, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (precomputeInverse_ok u (ws.congr restU.wr) layoutU widthU ptrU
    (by rw [modulus]; exact odd) (by rw [modulus]; exact large)
    (by rw [restU.rd, restU.wr, restU.sp]; exact stackRead)
    (by rw [restU.sp]; exact stackSep) (saved_base_kept frameU stackSep saved restU.sp)) ?_
  rintro v ⟨ready, modV, frameV, restV⟩
  refine WP.mono (kernel.correct v ready countFits) ?_
  rintro t ⟨done, value, modT, frameT, restT⟩
  rw [modV, modulus] at value
  exact ⟨done, modT.trans (modV.trans modulus), value,
    frameU.trans (frameV.trans frameT), restU.trans (restV.trans restT)⟩

theorem precompute_ok : PrecomputeLaw precompute := precomputeWith_ok baselineR2Kernel

end VG.Proof.Bignum.Arm
