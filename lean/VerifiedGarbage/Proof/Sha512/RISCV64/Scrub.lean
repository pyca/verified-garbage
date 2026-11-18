module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha512.RISCV64.Shared
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha384
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_224
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_256
public import VerifiedGarbage.Proof.Sha512.PostOut

meta import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Sha512.RISCV64.Shared
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha384
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_224
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_256
meta import VerifiedGarbage.Proof.Sha512.PostOut
/-!
# SHA-384, SHA-512, SHA-512/224 and SHA-512/256 on RISC-V, without secret residue

Each of the streaming functions, followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.withScrub`), which clears the caller-saved registers and the
stack its frames used. Their postconditions read the memory on return only
within their buffers (`Proof/Sha512/PostOut.lean`). HMAC,
PBKDF2, Ed25519 and the digests call their code as the internal
`vg_sha512_init_core`, … (an `_core` suffix to each name), not these
functions.

The `digest` functions instead clear only the runs of doublewords that the residue
analysis (`RISCV64.rtaint`) finds may differ between two runs
(`RISCV64.Scrub.withScrubSel`, `scrubSel_noResidue`). Their code wipes most of
its own scratch space, which leaves few such doublewords, or none.
-/

@[expose] public section

namespace VG.Proof.Sha512.RISCV64

open VG.RISCV64 VG.RISCV64.Scrub

/-- `vg_sha384_init`. -/
def init384Reg : Registration Spec.Sha512.init384Api RISCV64.target :=
  withScrub { code := Impl.Sha512.RISCV64.Stream.initWith Spec.Sha512.H0_384, verified := Shared.init384 }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.initPost_out Spec.Sha512.H0_384 64))

/-- `vg_sha512_init`. -/
def init512Reg : Registration Spec.Sha512.init512Api RISCV64.target :=
  withScrub { code := Impl.Sha512.RISCV64.Stream.initWith Spec.Sha512.H0_512, verified := Shared.init512 }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.initPost_out Spec.Sha512.H0_512 64))

/-- `vg_sha512_224_init`. -/
def init512_224Reg : Registration Spec.Sha512.init512_224Api RISCV64.target :=
  withScrub { code := Impl.Sha512.RISCV64.Stream.initWith Spec.Sha512.H0_512_224, verified := Shared.init512_224 }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.initPost_out Spec.Sha512.H0_512_224 64))

/-- `vg_sha512_256_init`. -/
def init512_256Reg : Registration Spec.Sha512.init512_256Api RISCV64.target :=
  withScrub { code := Impl.Sha512.RISCV64.Stream.initWith Spec.Sha512.H0_512_256, verified := Shared.init512_256 }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.initPost_out Spec.Sha512.H0_512_256 64))

/-- `vg_sha512_update`. -/
def updateReg : Registration Spec.Sha512.updateApi RISCV64.target :=
  withScrub { code := Impl.Sha512.RISCV64.Stream.update, verified := Shared.update }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.updatePost_out 64))

/-- `vg_sha512_finalize`. -/
def finalizeReg : Registration Spec.Sha512.finalizeApi RISCV64.target :=
  withScrub { code := Impl.Sha512.RISCV64.Stream.finalize, verified := Shared.finalize }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.finalizePost_out 64))

/-- `vg_sha384_finalize`. -/
def finalize384Reg : Registration Spec.Sha512.finalize384Api RISCV64.target :=
  withScrub { code := Impl.Sha512.RISCV64.Stream.finalize384, verified := Shared.finalize384 }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.finalizeDigestPost_out Spec.Sha512.H0_384 48 Spec.Sha512.sha384 64 (by decide)))

/-- `vg_sha512_256_finalize`. -/
def finalize512_256Reg : Registration Spec.Sha512.finalize512_256Api RISCV64.target :=
  withScrub { code := Impl.Sha512.RISCV64.Stream.finalize512_256, verified := Shared.finalize512_256 }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.finalizeDigestPost_out Spec.Sha512.H0_512_256 32 Spec.Sha512.sha512_256 64 (by decide)))

/-- `vg_sha512_224_finalize`. -/
def finalize512_224Reg : Registration Spec.Sha512.finalize512_224Api RISCV64.target :=
  withScrub { code := Impl.Sha512.RISCV64.Stream.finalize512_224, verified := Shared.finalize512_224 }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.finalizeDigestPost_out Spec.Sha512.H0_512_224 28 Spec.Sha512.sha512_224 64 (by decide)))

/-- `vg_sha384_digest`. -/
def digest384Reg : Registration Spec.Sha512.digest384Api RISCV64.target :=
  withScrubSel { code := Impl.MdStream.RISCV64.Digest.digest Proof.Hmac.Stream.RISCV64.Sha384.hash, verified := Proof.Hmac.Stream.RISCV64.Sha384.digest } [(448, [(0, 26), (50, 6)])]
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.digestPost_out 48 Spec.Sha512.sha384 64 (by decide)))
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.digestPost_out 48 Spec.Sha512.sha384 64 (by decide))) (hbp_nil _)
      (Impl.MdStream.RISCV64.Digest.digest Proof.Hmac.Stream.RISCV64.Sha384.hash) 448 0
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `vg_sha512_digest`. -/
def digest512Reg : Registration Spec.Sha512.digest512Api RISCV64.target :=
  withScrubSel { code := Impl.MdStream.RISCV64.Digest.digest Proof.Hmac.Stream.RISCV64.Sha512.hash, verified := Proof.Hmac.Stream.RISCV64.Sha512.digest } [(448, [(0, 26), (50, 6)])]
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.digestPost_out 64 Spec.Sha512.sha512 64 (by decide)))
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.digestPost_out 64 Spec.Sha512.sha512 64 (by decide))) (hbp_nil _)
      (Impl.MdStream.RISCV64.Digest.digest Proof.Hmac.Stream.RISCV64.Sha512.hash) 448 0
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `vg_sha512_224_digest`. -/
def digest512_224Reg : Registration Spec.Sha512.digest512_224Api RISCV64.target :=
  withScrubSel { code := Impl.MdStream.RISCV64.Digest.digest Proof.Hmac.Stream.RISCV64.Sha512_224.hash, verified := Proof.Hmac.Stream.RISCV64.Sha512_224.digest } [(448, [(0, 26), (50, 6)])]
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.digestPost_out 28 Spec.Sha512.sha512_224 64 (by decide)))
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.digestPost_out 28 Spec.Sha512.sha512_224 64 (by decide))) (hbp_nil _)
      (Impl.MdStream.RISCV64.Digest.digest Proof.Hmac.Stream.RISCV64.Sha512_224.hash) 448 0
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `vg_sha512_256_digest`. -/
def digest512_256Reg : Registration Spec.Sha512.digest512_256Api RISCV64.target :=
  withScrubSel { code := Impl.MdStream.RISCV64.Digest.digest Proof.Hmac.Stream.RISCV64.Sha512_256.hash, verified := Proof.Hmac.Stream.RISCV64.Sha512_256.digest } [(448, [(0, 26), (50, 6)])]
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.digestPost_out 32 Spec.Sha512.sha512_256 64 (by decide)))
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.digestPost_out 32 Spec.Sha512.sha512_256 64 (by decide))) (hbp_nil _)
      (Impl.MdStream.RISCV64.Digest.digest Proof.Hmac.Stream.RISCV64.Sha512_256.hash) 448 0
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))


end VG.Proof.Sha512.RISCV64
