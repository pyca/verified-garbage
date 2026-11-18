module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha384
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_224
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_256
public import VerifiedGarbage.Proof.Sha512.PostOut
public import VerifiedGarbage.Proof.Sha512.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sha512.RISCV64.Compress
import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Init
import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Update
import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Finalize
public import VerifiedGarbage.Spec.Sha512.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Impl.Sha512.RISCV64.Stream
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Sha512.RISCV64.Contract

/-! ### `Sha512.RISCV64.Shared`, which only this module used -/

section

/-!
# SHA-512 on RISC-V: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written
against per-target contracts (`Proof/Sha512/RISCV64/Contract.lean`); these
theorems move them to the shared contracts of `Spec/Sha512/Contract.lean`,
which the artifacts are emitted with.

`update` and `finalize` keep their working space in a frame of their own,
of 208 bytes (`Impl.Sha512.RISCV64.Stream.frameBytes`), the `stack` of their
contracts. SHA-384, SHA-512/224 and SHA-512/256 are SHA-512 from other
initial hash values, with their digests the first 48, 28 and 32 bytes of the
final hash value; their `update` is SHA-512's.
-/

@[expose] public section

namespace VG.Proof.Sha512.RISCV64.Shared

open _root_.VG.RISCV64

/-- `init` from `iv`, with the shared contract. -/
theorem init_of {iv : Spec.Sha512.HashValue}
    (hv : Verified RISCV64.target (Impl.Sha512.RISCV64.Stream.initWith iv) (Proof.Sha512.initRISCV64 iv)) :
    Verified RISCV64.target (Impl.Sha512.RISCV64.Stream.initWith iv) (Spec.Sha512.initContract RISCV64.abi iv) :=
  hv.of_implies (by
    contract_implies [Spec.Sha512.initContract, Spec.Sha512.initSig, Proof.Sha512.initRISCV64,
      RISCV64.abi, RISCV64.argRegs]
      [Proof.Sha512.RISCV64.Stream.initSat] using Proof.Sha512.RISCV64.Stream.initSat)

theorem init384 : Verified RISCV64.target (Impl.Sha512.RISCV64.Stream.initWith Spec.Sha512.H0_384)
    (Spec.Sha512.initContract RISCV64.abi Spec.Sha512.H0_384) :=
  init_of Proof.Sha512.RISCV64.Stream.init384_verified

theorem init512 : Verified RISCV64.target (Impl.Sha512.RISCV64.Stream.initWith Spec.Sha512.H0_512)
    (Spec.Sha512.initContract RISCV64.abi Spec.Sha512.H0_512) :=
  init_of Proof.Sha512.RISCV64.Stream.init512_verified

theorem init512_224 : Verified RISCV64.target (Impl.Sha512.RISCV64.Stream.initWith Spec.Sha512.H0_512_224)
    (Spec.Sha512.initContract RISCV64.abi Spec.Sha512.H0_512_224) :=
  init_of Proof.Sha512.RISCV64.Stream.init512_224_verified

theorem init512_256 : Verified RISCV64.target (Impl.Sha512.RISCV64.Stream.initWith Spec.Sha512.H0_512_256)
    (Spec.Sha512.initContract RISCV64.abi Spec.Sha512.H0_512_256) :=
  init_of Proof.Sha512.RISCV64.Stream.init512_256_verified

theorem update :
    Verified RISCV64.target Impl.Sha512.RISCV64.Stream.update
      (Spec.Sha512.updateContract RISCV64.abi 208) :=
  Proof.Sha512.RISCV64.Stream.Update.update_verified.of_implies (by
    contract_implies [Spec.Sha512.updateContract, Spec.Sha512.updateSig, Spec.Sha512.updatePost,
      Proof.Sha512.updateRISCV64, RISCV64.abi, RISCV64.argRegs]
      [Proof.Sha512.RISCV64.Stream.Update.sat] using Proof.Sha512.RISCV64.Stream.Update.sat)

/-- `finalizeDRISCV64 64`, writing all of the final hash value. -/
def finalize64 : Contract RISCV64.isa :=
  { Proof.Sha512.finalizeDRISCV64 64 with
    post := fun s s' => ∀ iv m, Spec.Sha512.Repr iv s.mem (s.gpr .a0) m → m.length < 2 ^ 64 →
      s.gpr .a1 = BitVec.ofNat 64 m.length →
      Spec.Sha512.bytesAt s'.mem (s.gpr .a2) 64 = Spec.Sha512.finalHash iv m }

theorem finalize64_verified :
    Verified RISCV64.target Impl.Sha512.RISCV64.Stream.finalize finalize64 :=
  Proof.Sha512.RISCV64.Stream.Finalize.finalize64_verified.of_implies
    ⟨fun _ h => h, fun _ _ _ h iv m hr hl hc => by
      rw [h iv m hr hl hc]
      exact List.take_of_length_le (by
        unfold Spec.Sha512.finalHash
        exact Nat.le_of_eq (Proof.Sha512.RISCV64.Stream.Finalize.flat_length_all _)),
      fun _ _ _ _ h => h, Proof.Sha512.RISCV64.Stream.Finalize.finalize64_verified.2.2⟩

theorem finalize :
    Verified RISCV64.target Impl.Sha512.RISCV64.Stream.finalize
      (Spec.Sha512.finalizeContract RISCV64.abi 208) :=
  finalize64_verified.of_implies (by
    contract_implies [Spec.Sha512.finalizeContract, Spec.Sha512.finalizeSig, Spec.Sha512.finalizePost,
      finalize64, Proof.Sha512.finalizeDRISCV64, RISCV64.abi, RISCV64.argRegs]
      [Proof.Sha512.RISCV64.Stream.Finalize.sat] using Proof.Sha512.RISCV64.Stream.Finalize.sat 64)

/-! ## The truncated digests

`finalize384`, `finalize512_256` and `finalize512_224` write the first 48,
32 and 28 bytes of the final hash value (`finalizeDRISCV64`); for the
algorithm's initial hash value, that is its digest. -/

/-- `finalizeDRISCV64 D`, for the `D`-byte `digest` of the messages hashed
from `iv`. -/
def finalizeDigestR (iv : Spec.Sha512.HashValue) (D : Nat) (digest : List Byte → List Byte) :
    Contract RISCV64.isa :=
  { Proof.Sha512.finalizeDRISCV64 D with
    post := fun s s' => ∀ m, Spec.Sha512.Repr iv s.mem (s.gpr .a0) m → m.length < 2 ^ 64 →
      s.gpr .a1 = BitVec.ofNat 64 m.length → Spec.Sha512.bytesAt s'.mem (s.gpr .a2) D = digest m }

theorem finalizeDigestR_of {code : Prog isa} {D : Nat} {iv : Spec.Sha512.HashValue}
    {digest : List Byte → List Byte} (hv : Verified RISCV64.target code (Proof.Sha512.finalizeDRISCV64 D))
    (hdg : ∀ m, (Spec.Sha512.finalHash iv m).take D = digest m) :
    Verified RISCV64.target code (finalizeDigestR iv D digest) :=
  hv.of_implies ⟨fun _ h => h, fun _ _ _ h m hr hl hc => (h iv m hr hl hc).trans (hdg m),
    fun _ _ _ _ h => h, hv.2.2⟩

theorem finalize384 :
    Verified RISCV64.target Impl.Sha512.RISCV64.Stream.finalize384
      (Spec.Sha512.finalizeDigestContract RISCV64.abi Spec.Sha512.H0_384 48 Spec.Sha512.sha384 208) :=
  (finalizeDigestR_of (iv := Spec.Sha512.H0_384) (digest := Spec.Sha512.sha384)
    Proof.Sha512.RISCV64.Stream.Finalize.finalize384_verified fun _ => rfl).of_implies (by
    contract_implies [Spec.Sha512.finalizeDigestContract, Spec.Sha512.finalizeDigestSig,
      Spec.Sha512.finalizeDigestPost, finalizeDigestR, Proof.Sha512.finalizeDRISCV64, RISCV64.abi,
      RISCV64.argRegs]
      [Proof.Sha512.RISCV64.Stream.Finalize.sat] using Proof.Sha512.RISCV64.Stream.Finalize.sat 48)

theorem finalize512_256 :
    Verified RISCV64.target Impl.Sha512.RISCV64.Stream.finalize512_256
      (Spec.Sha512.finalizeDigestContract RISCV64.abi Spec.Sha512.H0_512_256 32 Spec.Sha512.sha512_256
        208) :=
  (finalizeDigestR_of (iv := Spec.Sha512.H0_512_256) (digest := Spec.Sha512.sha512_256)
    Proof.Sha512.RISCV64.Stream.Finalize.finalize512_256_verified fun _ => rfl).of_implies (by
    contract_implies [Spec.Sha512.finalizeDigestContract, Spec.Sha512.finalizeDigestSig,
      Spec.Sha512.finalizeDigestPost, finalizeDigestR, Proof.Sha512.finalizeDRISCV64, RISCV64.abi,
      RISCV64.argRegs]
      [Proof.Sha512.RISCV64.Stream.Finalize.sat] using Proof.Sha512.RISCV64.Stream.Finalize.sat 32)

theorem finalize512_224 :
    Verified RISCV64.target Impl.Sha512.RISCV64.Stream.finalize512_224
      (Spec.Sha512.finalizeDigestContract RISCV64.abi Spec.Sha512.H0_512_224 28 Spec.Sha512.sha512_224
        208) :=
  (finalizeDigestR_of (iv := Spec.Sha512.H0_512_224) (digest := Spec.Sha512.sha512_224)
    Proof.Sha512.RISCV64.Stream.Finalize.finalize512_224_verified fun _ => rfl).of_implies (by
    contract_implies [Spec.Sha512.finalizeDigestContract, Spec.Sha512.finalizeDigestSig,
      Spec.Sha512.finalizeDigestPost, finalizeDigestR, Proof.Sha512.finalizeDRISCV64, RISCV64.abi,
      RISCV64.argRegs]
      [Proof.Sha512.RISCV64.Stream.Finalize.sat] using Proof.Sha512.RISCV64.Stream.Finalize.sat 28)

end VG.Proof.Sha512.RISCV64.Shared

end

end

/-!
# SHA-384, SHA-512, SHA-512/224 and SHA-512/256 on RISC-V, without secret residue

Each of the streaming functions, followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.withScrub`), which clears the caller-saved registers and the
stack its frames used. Their postconditions read the memory on return only
within their buffers (`Proof/Sha512/PostOut.lean`). HMAC,
PBKDF2, Ed25519 and the digests call their code as the internal
`vg_sha512_init_core`, … (an `_core` suffix to each name), not these
functions.
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
  withScrub { code := Impl.MdStream.RISCV64.Digest.digest Proof.Hmac.Stream.RISCV64.Sha384.hash, verified := Proof.Hmac.Stream.RISCV64.Sha384.digest }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.digestPost_out 48 Spec.Sha512.sha384 64 (by decide)))

/-- `vg_sha512_digest`. -/
def digest512Reg : Registration Spec.Sha512.digest512Api RISCV64.target :=
  withScrub { code := Impl.MdStream.RISCV64.Digest.digest Proof.Hmac.Stream.RISCV64.Sha512.hash, verified := Proof.Hmac.Stream.RISCV64.Sha512.digest }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.digestPost_out 64 Spec.Sha512.sha512 64 (by decide)))

/-- `vg_sha512_224_digest`. -/
def digest512_224Reg : Registration Spec.Sha512.digest512_224Api RISCV64.target :=
  withScrub { code := Impl.MdStream.RISCV64.Digest.digest Proof.Hmac.Stream.RISCV64.Sha512_224.hash, verified := Proof.Hmac.Stream.RISCV64.Sha512_224.digest }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.digestPost_out 28 Spec.Sha512.sha512_224 64 (by decide)))

/-- `vg_sha512_256_digest`. -/
def digest512_256Reg : Registration Spec.Sha512.digest512_256Api RISCV64.target :=
  withScrub { code := Impl.MdStream.RISCV64.Digest.digest Proof.Hmac.Stream.RISCV64.Sha512_256.hash, verified := Proof.Hmac.Stream.RISCV64.Sha512_256.digest }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.digestPost_out 32 Spec.Sha512.sha512_256 64 (by decide)))


end VG.Proof.Sha512.RISCV64
