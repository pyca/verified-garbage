module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.ScrubStream
public import VerifiedGarbage.Proof.Sha512.PostOut
import VerifiedGarbage.Proof.Sha512.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# SHA-384, SHA-512, SHA-512/224 and SHA-512/256 on x86-64, without secret residue

What `StreamFn.scrub` needs of their streaming and one-shot functions
beyond their code: their postconditions read the memory on return only
within the buffers (`X86_64.Scrub.PostOut`). Each variant scrubs them with
the granules the residue analysis of its own code selects
(`Proof/Variants/MdHash/X86_64/Sha512*.lean`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64.Sha512

open VG.X86_64 VG.X86_64.Scrub
open VG.Proof.Sha512.X86_64 (Compress)
open Spec.Sha512 (H0_384 H0_512_224 H0_512_256)

theorem updOut (v : Compress) : PostOut (updFn v).contract (updFn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.updatePost_out 64)

theorem finOut (v : Compress) : PostOut (finFn v).contract (finFn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.finalizePost_out 64)

theorem digOut (v : Compress) : PostOut (digFn v).contract (digFn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.digestPost_out 64 Spec.Sha512.sha512 64 (by decide))

theorem fin384Out (v : Compress) : PostOut (fin384Fn v).contract (fin384Fn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.finalizeDigestPost_out H0_384 48 Spec.Sha512.sha384 64 (by decide))

theorem dig384Out (v : Compress) : PostOut (dig384Fn v).contract (dig384Fn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.digestPost_out 48 Spec.Sha512.sha384 64 (by decide))

theorem fin512_256Out (v : Compress) : PostOut (fin512_256Fn v).contract (fin512_256Fn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.finalizeDigestPost_out H0_512_256 32 Spec.Sha512.sha512_256 64 (by decide))

theorem dig512_256Out (v : Compress) : PostOut (dig512_256Fn v).contract (dig512_256Fn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.digestPost_out 32 Spec.Sha512.sha512_256 64 (by decide))

theorem fin512_224Out (v : Compress) : PostOut (fin512_224Fn v).contract (fin512_224Fn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.finalizeDigestPost_out H0_512_224 28 Spec.Sha512.sha512_224 64 (by decide))

theorem dig512_224Out (v : Compress) : PostOut (dig512_224Fn v).contract (dig512_224Fn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.digestPost_out 28 Spec.Sha512.sha512_224 64 (by decide))

section S
variable (v : Compress) {so : Nat} (h : so = 0 ∨ so = 192)
  (hv : Verified X86_64.target v.callee.code (Proof.Sha512.compressWideX86_64S so))

theorem updOutS : PostOut (updFnS v h hv).contract (updFnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.updatePost_out 64)

theorem finOutS : PostOut (finFnS v h hv).contract (finFnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.finalizePost_out 64)

theorem digOutS : PostOut (digFnS v h hv).contract (digFnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.digestPost_out 64 Spec.Sha512.sha512 64 (by decide))

theorem fin384OutS : PostOut (fin384FnS v h hv).contract (fin384FnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.finalizeDigestPost_out H0_384 48 Spec.Sha512.sha384 64 (by decide))

theorem dig384OutS : PostOut (dig384FnS v h hv).contract (dig384FnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.digestPost_out 48 Spec.Sha512.sha384 64 (by decide))

theorem fin512_256OutS : PostOut (fin512_256FnS v h hv).contract (fin512_256FnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.finalizeDigestPost_out H0_512_256 32 Spec.Sha512.sha512_256 64 (by decide))

theorem dig512_256OutS : PostOut (dig512_256FnS v h hv).contract (dig512_256FnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.digestPost_out 32 Spec.Sha512.sha512_256 64 (by decide))

theorem fin512_224OutS : PostOut (fin512_224FnS v h hv).contract (fin512_224FnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.finalizeDigestPost_out H0_512_224 28 Spec.Sha512.sha512_224 64 (by decide))

theorem dig512_224OutS : PostOut (dig512_224FnS v h hv).contract (dig512_224FnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.digestPost_out 28 Spec.Sha512.sha512_224 64 (by decide))

end S

end VG.Proof.Pbkdf2.Md.X86_64.Sha512
