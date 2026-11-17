module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha224
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.ScrubStream
public import VerifiedGarbage.Proof.Sha256.PostOut
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Sha256.Scratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# SHA-224's and SHA-256's streaming and one-shot functions on x86-64, without secret residue

What `StreamFn.scrub` needs of SHA-256's `updFn`, `finFn` and `digFn`, and
SHA-224's `finFn` and `digFn`, beyond their code: their postconditions read
the memory on return only within the buffers (`X86_64.Scrub.PostOut`). Each variant
(`Proof/Variants/MdHash/X86_64/Sha256*.lean`) scrubs them with the granules
the residue analysis of its own code selects.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64.Sha256

open VG.X86_64 VG.X86_64.Scrub

theorem updOut (v : Proof.Sha256.X86_64.Compress) : PostOut (updFn v).contract (updFn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.updatePost_out 64)

theorem finOut (v : Proof.Sha256.X86_64.Compress) : PostOut (finFn v).contract (finFn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.finalizePost_out 64)

theorem digOut (v : Proof.Sha256.X86_64.Compress) : PostOut (digFn v).contract (digFn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.digestPost_out 32 Spec.Sha256.hash 64 (by decide))

section S
variable (v : Proof.Sha256.X86_64.Compress) {so : Nat} (h : so = 0 ∨ so = 112)
  (hv : Verified X86_64.target v.callee.code (Proof.Sha256.compressX86_64S so))

theorem updOutS : PostOut (updFnS v h hv).contract (updFnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.updatePost_out 64)

theorem finOutS : PostOut (finFnS v h hv).contract (finFnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.finalizePost_out 64)

theorem digOutS : PostOut (digFnS v h hv).contract (digFnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.digestPost_out 32 Spec.Sha256.hash 64 (by decide))

end S

end VG.Proof.Pbkdf2.Md.X86_64.Sha256

namespace VG.Proof.Pbkdf2.Md.X86_64.Sha224

open VG.X86_64 VG.X86_64.Scrub

theorem finOut (v : Proof.Sha256.X86_64.Compress) : PostOut (finFn v).contract (finFn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.finalize224Post_out 64)

theorem digOut (v : Proof.Sha256.X86_64.Compress) : PostOut (digFn v).contract (digFn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.digestPost_out 28 Spec.Sha256.sha224 64 (by decide))

section S
variable (v : Proof.Sha256.X86_64.Compress) {so : Nat} (h : so = 0 ∨ so = 112)
  (hv : Verified X86_64.target v.callee.code (Proof.Sha256.compressX86_64S so))

theorem finOutS : PostOut (finFnS v h hv).contract (finFnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.finalize224Post_out 64)

theorem digOutS : PostOut (digFnS v h hv).contract (digFnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.digestPost_out 28 Spec.Sha256.sha224 64 (by decide))

end S

end VG.Proof.Pbkdf2.Md.X86_64.Sha224
