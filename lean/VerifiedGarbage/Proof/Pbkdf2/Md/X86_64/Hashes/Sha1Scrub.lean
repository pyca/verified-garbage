module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.ScrubStream
public import VerifiedGarbage.Proof.Sha1.PostOut
import VerifiedGarbage.Proof.Sha1.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# SHA-1's streaming and one-shot functions on x86-64, without secret residue

What the cleanup (`StreamFnS`) needs of `updFn`, `finFn` and `digFn` beyond their
code: their postconditions read the memory on return only within the
buffers (`X86_64.Scrub.PostOut`). Each variant
(`Proof/Variants/MdHash/X86_64/Sha1*.lean`) scrubs them with the granules
the residue analysis of its own code selects.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64.Sha1

open VG.X86_64 VG.X86_64.Scrub

theorem updOut (v : Proof.Sha1.X86_64.Compress) : PostOut (updFn v).contract (updFn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.updatePost_out 64)

theorem finOut (v : Proof.Sha1.X86_64.Compress) : PostOut (finFn v).contract (finFn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.finalizePost_out 64)

theorem digOut (v : Proof.Sha1.X86_64.Compress) : PostOut (digFn v).contract (digFn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.digestPost_out 64)

section Zero
variable (v : Proof.Sha1.X86_64.Compress)
  (hc : MdStream.X86_64.CalleeOk (P := Proof.Sha1.X86_64.Stream.params0) Proof.Sha1.md v.callee.code)

theorem updOut0 : PostOut (updFn0 v hc).contract (updFn0 v hc).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.updatePost_out 64)

theorem finOut0 : PostOut (finFn0 v hc).contract (finFn0 v hc).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.finalizePost_out 64)

theorem digOut0 : PostOut (digFn0 v hc).contract (digFn0 v hc).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.digestPost_out 64)

end Zero

end VG.Proof.Pbkdf2.Md.X86_64.Sha1
