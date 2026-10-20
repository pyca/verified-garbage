module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.Cold
public import VerifiedGarbage.Proof.Framework.EntryBranch
public import VerifiedGarbage.Proof.Framework.OffsetBelow
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
public import VerifiedGarbage.Proof.Hmac.AnyKey
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
public import VerifiedGarbage.Proof.MdStream.X86_64.Words
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.AnyKeyEntry
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PadW
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words
public import VerifiedGarbage.Proof.Pbkdf2.Scratch
public import VerifiedGarbage.Proof.Sha256.X86_64.Compress
public import VerifiedGarbage.Proof.Sha512.X86_64.Wide
import VerifiedGarbage.Proof.Framework.Cold
import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Hmac.AnyKey
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.AnyKeyEntry
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PadW
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words
import VerifiedGarbage.Proof.Pbkdf2.Scratch
import VerifiedGarbage.Proof.Sha256.X86_64.Compress
import VerifiedGarbage.Proof.Sha512.X86_64.Wide

/-!
# PBKDF2-HMAC (RFC 8018) over a Merkle–Damgård hash function on x86-64

A generic file (see `TCB/Emit.lean`): PBKDF2's `iterate`
(`Impl/Pbkdf2/X86_64.lean`) and the whole `pbkdf2`, the one implementation for
every Merkle–Damgård hash function (`Impl/Pbkdf2/Md/X86_64.lean`), calling the
variant's compression function and the functions made with it, are emitted
once for each variant (`Variants/MdHash/X86_64/`), named with its suffix (e.g.
`vg_pbkdf2_hmac_sha256_shani`).

`stack` is that of the shared contracts: 8 bytes for `iterate`, which calls
only the compression function, and 24 for `pbkdf2`'s code, which calls HMAC's
functions, which call the streaming ones.

`pbkdf2` runs that code in a frame holding its working space, which was its
second stack argument (`Verified.stackArgScratch`). For SHA-256, whose
`pbkdf2` scrypt's code calls with its own working space, the code is also
emitted on its own, as `vg_pbkdf2_hmac_sha256_scratch`.
-/

@[expose] public section

namespace VG.Generic.MdHash.X86_64.Pbkdf2

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact := [
  v.I.iterateApi.artifact X86_64.target {
    suffix := v.suffix
    code := v.H.iterate
    stack := 8
    verified := v.iterate
    spSafe := v.iterateSp
    features := v.features },
  v.I.pbkdf2Api.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch (Proof.Pbkdf2.Md.X86_64.pbkdf2Frame v.I) 1 v.H.pbkdf2
    stack := 24 + Proof.Pbkdf2.Md.X86_64.pbkdf2Frame v.I
    verified := v.pbkdf2F
    spSafe := X86_64.withStackArgScratch_spSafe v.pbkdf2Sp
    features := v.features }] ++
  -- Scrypt's code calls `pbkdf2` of SHA-256 with its own working space.
  match v.sha256 with
  | none => []
  | some _ => [
    v.I.pbkdf2ScratchApi.artifact X86_64.target {
      suffix := v.suffix
      code := v.H.pbkdf2
      stack := 24
      verified := v.pbkdf2
      spSafe := v.pbkdf2Sp
      features := v.features }]

end VG.Generic.MdHash.X86_64.Pbkdf2
