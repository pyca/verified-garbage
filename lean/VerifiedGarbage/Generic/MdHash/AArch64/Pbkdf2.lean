module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.Framework.Cold
public import VerifiedGarbage.Proof.Framework.EntryBranch
public import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Hmac.AnyKey
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.AnyKeyEntry
public import VerifiedGarbage.Proof.Sha256.AArch64.Compress
public import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Common
public import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Digest
public import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Init
public import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Digest
public import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Init
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Cold
import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Hmac.AnyKey
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.AnyKeyEntry
import VerifiedGarbage.Proof.Sha256.AArch64.Compress
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Common
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Digest
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Init
import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Digest
import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Init

/-!
# PBKDF2-HMAC (RFC 8018) over a Merkle–Damgård hash function on AArch64

A generic file (see `TCB/Emit.lean`): PBKDF2's `iterate`
(`Impl/Pbkdf2/AArch64.lean`) and the whole `pbkdf2`, the one implementation
for every Merkle–Damgård hash function (`Impl/Pbkdf2/Md/AArch64.lean`),
calling the variant's compression function and the functions made with it, are
emitted once for each variant (`Variants/MdHash/AArch64/`), named with its
suffix.

`stack` is that of the shared contracts: none for `iterate`, which calls
only the compression function (which pushes no frame), and 16 bytes for
`pbkdf2`'s code, whose callees' callees (the streaming functions) may push a
frame saving `x30`. Neither code pushes a frame of its own: each saves its
return address in `scratch`.

`pbkdf2` runs that code in a frame of `8 * pbkdf2Scratch` bytes holding its
working space (`Verified.stackScratch`). For SHA-256, whose `pbkdf2` scrypt's
code calls with its own working space, the code is also emitted on its own,
as `vg_pbkdf2_hmac_sha256_scratch`.
-/

@[expose] public section

namespace VG.Generic.MdHash.AArch64.Pbkdf2

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact := [
  v.I.iterateApi.artifact AArch64.target {
    suffix := v.suffix
    notes := ["The function uses no stack: it saves its return address in `scratch`."]
    code := v.H.iterate
    verified := v.iterate
    features := v.features },
  v.I.pbkdf2Api.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch (Proof.Pbkdf2.Md.AArch64.pbkdf2Frame v.I) .x7 v.H.pbkdf2
    stack := 16 + Proof.Pbkdf2.Md.AArch64.pbkdf2Frame v.I
    verified := v.pbkdf2F
    features := v.features }] ++
  -- Scrypt's code calls `pbkdf2` of SHA-256 with its own working space.
  match v.sha256 with
  | none => []
  | some _ => [
    v.I.pbkdf2ScratchApi.artifact AArch64.target {
      suffix := v.suffix
      code := v.H.pbkdf2
      stack := 16
      verified := v.pbkdf2
      features := v.features }]

end VG.Generic.MdHash.AArch64.Pbkdf2
