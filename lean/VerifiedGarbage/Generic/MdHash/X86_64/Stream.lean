module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant

/-!
# Streaming Merkle–Damgård hash functions on X86_64

A generic file (see `TCB/Emit.lean`): each variant's streaming `update` and
`finalize` made with its implementation of the compression function, named
with its suffix (e.g. `vg_sha256_update_shani`). Those a family shares are carried by one member's variants (SHA-512's, for the
SHA-512 family); those of a hash function with one implementation (MD5) are
in its registration file.

The variant supplies each function's `Api` and its verified code
(`MdHash.stream`, a `StreamFn`), whose contract is the one the `Api` gives it
(`StreamFn.ofApi`).
-/

@[expose] public section

namespace VG.Generic.MdHash.X86_64.Stream

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact := v.stream.map fun f =>
  f.api.artifact X86_64.target { f.reg with suffix := v.suffix, features := v.features }

end VG.Generic.MdHash.X86_64.Stream
