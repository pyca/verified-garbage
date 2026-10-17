module

public import VerifiedGarbage.Impl.Pbkdf2.Md.AArch64

/-!
# HMAC's `init` for a key of any length over any Merkle–Damgård hash function: AArch64 implementation

As on x86-64 (`Impl/Pbkdf2/Md/AnyKey/X86_64.lean`):
`initAny(inner = x0, outer = x1, key = x2, key_len = x3, scratch = x4)`
does FIPS 198-1 §4's steps 1–3 for a key of any length: a key longer than a
block is hashed with the hash function's streaming functions, as `pbkdf2`
hashes a long password (`Hash.key`), and HMAC's `init` (`init_scratch`, which
takes a key of at most a block) is called with the key or its digest.

`scratch` has `pbkdf2`'s working space, `W + S` words, laid out as its: the
working space of the functions we call (`8 W` bytes), our caller's registers
and our return address (at `sv`), and for a long key the working state (at
`stWO`) and its digest (at `hkO`). The registers are `pbkdf2`'s up to the
key, so that `Hash.key` makes it: `x19` = `key`, `x20` = `key_len`, `x21` =
`inner`, `x22` = `outer`, `x23` = `scratch`. The only branches are on
`key_len`, which is public.

The digest stays in `scratch`, which the function that allocates it wipes
(`withStackScratchWiped`).
-/

@[expose] public section

namespace VG.Impl.Pbkdf2.Md.AArch64

open VG.AArch64
open VG.Impl.MdStream.AArch64 (mov)

namespace Hash

variable (H : Hash)

/-- Saving our caller's registers and our return address, and setting up
ours. -/
def anyEntry : List Instr :=
  H.hh.save ++ [mov .x23 .x4, mov .x19 .x2, mov .x20 .x3, mov .x21 .x0, mov .x22 .x1]

/-- HMAC's `init`'s states and working space (its key is in `x2`, `x3`). -/
def anyArgs : List Instr := [mov .x0 .x21, mov .x1 .x22, mov .x4 .x23]

def hmacInitAny : Prog isa :=
  .seq (.block H.anyEntry)
  (.seq H.key
  (.seq (.block Hash.anyArgs)
  (.seq (.call H.hmacInitN H.hmacInit)
    (.block H.exit))))

end Hash

end VG.Impl.Pbkdf2.Md.AArch64
