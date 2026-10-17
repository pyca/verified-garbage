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
(`withStackScratchWiped`). `vg_hmac_<hash>_init` runs that only for a key
longer than a block (`initEntry`, which compares `key_len` on entry): a key
of at most a block goes to `init` in a frame of its own as before, smaller
and not wiped.
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

/-- `x9 ← (B ≥ key_len) ? 0 : key_len`: zero exactly when the key (`x3`) is
at most `B` bytes (`subs` sets C, no borrow, when `B ≥ key_len`). -/
def entryCmp (B : Nat) : List Instr :=
  [.movz .x .x10 (BitVec.ofNat 16 B) 0, .movz .x .x12 0 0, .subs .x .x11 .x10 .x3, .csel .x .x9 .x12 .x3]

/-- `init` for a key of any length, choosing on entry: `long` (`init` for a
key of any length, cold) if `key_len` is more than `B` bytes, and `short`
(`init` for a key of at most a block) otherwise. -/
def initEntry (B : Nat) (short long : Prog isa) : Prog isa :=
  .seq (.block (entryCmp B)) (Code.iteCold (.nonzero .x .x9) long short)

end VG.Impl.Pbkdf2.Md.AArch64
