module

public import VerifiedGarbage.Impl.Pbkdf2.Md.X86_64

/-!
# HMAC's `init` for a key of any length over any Merkle–Damgård hash function: x86-64 implementation

`initAny(inner = rdi, outer = rsi, key = rdx, key_len = rcx, scratch = r8)`
does FIPS 198-1 §4's steps 1–3 for a key of any length: a key longer than a
block is hashed with the hash function's streaming functions, as `pbkdf2`
hashes a long password (`Hash.key`), and HMAC's `init` (`init_scratch`, which
takes a key of at most a block) is called with the key or its digest.

`scratch` has `pbkdf2`'s working space, `W + S` words, laid out as its: the
working space of the functions we call (`8 W` bytes), our caller's registers
(at `sv`), and for a long key the working state (at `stWO`) and its digest
(at `hkO`). The registers are `pbkdf2`'s up to the key, so that `Hash.key`
makes it: `rbx` = `key`, `rbp` = `key_len`, `r12` = `inner`, `r13` =
`outer`, `r15` = `scratch`. The only branch is on `key_len`, which is public.

The digest stays in `scratch`, which the function that allocates it wipes
(`withStackScratchWiped`).
-/

@[expose] public section

namespace VG.Impl.Pbkdf2.Md.X86_64

open VG.X86_64

namespace Hash

variable (H : Hash)

/-- Saving our caller's registers and setting up ours; then comparing the
key's length with the block size. -/
def anyEntry : List Instr :=
  H.hh.save ++ ([.mov .r15 (.reg .r8), .mov .rbx (.reg .rdx), .mov .rbp (.reg .rcx),
    .mov .r12 (.reg .rdi), .mov .r13 (.reg .rsi),
    .alu .cmp .rbp (.imm (BitVec.ofNat 32 (H.P.B + 1)))] : List Instr)

/-- HMAC's `init`'s states and working space (its key is in `rdx`, `rcx`). -/
def anyArgs : List Instr := [.mov .rdi (.reg .r12), .mov .rsi (.reg .r13), .mov .r8 (.reg .r15)]

def hmacInitAny : Prog isa :=
  .seq (.block H.anyEntry)
  (.seq H.key
  (.seq (.block Hash.anyArgs)
  (.seq (.call H.hmacInitN H.hmacInit)
    (.block H.exit))))

end Hash

end VG.Impl.Pbkdf2.Md.X86_64
