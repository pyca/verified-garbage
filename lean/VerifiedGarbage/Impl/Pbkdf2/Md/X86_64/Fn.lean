module

public import VerifiedGarbage.Impl.Pbkdf2.Md.X86_64
public import VerifiedGarbage.Impl.Pbkdf2.Md.AnyKey.X86_64
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.StackScratch.X86_64

/-!
# HMAC and PBKDF2 over a Merkle–Damgård hash function on x86-64: the functions as emitted

Each over a variant's code of the hash function `H`, in a frame of its own
for its working space (`Impl.StackScratch.X86_64`), followed by its cleanup
(`Impl.Scrub.X86_64`): `vg_hmac_<hash>_init`, the entry that runs the code
for a key of at most a block or the one for a key of any length, each with
the zeroing of every granule of its stack and the clearing of the registers
at the level `lv` (`scrubAll`); `vg_hmac_<hash>_finalize`, with the zeroing
of the runs `runs` of granules of its stack (`scrubSel`); and
`vg_pbkdf2_hmac_<hash>`, with the zeroing of every granule of its stack.
None returns a value.
-/

@[expose] public section

namespace VG.Impl.Pbkdf2.Md.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel)

/-- `vg_hmac_<hash>_init` over `H`, for a hash function of blocks of `B`
bytes, as emitted: for a key of at most a block, HMAC's `init` with
`H.stream.W + 6` words of working space; for a key of any length, its
`init` for any key with `H.W + H.S` words, which it wipes. -/
def hmacInit (lv : VecLevel) (B : Nat) (H : Hash) : Prog isa :=
  Impl.Pbkdf2.Md.X86_64.initEntry B
    (Impl.Scrub.X86_64.scrubAll lv 0 (16 + (8 + 8 * (H.stream.W + 6)))
      (Impl.StackScratch.X86_64.withStackScratch (8 + 8 * (H.stream.W + 6)) .r8 H.hmacInit))
    (Impl.Scrub.X86_64.scrubAll lv 0 (24 + (8 + 8 * (H.W + H.S)))
      (Impl.StackScratch.X86_64.withStackScratchWiped (8 + 8 * (H.W + H.S)) .r8 (H.W + H.S) H.hmacInitAny))

/-- `vg_hmac_<hash>_finalize` over `H`, as emitted: HMAC's `finalize` with
`H.W` words of working space. -/
def hmacFinalize (lv : VecLevel) (runs : List (Nat × Nat)) (H : Hash) : Prog isa :=
  Impl.Scrub.X86_64.scrubSel lv 0 (16 + (8 + 8 * H.W)) runs
    (Impl.StackScratch.X86_64.withStackScratch (8 + 8 * H.W) .r8 H.hmacFin)

/-- `vg_pbkdf2_hmac_<hash>` over `H`, as emitted: PBKDF2 with `H.W + H.S`
words of working space. -/
def pbkdf2 (lv : VecLevel) (H : Hash) : Prog isa :=
  Impl.Scrub.X86_64.scrubAll lv 0 (24 + (24 + 8 * (H.W + H.S)))
    (Impl.StackScratch.X86_64.withStackArgScratch (24 + 8 * (H.W + H.S)) 1 H.pbkdf2)

end VG.Impl.Pbkdf2.Md.X86_64.Fn
