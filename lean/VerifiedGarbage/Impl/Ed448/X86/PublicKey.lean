module

public import VerifiedGarbage.Impl.Ed448.X86.Shake

/-!
# Ed448 public-key derivation on x86 (32-bit)

`vg_ed448_public_key(out, seed, scratch)`, cdecl, with the base-point
multiplication `base` (`vg_ed448_scalar_base`, a parameter: the proof holds
for any code meeting its contract): `SHAKE256(seed, 114)` with the sponge
functions (`Impl/Ed448/X86/Shake.lean`), the first 57 bytes pruned
(RFC 8032 §5.2.5), and `[s]B` encoded by `base`.

The frame is Ed25519's on this target (`Impl/Ed25519/X86/PublicKey.lean`):
64 words pushed, the outgoing arguments at `esp` (24 bytes), the hash at
`esp + 24`, pruned there in place, so that the scalar `base` reads lies
outside `scratch` and `out`, which it writes; the frame from `esp + 24` is
cleared before it is popped. Every address depends only on the pointers and
`esp`.
-/

@[expose] public section

namespace VG.Impl.Ed448.X86.PublicKey

open VG.X86
open VG.Impl.Ed25519.X86.Whole (Value setup zeroWords)
open VG.Impl.Ed448.X86.Shake

/-- Where in the frame the hash, and then the scalar, is; `scratch` is the
third argument. -/
def HASH : Nat := 24
def SC : Nat := 2

/-- `SHAKE256(seed, 114)` into the frame at `HASH`. -/
def hash : Prog isa :=
  .seq (zeroState SC) <| .seq (absorb (firstArgs SC (.caller 1 0) (.const 57))) <|
  .seq (pad SC) (squeeze SC HASH)

/-- `scalar_base(out, esp + HASH, scratch)`. -/
def baseArgs : List Instr := setup 0 [.caller 0 0, .frame HASH, .caller SC 0]

/-- The frame from `HASH` on, cleared. -/
def wipe : List Instr := zeroWords 6 58

def body (base : Prog isa) : Prog isa :=
  .seq hash <| .seq (.block (pruneAt HASH)) <|
  .seq (callWith baseArgs "vg_ed448_scalar_base" base) (.block wipe)

/-- `vg_ed448_public_key`, with `base` for `vg_ed448_scalar_base`. -/
def code (base : Prog isa) : Prog isa :=
  .frame (.push (List.replicate 64 .eax)) (body base) (.pop .eax 64)

end VG.Impl.Ed448.X86.PublicKey
