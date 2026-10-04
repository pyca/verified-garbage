import VerifiedGarbage.Impl.Ed448.X86.Shake
import VerifiedGarbage.Impl.Ed448.X86.Scalar

/-!
# Ed448 signing with a cached public key on x86 (32-bit)

`vg_ed448_sign_cached(out, seed, pk, context, ctxlen, message, len,
scratch)`, cdecl, with the base-point multiplication `base`
(`vg_ed448_scalar_base`, a parameter: the proof holds for any code meeting
its contract): RFC 8032 §5.2.6, with the public key `A` given (and
`ctxlen ≤ 255`).

In Ed25519's frame on this target (64 words pushed: the outgoing arguments
at `esp`, 24 bytes; the caller's at `esp + 260`), with a 114-byte hash at
`HASH`, `s` at `S` and `k` at `K`, and the first ten bytes of
`dom4(0, context)` written at `HASH` before each hash that starts with them
(the blocks of `Impl/Ed448/X86/Shake.lean`):

* `SHAKE256(seed, 114)` into the frame at `S`, whose first 57 bytes, pruned
  in place, are `s` and whose last 57, at `K`, are the prefix;
* `r`, `SHAKE256(dom4(0, C) ‖ prefix ‖ M, 114)` (into the frame at `HASH`)
  reduced modulo `L` (`vg_ed448_scalar_reduce`), into the second half of
  `out`;
* `R = [r]B`, into the first half of `out` (`base`);
* `k`, `SHAKE256(dom4(0, C) ‖ R ‖ A ‖ M, 114)` reduced modulo `L`, at `K`;
* `S = (r + k s) mod L`, into the second half of `out`, over `r`
  (`vg_ed448_scalar_mul_add`, whose output may be one of its inputs);
* the frame from `HASH` on cleared.

Every address depends only on the pointers, the lengths and `esp`.
-/

namespace VG.Impl.Ed448.X86.SignCached

open VG.X86
open VG.Impl.Ed25519.X86.Whole (Value setup zeroWords)
open VG.Impl.Ed448.X86.Shake

/-- Where in the frame the hash (and the header of `dom4`), `s` (then the
prefix after it) and `k` are; `scratch` is the eighth argument. -/
def HASH : Nat := 24
def S : Nat := 138
def K : Nat := 195
def SC : Nat := 7

/-- `SHAKE256(seed, 114)` into the frame at `S`. -/
def seedHash : Prog isa :=
  .seq (zeroState SC) <| .seq (absorb (firstArgs SC (.caller 1 0) (.const 57))) <|
  .seq (pad SC) (squeeze SC S)

/-- `SHAKE256(dom4(0, C) ‖ prefix ‖ M, 114)`, the prefix at `K` and the header
at `HASH`, into the frame at `HASH`. -/
def nonceHash : Prog isa :=
  .seq (zeroState SC) <| .seq (absorb (firstArgs SC (.frame HASH) (.const 10))) <|
  .seq (absorb (nextArgs SC (.caller 3 0) (.caller 4 0))) <|
  .seq (absorb (nextArgs SC (.frame K) (.const 57))) <|
  .seq (absorb (nextArgs SC (.caller 5 0) (.caller 6 0))) <|
  .seq (pad SC) (squeeze SC HASH)

/-- `SHAKE256(dom4(0, C) ‖ R ‖ A ‖ M, 114)`, `R` the first half of `out` and
the header at `HASH`, into the frame at `HASH`. -/
def chalHash : Prog isa :=
  .seq (zeroState SC) <| .seq (absorb (firstArgs SC (.frame HASH) (.const 10))) <|
  .seq (absorb (nextArgs SC (.caller 3 0) (.caller 4 0))) <|
  .seq (absorb (nextArgs SC (.caller 0 0) (.const 57))) <|
  .seq (absorb (nextArgs SC (.caller 2 0) (.const 57))) <|
  .seq (absorb (nextArgs SC (.caller 5 0) (.caller 6 0))) <|
  .seq (pad SC) (squeeze SC HASH)

/-- `scalar_reduce(out + 57, esp + HASH, scratch)`: `r`. -/
def reduceRArgs : List Instr := setup 0 [.caller 0 57, .frame HASH, .caller SC 0]

/-- `scalar_base(out, out + 57, scratch)`: `R`. -/
def baseArgs : List Instr := setup 0 [.caller 0 0, .caller 0 57, .caller SC 0]

/-- `scalar_reduce(esp + K, esp + HASH, scratch)`: `k`. -/
def reduceKArgs : List Instr := setup 0 [.frame K, .frame HASH, .caller SC 0]

/-- `scalar_mul_add(out + 57, r = out + 57, k = esp + K, s = esp + S, scratch)`. -/
def mulAddArgs : List Instr := setup 0 [.caller 0 57, .caller 0 57, .frame K, .frame S, .caller SC 0]

/-- The frame from `HASH` on, cleared. -/
def wipe : List Instr := zeroWords 6 58

def body (base : Prog isa) : Prog isa :=
  .seq seedHash <| .seq (.block (pruneAt S)) <| .seq (.block (hdrAt 4 HASH)) <| .seq nonceHash <|
  .seq (callWith reduceRArgs "vg_ed448_scalar_reduce" Impl.Ed448.X86.scalarReduce) <|
  .seq (callWith baseArgs "vg_ed448_scalar_base" base) <| .seq (.block (hdrAt 4 HASH)) <| .seq chalHash <|
  .seq (callWith reduceKArgs "vg_ed448_scalar_reduce" Impl.Ed448.X86.scalarReduce) <|
  .seq (callWith mulAddArgs "vg_ed448_scalar_mul_add" Impl.Ed448.X86.scalarMulAdd) (.block wipe)

/-- `vg_ed448_sign_cached`, with `base` for `vg_ed448_scalar_base`. -/
def code (base : Prog isa) : Prog isa :=
  .frame (.push (List.replicate 64 .eax)) (body base) (.pop .eax 64)

end VG.Impl.Ed448.X86.SignCached
