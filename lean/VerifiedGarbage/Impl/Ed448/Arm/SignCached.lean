import VerifiedGarbage.Impl.Ed448.Arm.Shake
import VerifiedGarbage.Impl.Ed448.Arm.Scalar

/-!
# Ed448 signing with a cached public key on ARMv7

`vg_ed448_sign_cached(out = r0, seed = r1, pk = r2, context = r3,
ctxlen = [sp], message = [sp, #4], len = [sp, #8], scratch = [sp, #12])`:
RFC 8032 §5.2.6, with the public key `A` given (and `ctxlen ≤ 255`).

It runs `body` in Ed25519's frame on this target (`Impl/Ed25519/Arm/Whole`,
`wrap 6`): 248 bytes of locals from `sp`, the first six arguments saved
above them, and `r12` and `lr` pushed, above which `len` and `scratch` stay
where the caller put them (`.caller 10` and `.caller 11`). The locals hold,
from `sp`: the outgoing stack arguments (8 bytes), a 114-byte hash (at
`HASH`), the secret scalar `s` (at `S`, 57 bytes), the challenge `k` (at
`K`, 57 bytes) and the first ten bytes of `dom4(0, context)` (at `HDR`).
Then (the hashes with the blocks of `Impl/Ed448/Arm/Shake`):

* `SHAKE256(seed, 114)` into the frame at `S`, whose first 57 bytes, pruned
  in place, are `s` and whose last 57, at `K`, are the prefix;
* `r`, `SHAKE256(dom4(0, C) ‖ prefix ‖ M, 114)` (into the frame at `HASH`)
  reduced modulo `L` (`vg_ed448_scalar_reduce`), into the second half of
  `out`;
* `R = [r]B`, into the first half of `out` (`vg_ed448_scalar_base`);
* `k`, `SHAKE256(dom4(0, C) ‖ R ‖ A ‖ M, 114)` reduced modulo `L`, at `K`;
* `S = (r + k s) mod L`, into the second half of `out`, over `r`
  (`vg_ed448_scalar_mul_add`, which allows its output to be an input);
* the locals from `HASH` on cleared.

Every address depends only on the pointers, the lengths and `sp`.
-/

namespace VG.Impl.Ed448.Arm.SignCached

open VG.Arm
open VG.Impl.Ed25519.Arm.Whole
open VG.Impl.Ed448.Arm.Shake

/-- Where in the frame the hash, `s` (then the prefix after it), `k` and the
header of `dom4` are. -/
def HASH : Nat := 8
def S : Nat := 122
def K : Nat := 179
def HDR : Nat := 236

/-- `scratch` and `len`: the caller's fourth and third stack arguments, which
`wrap 6` does not save (`sp + 248 + 4 * 11` and `sp + 248 + 4 * 10`). -/
def SC : Nat := 11
def LEN : Value := .caller 10 0

/-- `SHAKE256(seed, 114)` into the frame at `S`. -/
def seedHash : Prog isa :=
  .seq (zeroState SC) <| .seq (absorb (firstArgs SC (.caller 1 0) (.const 57))) <|
  .seq (pad SC) (squeeze SC S)

/-- `s`: pruning (`Spec.Ed448.prune`) in place on the first 57 bytes of the
hash at `S`, from `r12 = sp + S`. -/
def prune : Prog isa := .seq (.block [.addSp .r12 S]) (.block PublicKey.pruneOps)

/-- `SHAKE256(dom4(0, C) ‖ prefix ‖ M, 114)`, the prefix at `K`, into the frame
at `HASH`. -/
def nonceHash : Prog isa :=
  .seq (zeroState SC) <| .seq (absorb (firstArgs SC (.frame HDR) (.const 10))) <|
  .seq (absorb (nextArgs SC (.caller 3 0) (.caller 4 0))) <|
  .seq (absorb (nextArgs SC (.frame K) (.const 57))) <|
  .seq (absorb (nextArgs SC (.caller 5 0) LEN)) <|
  .seq (pad SC) (squeeze SC HASH)

/-- `SHAKE256(dom4(0, C) ‖ R ‖ A ‖ M, 114)`, `R` the first half of `out`,
into the frame at `HASH`. -/
def chalHash : Prog isa :=
  .seq (zeroState SC) <| .seq (absorb (firstArgs SC (.frame HDR) (.const 10))) <|
  .seq (absorb (nextArgs SC (.caller 3 0) (.caller 4 0))) <|
  .seq (absorb (nextArgs SC (.caller 0 0) (.const 57))) <|
  .seq (absorb (nextArgs SC (.caller 2 0) (.const 57))) <|
  .seq (absorb (nextArgs SC (.caller 5 0) LEN)) <|
  .seq (pad SC) (squeeze SC HASH)

/-- `scalar_reduce(out + 57, sp + HASH, scratch)`: `r`. -/
def reduceRArgs : List Instr := setup [(.r0, .caller 0 57), (.r1, .frame HASH), (.r2, .caller SC 0)] []

/-- `scalar_base(out, out + 57, scratch)`: `R`. -/
def baseArgs : List Instr := setup [(.r0, .caller 0 0), (.r1, .caller 0 57), (.r2, .caller SC 0)] []

/-- `scalar_reduce(sp + K, sp + HASH, scratch)`: `k`. -/
def reduceKArgs : List Instr := setup [(.r0, .frame K), (.r1, .frame HASH), (.r2, .caller SC 0)] []

/-- `scalar_mul_add(out + 57, r = out + 57, k = sp + K, s = sp + S, scratch)`. -/
def mulAddArgs : List Instr :=
  setup [(.r0, .caller 0 57), (.r1, .caller 0 57), (.r2, .frame K), (.r3, .frame S)] [.caller SC 0]

/-- The locals from `HASH` on, cleared. -/
def wipe : List Instr := zeroWords 2 60

def body : Prog isa :=
  .seq (.block (hdrAt 4 HDR)) <| .seq seedHash <| .seq prune <| .seq nonceHash <|
  .seq (callWith reduceRArgs "vg_ed448_scalar_reduce" Impl.Ed448.Arm.scalarReduce) <|
  .seq (callWith baseArgs "vg_ed448_scalar_base" Impl.Ed448.Arm.scalarBase) <| .seq chalHash <|
  .seq (callWith reduceKArgs "vg_ed448_scalar_reduce" Impl.Ed448.Arm.scalarReduce) <|
  .seq (callWith mulAddArgs "vg_ed448_scalar_mul_add" Impl.Ed448.Arm.scalarMulAdd) (.block wipe)

/-- `vg_ed448_sign_cached`. -/
def code : Prog isa := wrap 6 body

end VG.Impl.Ed448.Arm.SignCached
