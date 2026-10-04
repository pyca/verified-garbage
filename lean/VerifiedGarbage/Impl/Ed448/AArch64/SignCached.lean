import VerifiedGarbage.Impl.Ed448.AArch64.Whole
import VerifiedGarbage.Impl.Ed448.AArch64.Scalar
import VerifiedGarbage.Impl.Ed448.AArch64.ScalarBase

/-!
# Ed448 signing with a cached public key on AArch64

`vg_ed448_sign_cached(out = x0, seed = x1, pk = x2, context = x3, ctxlen = x4,
message = x5, len = x6, scratch = x7)`: RFC 8032 §5.2.6, with the public key
`A` given (and `ctxlen ≤ 255`), with the permutation `c`.

In the frame of the complete operations (`Impl.Ed25519.AArch64.Whole.wrap`,
which saves `x0`–`x5`), with `len` and `scratch` kept in the locals at 200
and 208 and the first ten bytes of `dom4(0, context)` at 0:

* `SHAKE256(seed, 114)` into the locals at 16, whose first 57 bytes, pruned,
  are `s`, at 136 (`pruneAt`), and whose last 57 are the prefix;
* `r`, `SHAKE256(dom4(0, C) ‖ prefix ‖ M, 114)` (into the locals at 16)
  reduced modulo `L` (`vg_ed448_scalar_reduce`), into the second half of
  `out`;
* `R = [r]B`, into the first half of `out` (`vg_ed448_scalar_base`);
* `k`, `SHAKE256(dom4(0, C) ‖ R ‖ A ‖ M, 114)` reduced modulo `L`, at 16;
* `S = (r + k s) mod L`, into the second half of `out`, over `r`
  (`vg_ed448_scalar_mul_add`);
* the locals from 16 to 200 (the hash, `k` and `s`) cleared.

The hashes use the sponge functions, each absorption starting at the
position the previous one returned (in `x0`), with the Keccak state at
`scratch` and their working space at `scratch + 256`. Every address and
branch depends only on the pointers and the lengths.
-/

namespace VG.Impl.Ed448.AArch64.SignCached

open VG.AArch64
open VG.Impl.Ed25519.AArch64.Whole (Value wrap zeroWords)
open VG.Impl.Ed448.AArch64.Whole (Src callS keep hdr zeroSt kabs kpad ksqz pruneAt)

/-- Where the locals are: the header of `dom4`, the hash (then `k`), `s`,
`len` and `scratch`. -/
def fHdr : Nat := 0
def fH : Nat := 16
def fS : Nat := 136
def fLen : Nat := 200
def fScr : Nat := 208

/-- The saved arguments, and `len`. -/
def aOut : Src := .val (.caller 0 0)
def aR : Src := .val (.caller 0 57)
def aSeed : Src := .val (.caller 1 0)
def aPk : Src := .val (.caller 2 0)
def aCtx : Src := .val (.caller 3 0)
def aCtxLen : Src := .val (.caller 4 0)
def aMsg : Src := .val (.caller 5 0)
def aLen : Src := .loc fLen 0

/-- `len` and `scratch` kept, and the header of `dom4`. -/
def entry : List Instr := keep .x6 fLen ++ keep .x7 fScr ++ hdr fHdr (.caller 4 0)

/-- `SHAKE256(seed, 114)` into the locals at `fH`. -/
def seedHash (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .seq (zeroSt fScr) <|
  .seq (kabs c fScr aSeed (.val (.const 57)) (.val (.const 0))) <|
  .seq (kpad c fScr .ret) (ksqz c fScr (.val (.frame fH)))

/-- `s`, the first half of the hash pruned, at `fS`. -/
def prune : List Instr := pruneAt fH fS

/-- `SHAKE256(dom4(0, C) ‖ prefix ‖ M, 114)` into the locals at `fH`. -/
def nonceHash (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .seq (zeroSt fScr) <|
  .seq (kabs c fScr (.val (.frame fHdr)) (.val (.const 10)) (.val (.const 0))) <|
  .seq (kabs c fScr aCtx aCtxLen .ret) <|
  .seq (kabs c fScr (.val (.frame (fH + 57))) (.val (.const 57)) .ret) <|
  .seq (kabs c fScr aMsg aLen .ret) <|
  .seq (kpad c fScr .ret) (ksqz c fScr (.val (.frame fH)))

/-- `SHAKE256(dom4(0, C) ‖ R ‖ A ‖ M, 114)` into the locals at `fH`. -/
def chalHash (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .seq (zeroSt fScr) <|
  .seq (kabs c fScr (.val (.frame fHdr)) (.val (.const 10)) (.val (.const 0))) <|
  .seq (kabs c fScr aCtx aCtxLen .ret) <|
  .seq (kabs c fScr aOut (.val (.const 57)) .ret) <|
  .seq (kabs c fScr aPk (.val (.const 57)) .ret) <|
  .seq (kabs c fScr aMsg aLen .ret) <|
  .seq (kpad c fScr .ret) (ksqz c fScr (.val (.frame fH)))

def reduceRArgs : List (Reg × Src) := [(.x0, aR), (.x1, .val (.frame fH)), (.x2, .loc fScr 0)]
def baseArgs : List (Reg × Src) := [(.x0, aOut), (.x1, aR), (.x2, .loc fScr 0)]
def reduceKArgs : List (Reg × Src) := [(.x0, .val (.frame fH)), (.x1, .val (.frame fH)), (.x2, .loc fScr 0)]
def mulAddArgs : List (Reg × Src) :=
  [(.x0, aR), (.x1, aR), (.x2, .val (.frame fH)), (.x3, .val (.frame fS)), (.x4, .loc fScr 0)]

/-- The hash, `k` and `s` cleared. -/
def wipe : List Instr := zeroWords 2 23

def body (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .seq (.block entry) <| .seq (seedHash c) <| .seq (.block prune) <| .seq (nonceHash c) <|
  .seq (callS reduceRArgs "vg_ed448_scalar_reduce" scalarReduce) <|
  .seq (callS baseArgs "vg_ed448_scalar_base" scalarBase) <| .seq (chalHash c) <|
  .seq (callS reduceKArgs "vg_ed448_scalar_reduce" scalarReduce) <|
  .seq (callS mulAddArgs "vg_ed448_scalar_mul_add" scalarMulAdd) (.block wipe)

/-- `vg_ed448_sign_cached`, with the permutation `c`. -/
def signCachedWith (c : Impl.Sha3.AArch64.Callee) : Prog isa := wrap (body c)

end VG.Impl.Ed448.AArch64.SignCached
