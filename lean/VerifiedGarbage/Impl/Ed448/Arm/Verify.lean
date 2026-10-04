import VerifiedGarbage.Impl.Ed448.Arm.Shake
import VerifiedGarbage.Impl.Ed448.Arm.Scalar
import VerifiedGarbage.Impl.Ed448.Arm.VerifyEquation

/-!
# Ed448 verification on ARMv7

`vg_ed448_verify(pk = r0, context = r1, ctxlen = r2, message = r3,
len = [sp], signature = [sp, #4], scratch = [sp, #8]) -> r0`: RFC 8032
§5.2.7.

If `ctxlen ≥ 256` it returns 0 at once: such a context is not an Ed448
context. Otherwise it runs `body` in Ed25519's frame on this target
(`Impl/Ed25519/Arm/Whole`, `wrap 6`): 248 bytes of locals from `sp`, the
first six arguments saved above them, and `r12` and `lr` pushed, above which
the seventh, `scratch`, stays where the caller put it (`.caller 10`, read at
`sp + 288`). In the locals, from `sp`: the outgoing stack arguments, the
first ten bytes of `dom4(0, context)` (`"SigEd448" ‖ 0 ‖ ctxlen`, at `HDR`),
the 114-byte hash (at `HASH`) and the challenge `k` (at `K`). Then:

* `H(dom4(0, context) ‖ R ‖ A ‖ M)` into the frame, with the blocks of
  `Impl/Ed448/Arm/Shake` (the sponge functions `vg_keccak_absorb_scratch`,
  `vg_keccak_pad_scratch` and `vg_keccak_squeeze_scratch`, rate 136, SHAKE's
  suffix), the Keccak state at `scratch` and their working space at
  `scratch + 208`; each absorption after the first starts at the position
  the previous one returned (moved from `r0` to `r2`);
* `k`, the hash reduced modulo `L` (`vg_ed448_scalar_reduce`);
* the result of `vg_ed448_verify_equation(pk, signature, k, scratch)`.

Every address and branch depends only on the pointers and the lengths.
-/

namespace VG.Impl.Ed448.Arm.Verify

open VG.Arm
open VG.Impl.Ed25519.Arm.Whole
open VG.Impl.Ed448.Arm.Shake (hdrAt zeroState firstArgs nextArgs absorb pad squeeze)

/-- Where in the frame the header of `dom4` (16 bytes), the hash and `k` are. -/
def HDR : Nat := 24
def HASH : Nat := 40
def K : Nat := 160

/-- `scratch`, plus `d`: the caller's third stack argument, which `wrap 6`
does not save (`sp + 248 + 4 * 10`). -/
def SC : Nat := 10
def scr (d : Nat) : Value := .caller SC d

/-- The first ten bytes of `dom4(0, context)` at `HDR`
(`Impl/Ed448/Arm/Shake`), from the saved `ctxlen`. -/
def hdr : List Instr := hdrAt 2 HDR

/-- `H(dom4(0, context) ‖ R ‖ A ‖ M)` into the frame at `HASH`. -/
def hash : Prog isa :=
  .seq (zeroState SC) <| .seq (absorb (firstArgs SC (.frame HDR) (.const 10))) <|
  .seq (absorb (nextArgs SC (.caller 1 0) (.caller 2 0))) <|
  .seq (absorb (nextArgs SC (.caller 5 0) (.const 57))) <|
  .seq (absorb (nextArgs SC (.caller 0 0) (.const 57))) <|
  .seq (absorb (nextArgs SC (.caller 3 0) (.caller 4 0))) <|
  .seq (pad SC) (squeeze SC HASH)

/-- `scalar_reduce(out = sp + K, wide = sp + HASH, scratch)`. -/
def reduceArgs : List Instr := setup [(.r0, .frame K), (.r1, .frame HASH), (.r2, scr 0)] []

/-- `verify_equation(pk, signature, sp + K, scratch)`. -/
def equationArgs : List Instr :=
  setup [(.r0, .caller 0 0), (.r1, .caller 5 0), (.r2, .frame K), (.r3, scr 0)] []

def body : Prog isa :=
  .seq (.block hdr) <| .seq hash <|
  .seq (callWith reduceArgs "vg_ed448_scalar_reduce" Impl.Ed448.Arm.scalarReduce)
    (callWith equationArgs "vg_ed448_verify_equation" Impl.Ed448.Arm.verifyEquation)

/-- `ctxlen < 256`: Z set exactly when `ctxlen >> 8 = 0`. -/
def check : List Instr := [.mov .r12 (.shifted .r2 .lsr 8), .cmp .r12 (.imm 0)]

/-- `vg_ed448_verify`. -/
def code : Prog isa := .seq (.block check) (.ite .eq (wrap 6 body) (.block [.movw .r0 0]))

end VG.Impl.Ed448.Arm.Verify
