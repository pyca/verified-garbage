module

public import VerifiedGarbage.Impl.Ed448.X86.Shake
public import VerifiedGarbage.Impl.Ed448.X86.Scalar

/-!
# Ed448 verification on x86 (32-bit)

`vg_ed448_verify(pk, context, ctxlen, message, len, signature, scratch) ->
eax`, cdecl, with the verification equation `eq`
(`vg_ed448_verify_equation`, a parameter: the proof holds for any code
meeting its contract): RFC 8032 §5.2.7.

If `ctxlen ≥ 256` it returns 0 at once: such a context is not an Ed448
context. Otherwise, in Ed25519's frame on this target (64 words pushed, the
outgoing arguments at `esp`, the caller's at `esp + 260`), with the first
ten bytes of `dom4(0, context)` at `HDR`, the hash at `HASH` and `k` at `K`:

* `H(dom4(0, context) ‖ R ‖ A ‖ M)` into the frame, with the blocks of
  `Impl/Ed448/X86/Shake.lean`; each absorption after the first starts at the
  position the previous one returned;
* `k`, the hash reduced modulo `L` (`vg_ed448_scalar_reduce`);
* the result of `eq(pk, signature, k, scratch)`, kept in `eax` through the
  frame's pop (into `edx`).

Every address and branch depends only on the pointers and the lengths.
-/

@[expose] public section

namespace VG.Impl.Ed448.X86.Verify

open VG.X86
open VG.Impl.Ed25519.X86.Whole (Value setup)
open VG.Impl.Ed448.X86.Shake

/-- Where in the frame the header of `dom4` (12 bytes), the hash and `k` are;
`scratch` is the seventh argument. -/
def HDR : Nat := 24
def HASH : Nat := 40
def K : Nat := 160
def SC : Nat := 6

/-- `H(dom4(0, context) ‖ R ‖ A ‖ M)` into the frame at `HASH`. -/
def hash : Prog isa :=
  .seq (zeroState SC) <| .seq (absorb (firstArgs SC (.frame HDR) (.const 10))) <|
  .seq (absorb (nextArgs SC (.caller 1 0) (.caller 2 0))) <|
  .seq (absorb (nextArgs SC (.caller 5 0) (.const 57))) <|
  .seq (absorb (nextArgs SC (.caller 0 0) (.const 57))) <|
  .seq (absorb (nextArgs SC (.caller 3 0) (.caller 4 0))) <|
  .seq (pad SC) (squeeze SC HASH)

/-- `scalar_reduce(esp + K, esp + HASH, scratch)`. -/
def reduceArgs : List Instr := setup 0 [.frame K, .frame HASH, .caller SC 0]

/-- `verify_equation(pk, signature, esp + K, scratch)`. -/
def equationArgs : List Instr := setup 0 [.caller 0 0, .caller 5 0, .frame K, .caller SC 0]

def body (eq : Prog isa) : Prog isa :=
  .seq (.block (hdrAt 2 HDR)) <| .seq hash <|
  .seq (callWith reduceArgs "vg_ed448_scalar_reduce" Impl.Ed448.X86.scalarReduce)
    (callWith equationArgs "vg_ed448_verify_equation" eq)

/-- `ctxlen < 256`: ZF set exactly when `ctxlen >> 8 = 0`. -/
def check : List Instr :=
  [.mov .eax (.mem ⟨.esp, 12⟩), .shift .shr .eax 8, .alu .cmp .eax (.imm 0)]

/-- `vg_ed448_verify`, with `eq` for `vg_ed448_verify_equation`. -/
def code (eq : Prog isa) : Prog isa :=
  .seq (.block check) <| .ite .e
    (.frame (.push (List.replicate 64 .eax)) (body eq) (.pop .edx 64))
    (.block [.mov .eax (.imm 0)])

end VG.Impl.Ed448.X86.Verify
