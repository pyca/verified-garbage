module

public import VerifiedGarbage.Impl.Dsa.Arm.Entry

/-! # DSA domain checking and key derivation on ARMv7

Both reuse the signer's entry, public-width dispatch, shape check and
arithmetic. A domain has one generator, so its range and subgroup power are
checked once, not by the public-key validator with g as y. Derivation then
checks x's range, computes y = g^x mod p and checks y's range; the identity
`(g^x)^q = (g^q)^x` supplies y's subgroup check. Secret-dependent checks
accumulate the mask; the key is copied out under it.
-/

@[expose] public section
namespace VG.Impl.Dsa.Arm.Generate
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Impl.Dsa.Layout

/-- `1 < g < p` and `q ∣ p - 1`. -/
def domain (pLen qLen : Nat) : Prog isa := Core.sequence [
  Validate.range pLen .p (.input .g) true,
  Validate.minus pLen .p 1 t,
  Core.reduce qLen (.imm pLen) (.local t) u,
  Validate.zero qLen (.local u)]

/-- `g^q = 1 mod p`. -/
def subgroup (pLen qLen : Nat) : Prog isa :=
  .seq (Core.power pLen qLen .p (.input .g) (.input .q) t) (Validate.isOne pLen (.local t))

def parameters (pLen qLen : Nat) : Prog isa := .seq (domain pLen qLen) (subgroup pLen qLen)

/-- Try the supported widths in turn; the last continuation is unreachable
for lengths the contracts accept. -/
def dispatch (sized : Nat → Nat → Prog isa) : List (Nat × Nat) → Prog isa
  | [] => .block [.mov .r0 (.imm 0)]
  | (pLen, qLen) :: rest =>
    .seq (Entry.widthMatch pLen qLen) (.ite .eq (sized pLen qLen) (dispatch sized rest))

def widths : List (Nat × Nat) := [(128, 20), (256, 28), (256, 32), (384, 32), (256, 20)]

/-- The shape check also clamps a digest length, which generation never
reads: it is given the public p_len. -/
def checkArguments : List (Entry.Arg × Field) :=
  [(.reg .r0, .p), (.reg .r2, .pLen), (.reg .r3, .qLen), (.reg .r2, .digestLen)]

/-- `vg_dsa_check_parameters(params, params_len, p_len, q_len, scratch,
scratch_len)`. -/
def checkEntry : List Instr :=
  Entry.openScratch 0 ++ checkArguments.flatMap Entry.saveArgument ++ Entry.keyPointers

def checkSized (pLen qLen : Nat) : Prog isa :=
  .seq (Shape.check pLen qLen)
    (.ite .eq (.block [.mov .r0 (.imm 0)]) (.seq (parameters pLen qLen) (.block SignVerify.result)))

def checkParameters : Prog isa := Core.sequence [
  .block checkEntry, dispatch checkSized widths, .block Entry.restore]

/-- The supplied x is kept at the signer's nonce field. -/
def deriveArguments : List (Entry.Arg × Field) :=
  [(.reg .r0, .out), (.reg .r2, .p), (.stack 0, .pLen), (.stack 1, .nonce), (.stack 2, .qLen),
    (.stack 0, .digestLen)]

/-- `vg_dsa_derive_key(out, out_len, params, params_len, p_len, x, q_len,
scratch, scratch_len)`. -/
def deriveEntry : List Instr :=
  Entry.openScratch 3 ++ deriveArguments.flatMap Entry.saveArgument ++ Entry.keyPointers

/-- The domain's checks, x's range, y = g^x mod p and y's range. -/
def deriveCompute (pLen qLen : Nat) : Prog isa := Core.sequence [
  parameters pLen qLen,
  Validate.range qLen .q (.input .nonce),
  Core.power pLen qLen .p (.input .g) (.input .nonce) t2,
  Validate.range pLen .p (.local t2) true]

def copyStep : List Instr :=
  [.ldrb .r0 .r1 0, .dp .and .r0 .r0 (.reg .r3), .strb .r0 .r10 0,
    .dp .add .r1 .r1 (.imm 1), .dp .add .r10 .r10 (.imm 1), .subs .r2 .r2 (.imm 1)]

/-- Copy `r2 > 0` bytes from `r1` to `r10`, each and-ed with the mask `r3`. -/
def copyMasked : Prog isa := .loop (.block copyStep) .ne

def copyFrom (len : Nat) : Prog isa := .seq (.block [.movw .r2 (BitVec.ofNat 16 len)]) copyMasked

/-- The output is p||q||g||y||x, under the mask; `r10` runs on through the
three copies. Every pointer is loaded before the first store. -/
def writeKey (pLen qLen : Nat) : Prog isa := Core.sequence [
  .block [.ldr .r3 .r12 (Layout.field .mask), .ldr .r10 .r12 (Layout.field .out),
    .ldr .r1 .r12 (Layout.field .p), .ldr .r4 .r12 (Layout.field .nonce)],
  copyFrom (2 * pLen + qLen), .block (ptr .r1 t2), copyFrom pLen, .block [.mov .r1 (.reg .r4)], copyFrom qLen,
  .block SignVerify.result]

/-- A rejected shape zeros the whole output. -/
def deriveFailure (pLen qLen : Nat) : Prog isa := Core.sequence [
  .block [.ldr .r11 .r12 (Layout.field .out), .movw .r4 (BitVec.ofNat 16 (3 * pLen + 2 * qLen)),
    .dp .add .lr .r11 (.reg .r4), .mov .r4 (.imm 0)],
  .loop (.block [.strb .r4 .r11 0, .dp .add .r11 .r11 (.imm 1), .cmp .r11 (.reg .lr)]) .ne,
  .block [.mov .r0 (.imm 0)]]

def deriveSized (pLen qLen : Nat) : Prog isa :=
  .seq (Shape.check pLen qLen)
    (.ite .eq (deriveFailure pLen qLen) (.seq (deriveCompute pLen qLen) (writeKey pLen qLen)))

def deriveKey : Prog isa := Core.sequence [
  .block deriveEntry, dispatch deriveSized widths, .block Entry.restore]

end VG.Impl.Dsa.Arm.Generate
