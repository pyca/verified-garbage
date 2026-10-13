module

public import VerifiedGarbage.Impl.Dsa.AArch64.Core

/-! # DSA input checks and result masks on AArch64

As x86-64's (`Impl/Dsa/X86_64/Checks.lean`): all checks accumulate an
all-ones/zero mask. Only the initial checks of public modulus sizes and
oddness branch before arithmetic. In particular, private-key consistency and
signature scalar checks never skip arithmetic. A comparison's carry becomes
a mask by `csel` (`Crt.borrowMask`, `carryMask`): the model branches only on
whether a register is zero.
-/

@[expose] public section

namespace VG.Impl.Dsa.AArch64.Checks

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.Layout

/-- Intersect the result mask with `x15`, at the outer workspace. -/
def accumulate : List Instr :=
  [Core.field .x3 .mask, .logic .and .x .x15 .x15 .x3, .str .x .x15 .x0 Field.mask.offset]

/-- `x4 := 0 - 1`, and `x15 :=` all ones on a carry, 0 otherwise; `x7 = 0`. -/
def carryMask : List Instr := [.subImm .x .x4 .x7 1, .csel .x .x15 .x4 .x7]

/-- `x15 :=` all ones iff `x3` is zero: the borrow of `x3 - 1`. -/
def zeroMask : List Instr := [movi .x7 0, movi .x4 1, .subs .x .x3 .x3 .x4] ++ Crt.borrowMask

/-- `x15 :=` all ones iff `x3 ≥ n`: the carry of `x3 - n`. -/
def atLeast (n : Nat) : List Instr := [movi .x7 0, movi .x4 n, .subs .x .x3 .x3 .x4] ++ carryMask

/-- Record a nonzero byte only if the scan has not found one yet. -/
def significantChoose : Prog isa :=
  .ite (.zero .x .x8)
    (.ite (.zero .x .x3) (.block []) (.block [mov .x8 .x2, mov .x9 .x3]))
    (.block [])

/-- One public byte of the actual-width scan. -/
def significantByte : Prog isa := seqs [
  .block [.ldrb .x3 .x1 0],
  significantChoose,
  .block [.addImm .x .x1 .x1 1, .subImm .x .x2 .x2 1]]

/-- Read all bytes, returning the number of bytes from the first nonzero
byte in `x8` and that byte in `x9`. Both are zero for an all-zero input.
Input pointer `x1`, positive byte length `x2`. -/
def significant : Prog isa := seqs [
  .block [movi .x8 0, movi .x9 0],
  .loop significantByte (.nonzero .x .x2)]

/-- Equality of `x8` with a public immediate, as a mask in `x15`. -/
def widthMask (n : Nat) : List Instr := [movi .x4 n, .logic .eor .x .x3 .x8 .x4] ++ zeroMask

/-- The supported subgroup widths for the modulus width in `x10`, as a mask
in `x15`; the subgroup's width is in `x8`. -/
def widthChoice : Prog isa :=
  .seq (.block [.subImm .x .x5 .x10 128])
    (.ite (.zero .x .x5) (.block (widthMask 20))
      (.seq (.block [.subImm .x .x5 .x10 256])
        (.ite (.zero .x .x5)
          (.block (widthMask 28 ++ ([mov .x11 .x15] : List Instr) ++ widthMask 32 ++
            ([.logic .orr .x .x15 .x15 .x11] : List Instr)))
          (.seq (.block [.subImm .x .x5 .x10 384])
            (.ite (.zero .x .x5) (.block (widthMask 32)) (.block [movi .x15 0]))))))

/-- Check supported actual bit lengths (not just allocated byte widths),
public modulus oddness, and compute the digest-prefix length. `x3` on exit
is the mask, zero iff the domain is rejected. Public fields p and q remain
unchanged. -/
def domainShape : Prog isa := seqs [
  .block [Core.field .x1 .p, Core.field .x2 .pLen],
  significant,
  .block (([sth .x8 22, mov .x3 .x9] : List Instr) ++ atLeast 128 ++
    ([.str .x .x15 .x0 Field.mask.offset, Core.field .x1 .q, Core.field .x2 .qLen] : List Instr)),
  significant,
  .block (([.str .x .x8 .x0 Field.digestPrefixLen.offset, mov .x3 .x9] : List Instr) ++ atLeast 128 ++
    accumulate ++ ([ldh .x10 22] : List Instr)),
  widthChoice,
  .block (accumulate ++
    ([Core.field .x1 .p, Core.field .x2 .pLen, .add .x .x1 .x1 .x2, .subImm .x .x1 .x1 1, .ldrb .x3 .x1 0,
      Core.field .x1 .q, Core.field .x2 .qLen, .add .x .x1 .x1 .x2, .subImm .x .x1 .x1 1, .ldrb .x4 .x1 0,
      .logic .and .x .x3 .x3 .x4, movi .x4 1, .logic .and .x .x3 .x3 .x4,
      movi .x7 0, .sub .x .x15 .x7 .x3] : List Instr) ++ accumulate ++
    ([Core.field .x3 .digestLen, Core.field .x5 .digestPrefixLen,
      .subs .x .x4 .x3 .x5, .csel .x .x3 .x5 .x3,
      .str .x .x3 .x0 Field.digestPrefixLen.offset, Core.field .x3 .mask] : List Instr))]

/-- Intersect the mask with an equality of positive, equal-length byte
strings. `unequal` instead requires their inequality. -/
def equal (a b : Operand) (unequal : Bool := false) : Prog isa := seqs [
  .block (Core.pointer a.pointer ++ ([mov .x1 .x3] : List Instr) ++ Core.pointer b.pointer ++
    ([mov .x2 .x3, Core.field .x9 a.length, movi .x8 0] : List Instr)),
  .loop (.block [.ldrb .x3 .x1 0, .ldrb .x4 .x2 0, .logic .eor .x .x3 .x3 .x4,
    .logic .orr .x .x8 .x8 .x3, .addImm .x .x1 .x1 1, .addImm .x .x2 .x2 1, .subImm .x .x9 .x9 1])
    (.nonzero .x .x9),
  .block (([mov .x3 .x8] : List Instr) ++ zeroMask ++
    (if unequal then [.logic .eor .x .x15 .x15 .x4] else []) ++ accumulate)]

/-- Intersect the mask with whether a positive-length byte string is zero
(or nonzero). -/
def zero (a : Operand) (nonzero : Bool := false) : Prog isa := seqs [
  .block (Core.pointer a.pointer ++ ([mov .x1 .x3, Core.field .x9 a.length, movi .x8 0] : List Instr)),
  .loop (.block [.ldrb .x3 .x1 0, .logic .orr .x .x8 .x8 .x3,
    .addImm .x .x1 .x1 1, .subImm .x .x9 .x9 1]) (.nonzero .x .x9),
  .block (([mov .x3 .x8] : List Instr) ++ zeroMask ++
    (if nonzero then [.logic .eor .x .x15 .x15 .x4] else []) ++ accumulate)]

/-- In a child workspace: array aX is below the modulus and at least 1
(or at least 2 for g and y). The mask into `x15`. -/
def rangeMask (aboveOne : Bool) : Prog isa := seqs [
  .block [ldh .x12 sW, ldh .x16 (sArr aX), ldh .x17 (sArr aN), movi .x7 0, mov .x14 .x12,
    .subs .x .x3 .x7 .x7],
  cmpLoop,
  .block (Crt.borrowMask ++ ([mov .x11 .x15, ldh .x16 (sArr aX), ld .x9 .x16] : List Instr) ++
    (if aboveOne then [.lsr .x .x9 .x9 1] else []) ++
    ([next .x16, .subImm .x .x14 .x12 1] : List Instr)),
  countLoop .x14 [ld .x3 .x16, .logic .orr .x .x9 .x9 .x3, next .x16],
  .block (([mov .x3 .x9] : List Instr) ++ zeroMask ++
    ([.logic .eor .x .x15 .x15 .x4, .logic .and .x .x15 .x15 .x11] : List Instr))]

def range (ws : Nat) (a : Operand) (aboveOne : Bool := false) : Prog isa := seqs [
  .block (Core.operand arg argLen a ++ Core.enter ws), Arithmetic.load aX arg argLen,
  rangeMask aboveOne,
  .block (([Crt.leave] : List Instr) ++ accumulate)]

/-- Store modulus minus a small positive value. Called only after domain
shape checks, so subtraction cannot underflow. -/
def modulusMinus (ws : Nat) (amount : Nat) (output : Operand) : Prog isa :=
  seqs ([.block (Core.operand result resultLen output ++ Core.enter ws ++
    ([ldh .x12 sW, ldh .x16 (sArr aN), ldh .x17 (sArr aY), movi .x7 0, movi .x4 amount,
      ld .x3 .x16, .subs .x .x3 .x3 .x4, st .x3 .x17, next .x16, next .x17, .subImm .x .x14 .x12 1] : List Instr)),
    countLoop .x14 [ld .x3 .x16, .sbcs .x .x3 .x3 .x7, st .x3 .x17, next .x16, next .x17]] ++ Core.finish)

/-- Compare a child result with the ordinary number 1, accumulating its
mask after returning to the parent. -/
def isOne (ws : Nat) (value : Operand) : Prog isa := seqs [
  .block (Core.operand arg argLen value ++ Core.enter ws),
  Arithmetic.load aX arg argLen,
  .block [ldh .x12 sW, ldh .x16 (sArr aX), ld .x9 .x16, movi .x4 1, .logic .eor .x .x9 .x9 .x4,
    next .x16, .subImm .x .x14 .x12 1],
  countLoop .x14 [ld .x3 .x16, .logic .orr .x .x9 .x9 .x3, next .x16],
  .block (([mov .x3 .x9] : List Instr) ++ zeroMask ++ ([Crt.leave] : List Instr) ++ accumulate)]

/-- Range and domain checks, then both subgroup memberships, independently. -/
def publicKey (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  range pWorkspace Core.generator true, range pWorkspace Core.publicValue true,
  modulusMinus pWorkspace 1 (Core.element t),
  Core.reduce mul (Core.element t) (Core.scalar u), zero (Core.scalar u),
  modulusMinus qWorkspace 2 (Core.scalar qMinusTwo),
  Core.pow mul pWorkspace Core.generator ⟨.input .q, .qLen⟩ (Core.element t),
  isOne pWorkspace (Core.element t),
  Core.pow mul pWorkspace Core.publicValue ⟨.input .q, .qLen⟩ (Core.element t),
  isOne pWorkspace (Core.element t)]

/-- Private/public key consistency and nonce rejection masks. -/
def privateKey (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  range qWorkspace Core.privateScalar, range qWorkspace Core.nonce,
  Core.pow mul pWorkspace Core.generator Core.privateScalar (Core.element t),
  equal (Core.element t) Core.publicValue]

end VG.Impl.Dsa.AArch64.Checks
