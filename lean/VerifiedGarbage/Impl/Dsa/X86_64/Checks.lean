module

public import VerifiedGarbage.Impl.Dsa.X86_64.Core

/-! # DSA input checks and result masks

All checks accumulate an all-ones/zero mask. Only the initial checks of
public modulus sizes and oddness branch before arithmetic. In particular,
private-key consistency and signature scalar checks never skip arithmetic.
-/

@[expose] public section

namespace VG.Impl.Dsa.X86_64.Checks

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.Layout

/-- Intersect the result mask with rax, at the outer workspace. -/
def accumulate : List Instr :=
  [.alu .and .rax (.mem (Core.field .mask)), .store (Core.field .mask) .rax]

/-- Record a nonzero byte only if the scan has not found one yet. -/
def significantChoose : Prog isa :=
  .ite .e
    (.seq (.block [.alu .test .rax (.reg .rax)])
      (.ite .ne (.block [.mov .r8 (.reg .rcx), .mov .r9 (.reg .rax)]) (.block [])))
    (.block [])

/-- One public byte of the actual-width scan. -/
def significantByte : Prog isa := seqs [
  .block [.movzx8 .rax (at0 .rsi), .alu .test .r8 (.reg .r8)],
  significantChoose,
  .block [.alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]]

/-- Read all bytes, returning the number of bytes from the first nonzero
byte in r8 and that byte in r9. Both are zero for an all-zero input.
Input pointer rsi, positive byte length rcx. -/
def significant : Prog isa := seqs [
  .block [.mov32 .r8 (.imm 0), .mov32 .r9 (.imm 0)],
  .loop significantByte .ne]

/-- Equality of r8 with a public immediate, as a mask in rax. -/
def widthMask (n : Nat) : List Instr :=
  [.mov .rax (.reg .r8), .alu .xor .rax (.imm (BitVec.ofNat 32 n)),
    .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax)]

/-- All imported subgroup widths for a 2048-bit modulus, including legacy 160-bit q. -/
def width2048 : List Instr :=
  widthMask 28 ++ ([.mov .r10 (.reg .rax)] : List Instr) ++ widthMask 32 ++
    ([.alu .or .rax (.reg .r10)] : List Instr) ++ ([.mov .r10 (.reg .rax)] : List Instr) ++ widthMask 20 ++
    ([.alu .or .rax (.reg .r10)] : List Instr)

/-- Check supported actual bit lengths (not just allocated byte widths),
public modulus oddness, and compute the digest-prefix length. ZF on exit
is set iff the mask is zero. Public fields p and q remain unchanged. -/
def domainShape : Prog isa := seqs [
  .block [.mov .rsi (.mem (Core.field .p)), .mov .rcx (.mem (Core.field .pLen))],
  significant,
  .block [.store (hdr 22) .r8, .alu .cmp .r9 (.imm 128), .alu .sbb .rax (.reg .rax),
    .alu .xor .rax (.imm (-1)), .store (Core.field .mask) .rax,
    .mov .rsi (.mem (Core.field .q)), .mov .rcx (.mem (Core.field .qLen))],
  significant,
  .block (([.store (Core.field .digestPrefixLen) .r8,
    .alu .cmp .r9 (.imm 128), .alu .sbb .rax (.reg .rax), .alu .xor .rax (.imm (-1))] : List Instr) ++ accumulate ++
    ([.mov .rdx (.mem (hdr 22)), .alu .cmp .rdx (.imm 128)] : List Instr)),
  .ite .e (.block (widthMask 20))
    (.seq (.block [.alu .cmp .rdx (.imm 256)])
      (.ite .e
        (.block width2048)
        (.seq (.block [.alu .cmp .rdx (.imm 384)])
          (.ite .e (.block (widthMask 32)) (.block [.mov32 .rax (.imm 0)]))))),
  .block (accumulate ++
    ([.mov .rsi (.mem (Core.field .p)), .mov .rcx (.mem (Core.field .pLen)),
      .movzx8 .rax { base := .rsi, index := some .rcx, disp := -1 },
      .mov .rsi (.mem (Core.field .q)), .mov .rcx (.mem (Core.field .qLen)),
      .movzx8 .rdx { base := .rsi, index := some .rcx, disp := -1 },
      .alu .and .rax (.reg .rdx), .alu .and .rax (.imm 1),
      .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax), .mov .rax (.reg .rdx)] : List Instr) ++ accumulate ++
    ([.mov .rax (.mem (Core.field .digestLen)), .mov .rdx (.mem (Core.field .digestPrefixLen)),
      .alu .cmp .rdx (.reg .rax), .cmov .b .rax (.reg .rdx),
      .store (Core.field .digestPrefixLen) .rax,
      .mov .rax (.mem (Core.field .mask)), .alu .test .rax (.reg .rax)] : List Instr))]

/-- Intersect the mask with an equality of positive, equal-length byte
strings. `unequal` instead requires their inequality. -/
def equal (a b : Operand) (unequal : Bool := false) : Prog isa := seqs [
  .block (Core.pointer a.pointer ++ ([.mov .rsi (.reg .rax)] : List Instr) ++ Core.pointer b.pointer ++
    ([.mov .rdx (.reg .rax), .mov .rcx (.mem (Core.field a.length)), .mov32 .r8 (.imm 0)] : List Instr)),
  .loop (.block [.movzx8 .rax (at0 .rsi), .movzx8 .r9 (at0 .rdx), .alu .xor .rax (.reg .r9),
    .alu .or .r8 (.reg .rax), .alu .add .rsi (.imm 1), .alu .add .rdx (.imm 1), .alu .sub .rcx (.imm 1)]) .ne,
  .block (([.alu .cmp .r8 (.imm 1), .alu .sbb .rax (.reg .rax)] : List Instr) ++
    (if unequal then [.alu .xor .rax (.imm (-1))] else []) ++ accumulate)]

/-- Intersect the mask with whether a positive-length byte string is zero
(or nonzero). -/
def zero (a : Operand) (nonzero : Bool := false) : Prog isa := seqs [
  .block (Core.pointer a.pointer ++ ([.mov .rsi (.reg .rax),
    .mov .rcx (.mem (Core.field a.length)), .mov32 .r8 (.imm 0)] : List Instr)),
  .loop (.block [.movzx8 .rax (at0 .rsi), .alu .or .r8 (.reg .rax),
    .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) .ne,
  .block (([.alu .cmp .r8 (.imm 1), .alu .sbb .rax (.reg .rax)] : List Instr) ++
    (if nonzero then [.alu .xor .rax (.imm (-1))] else []) ++ accumulate)]

/-- In a child workspace: array aX is below the modulus and at least 1
(or at least 2 for g and y). Return the mask in rax. -/
def rangeMask (aboveOne : Bool) : Prog isa := seqs [
  .block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aX))),
    .mov .r10 (.mem (hdr (sArr aN))), .mov32 .rbp (.imm 0)],
  wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)),
    .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp],
  .block (([.mov .r15 (.mem (at0 .rbx))] : List Instr) ++
    (if aboveOne then [.shift .shr .r15 1] else [])),
  wordLoop 1 [.mov .rax (.mem (ix .rbx .r14)), .alu .or .r15 (.reg .rax)],
  .block [.alu .cmp .r15 (.imm 1), .alu .sbb .rax (.reg .rax),
    .alu .xor .rax (.imm (-1)), .alu .and .rax (.reg .rbp)]]

def range (ws : Nat) (a : Operand) (aboveOne : Bool := false) : Prog isa := seqs [
  .block (Core.operand arg argLen a ++ Core.enter ws), Arithmetic.load aX arg argLen,
  rangeMask aboveOne,
  .block (([Crt.leave] : List Instr) ++ accumulate)]

/-- Store modulus minus a small positive value. Called only after domain
shape checks, so subtraction cannot underflow. -/
def modulusMinus (ws : Nat) (amount : Nat) (output : Operand) : Prog isa :=
  seqs ([.block (Core.operand result resultLen output ++ Core.enter ws ++
    ([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aN))),
      .mov .rbx (.mem (hdr (sArr aY))), .mov .rax (.mem (at0 .rsi)),
      .alu .sub .rax (.imm (BitVec.ofNat 32 amount)), .store (at0 .rbx) .rax, cfToRbp] : List Instr)),
    wordLoop 1 [cfFromRbp, .mov .rax (.mem (ix .rsi .r14)), .alu .sbb .rax (.imm 0),
      .store (ix .rbx .r14) .rax, cfToRbp]] ++ Core.finish)

/-- Compare a child result with the ordinary number 1, accumulating its
mask after returning to the parent. -/
def isOne (ws : Nat) (value : Operand) : Prog isa := seqs [
  .block (Core.operand arg argLen value ++ Core.enter ws),
  Arithmetic.load aX arg argLen,
  .block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aX))),
    .mov .r15 (.mem (at0 .rbx)), .alu .xor .r15 (.imm 1)],
  wordLoop 1 [.mov .rax (.mem (ix .rbx .r14)), .alu .or .r15 (.reg .rax)],
  .block (([.alu .cmp .r15 (.imm 1), .alu .sbb .rax (.reg .rax), Crt.leave] : List Instr) ++ accumulate)]

/-- Range and domain checks before the public subgroup exponentiations. -/
def publicPrefix (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  range pWorkspace Core.generator true, range pWorkspace Core.publicValue true,
  modulusMinus pWorkspace 1 (Core.element t),
  Core.reduce mul (Core.element t) (Core.scalar u), zero (Core.scalar u),
  modulusMinus qWorkspace 2 (Core.scalar qMinusTwo)]

/-- Signing also checks `g^x = y`, so `g^q = 1` implies the public value's subgroup check. -/
def signingKey (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs (publicPrefix mul ++ [
  Core.publicPow sq mul pWorkspace Core.generator ⟨.input .q, .qLen⟩ (Core.element t),
  isOne pWorkspace (Core.element t)])

/-- Check both subgroup memberships independently, with public q windows. -/
def publicKey (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs (publicPrefix mul ++ [
  Core.publicPow sq mul pWorkspace Core.generator ⟨.input .q, .qLen⟩ (Core.element t),
  isOne pWorkspace (Core.element t),
  Core.publicPow sq mul pWorkspace Core.publicValue ⟨.input .q, .qLen⟩ (Core.element t),
  isOne pWorkspace (Core.element t)])

/-- Private/public key consistency and nonce rejection masks. -/
def privateKey (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  range qWorkspace Core.privateScalar, range qWorkspace Core.nonce,
  Core.pow sq mul pWorkspace Core.generator Core.privateScalar (Core.element t),
  equal (Core.element t) Core.publicValue]

end VG.Impl.Dsa.X86_64.Checks
