module

public import VerifiedGarbage.Impl.Bignum.X86_64.Adx

/-!
# Clearing the window and the final subtraction, eight words at a time

For `w` a multiple of 8, as the tiled ADX code requires: `zeroWin8` clears
the `2 w + 2` words from `r8` as `Adx.zeroWin` does, eight stores per
iteration; `finish8` computes `Adx.finish`'s result, with the borrow of the
subtraction and the mask of the selection moved between `rbp` and the
carry flag once per eight words rather than once per word, and the
selection by `cmovb`, which reads the carry flag set from the mask.
-/

@[expose] public section

namespace VG.Impl.Bignum.X86_64.Adx

open VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public

/-- The `2 w + 2` words from `r8` cleared (`rbx = w`, a multiple of 8). -/
def zeroWin8 : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0), .mov .rcx (.reg .rbx), .alu .add .rcx (.reg .rcx), .mov32 .r14 (.imm 0)])
    (.seq (.loop (.block ((List.range 8).map (fun (k : Nat) => .store (ix .r8 .r14 (8 * (k : Int))) .rax) ++
        ([.alu .add .r14 (.imm 8), .alu .cmp .r14 (.reg .rcx)] : List Instr))) .ne)
      (.block ((List.range 2).map fun (k : Nat) => .store (ix .r8 .r14 (8 * (k : Int))) .rax)))

/-- Word `k` of a block of `T - m`. -/
def subWord8 (k : Nat) : List Instr :=
  [.mov .rax (.mem (ix .r8 .r14 (8 * k))), .alu .sbb .rax (.mem (ix .r10 .r14 (8 * k))),
    .store (ix .rsi .r14 (8 * k)) .rax]

/-- `subMod`'s result, eight words per iteration. -/
def subMod8 : Prog isa :=
  .seq (.block [.mov32 .rbp (.imm 0), .mov .r14 (.imm 0)])
    (.seq (.loop (.block ([cfFromRbp] ++ (List.range 8).flatMap subWord8 ++
        [cfToRbp, .alu .add .r14 (.imm 8), .alu .cmp .r14 (.reg .r12)])) .ne)
      (.block [.mov .rax (.mem (ix .r8 .r12)), cfFromRbp, .alu .sbb .rax (.imm 0), cfToRbp]))

/-- Word `k` of a block of the selection: `T` if the carry flag is set,
`T - m` otherwise. -/
def selWord8 (k : Nat) : List Instr :=
  [.mov .rax (.mem (ix .rsi .r14 (8 * k))), .cmov .b .rax (.mem (ix .r8 .r14 (8 * k))),
    .store (ix .rbx .r14 (8 * k)) .rax]

/-- `selectAcc`'s result, eight words per iteration. -/
def select8 : Prog isa :=
  .seq (.block [.mov .r14 (.imm 0)])
    (.loop (.block ([cfFromRbp] ++ (List.range 8).flatMap selWord8 ++
      [cfToRbp, .alu .add .r14 (.imm 8), .alu .cmp .r14 (.reg .r12)])) .ne)

/-- `finish o` for `w` a multiple of 8. -/
def finish8 (o : Nat) : Prog isa :=
  .seq (.block (finishBases o)) (.seq subMod8 select8)

end VG.Impl.Bignum.X86_64.Adx
