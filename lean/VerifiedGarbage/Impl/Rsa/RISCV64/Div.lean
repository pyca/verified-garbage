module

public import VerifiedGarbage.Impl.Rsa.RISCV64.KeyWs

/-!
# Fixed-iteration division for the RSA key operations on RISC-V

As on PPC64LE (`Impl/Rsa/PPC64LE/Div.lean`), in words of 64 bits: `div q r d
t` runs `64 w` steps of bit-serial division (`Proof/Rsa/KeyMath.lean`'s
`divStep`) of the dividend in array `q` (`w` words) by the divisor in array
`d` (`w` words and an extra word 0), the remainder in array `r` (`w + 1`
words) and array `t` a temporary (`w + 1` words). Each step shifts the
quotient and the remainder left by one bit together, the quotient's top bit
into the remainder, computes `[t] := [r] - [d]` and, if it did not borrow,
keeps it as the remainder (a masked selection) and sets the quotient's new
low bit. The quotient ends in array `q` and the remainder in `r`; a divisor
of 0 still runs the same steps.

The steps count down in `s7`, and the new quotient bit is in `a5`; every
address is computed from the working space's base (`ptr`), so the addresses
and branches depend only on `w` and the base.
-/

@[expose] public section

namespace VG.Impl.Rsa.RISCV64.Div

open VG.RISCV64 VG.Impl.Bignum.RISCV64 VG.Impl.Rsa.RISCV64.Keys

/-- One word of a left shift at `t0`, the carry in and out in `t4`. -/
def shlBody : List Instr :=
  [.load .d .t5 .t0 0, .shift .sll .d .t6 .t5 1, .logic .or .t6 .t6 .t4, .store .d .t6 .t0 0,
    .shift .srl .d .t4 .t5 63, .addi .t0 .t0 8]

/-- The quotient (`w` words) and the remainder (`w + 1`) shifted left
together. -/
def shift (q r : Nat) : Prog isa :=
  .seq (.block (ptr .t0 q ++ [.li .t4 0, mov .t3 .s9]))
    (.seq (countLoop .t3 shlBody)
      (.seq (.block (ptr .t0 r ++ [.addi .t3 .s9 1])) (countLoop .t3 shlBody)))

/-- `[t] := [r] - [d]` over `w + 1` words, the borrow in `t4`. -/
def subtract (r d t : Nat) : Prog isa := subN 1 t r d

/-- The new quotient bit `1 - borrow` into `a5`, and the mask `0 - a5` into
`t4`. -/
def bit : List Instr := [.logicImm .xor .a5 .t4 1, .li .t5 0, .sub .t4 .t5 .a5]

/-- `[r] := mask ? [t] : [r]` over `w + 1` words. -/
def keep (r t : Nat) : Prog isa :=
  .seq (.block (ptrs r r t ++ [.addi .t3 .s9 1])) (countLoop .t3 selBody)

/-- The quotient bit or'ed into the quotient's low word, and one step less. -/
def setBit (q : Nat) : List Instr :=
  ptr .t0 q ++ [.load .d .t5 .t0 0, .logic .or .t5 .t5 .a5, .store .d .t5 .t0 0,
    .addi .s7 .s7 (-1)]

/-- One step. -/
def step (q r d t : Nat) : Prog isa :=
  .seq (shift q r) (.seq (subtract r d t) (.seq (.block bit) (.seq (keep r t) (.block (setBit q)))))

/-- The remainder zeroed, and `64 w` steps to count. -/
def init (r : Nat) : Prog isa :=
  .seq (.block (ptr .t0 r ++ [.addi .t3 .s9 1, .li .t5 0]))
    (.seq (countLoop .t3 [.store .d .t5 .t0 0, .addi .t0 .t0 8]) (.block [.shift .sll .d .s7 .s9 6]))

/-- `64 w` division steps of `[q]` by `[d]`: the quotient in `[q]` and the
remainder in `[r]`. -/
def div (q r d t : Nat) : Prog isa := .seq (init r) (.loop (step q r d t) (.nonzero .s7))

end VG.Impl.Rsa.RISCV64.Div
