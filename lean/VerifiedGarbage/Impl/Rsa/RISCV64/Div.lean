module

public import VerifiedGarbage.Impl.Rsa.RISCV64.KeyWs

/-!
# Fixed-iteration division for the RSA key operations on RISC-V

In words of 64 bits: `div q r d t` runs `64 w` steps of non-restoring
bit-serial division of the dividend in array `q` (`w` words) by the divisor
in array `d` (`w` words and an extra word 0), the remainder in array `r`
(`w + 1` words, in two's complement); `t` is not used. The dividend's bits
are taken from the top, the next one from the top of its word, which is then
shifted left with the new quotient bit in. Each step shifts the bit into the
remainder and, in one pass over its words, subtracts the divisor (while the
remainder is not negative, the mask `a4` all ones: `[d] ⊕ a4` and a carry of
1) or adds it (`a4 = 0`); the remainder's sign gives the next mask and the
quotient bit. At the end, a negative remainder has the divisor added back
(`fix`). The quotient ends in array `q` and the remainder in `r`; a divisor
of 0 still runs the same steps.

The steps count down in `s7`, and the new quotient bit is in `a5`; every
address is computed from the working space's base (`ptr`) and `s7`, so the
addresses and branches depend only on `w` and the base.
-/

@[expose] public section

namespace VG.Impl.Rsa.RISCV64.Div

open VG.RISCV64 VG.Impl.Bignum.RISCV64 VG.Impl.Rsa.RISCV64.Keys

/-- One word of a left shift at `t0`, the carry in and out in `t4`. -/
def shlBody : List Instr :=
  [.load .d .t5 .t0 0, .shift .sll .d .t6 .t5 1, .logic .or .t6 .t6 .t4, .store .d .t6 .t0 0,
    .shift .srl .d .t4 .t5 63, .addi .t0 .t0 8]

/-- `t2 := ` the address of word `(s7 - 1) / 64` of array `q`: the word the
dividend's next bit is in, and the quotient's next bit goes to. -/
def qword (q : Nat) : List Instr :=
  ptr .t2 q ++ [.addi .t5 .s7 (-1), .shift .srl .d .t5 .t5 6, .shift .sll .d .t5 .t5 3, .add .t2 .t2 .t5]

/-- One word of `[r] := 2 [r] + c + ([d] ⊕ mask) + c'`: the shift's carry in and
out in `t3`, the addition's in `t4`, the mask in `a4`. -/
def passBody : List Instr :=
  [.load .d .t5 .t0 0, .shift .sll .d .t6 .t5 1, .logic .or .t6 .t6 .t3, .shift .srl .d .t3 .t5 63,
    .load .d .t5 .t1 0, .logic .xor .t5 .t5 .a4, .add .t6 .t6 .t4, .sltu .a5 .t6 .t4,
    .add .t6 .t6 .t5, .sltu .t4 .t6 .t5, .logic .or .t4 .t4 .a5, .store .d .t6 .t0 0,
    .addi .t0 .t0 8, .addi .t1 .t1 8]

/-- One step of non-restoring division: the dividend's next bit shifted into
the remainder, which then has the divisor subtracted (a mask `a4` of all
ones, while it is not negative) or added (`a4 = 0`); the new mask and
quotient bit from its sign, the bit shifted into the dividend's word. -/
def stepK (q r d : Nat) (k : Reg) : Prog isa :=
  .seq (.block (qword q ++ [.load .d .t5 .t2 0, .shift .srl .d .t3 .t5 63] ++ ptr .t0 r ++ ptr .t1 d ++
      [.logicImm .and .t4 .a4 1, .addi .t2 k 1]))
    (.seq (countLoop .t2 passBody)
      (.block ([.shift .srl .d .t5 .t6 63, .addi .a4 .t5 (-1), .logicImm .and .a5 .a4 1] ++ qword q ++
        [.load .d .t5 .t2 0, .shift .sll .d .t5 .t5 1, .logic .or .t5 .t5 .a5, .store .d .t5 .t2 0,
          .addi .s7 .s7 (-1)])))

/-- The remainder zeroed, `64 w` steps to count, and the mask to subtract. -/
def init (r : Nat) : Prog isa :=
  .seq (.block (ptr .t0 r ++ [.addi .t3 .s9 1, .li .t5 0]))
    (.seq (countLoop .t3 [.store .d .t5 .t0 0, .addi .t0 .t0 8])
      (.block [.shift .sll .d .s7 .s9 6, .li .a4 (-1)]))

/-- One word of `[r] := [r] + ([d] ∧ mask)`, the carry in and out in `t4`. -/
def fixBody : List Instr :=
  [.load .d .t5 .t0 0, .load .d .t6 .t1 0, .logic .and .t6 .t6 .a4, .add .t5 .t5 .t4, .sltu .a5 .t5 .t4,
    .add .t5 .t5 .t6, .sltu .t4 .t5 .t6, .logic .or .t4 .t4 .a5, .store .d .t5 .t0 0, .addi .t0 .t0 8,
    .addi .t1 .t1 8]

/-- A negative remainder has the divisor added back. -/
def fixK (r d : Nat) (k : Reg) : Prog isa :=
  .seq (.block (ptr .t0 r ++ ptr .t1 d ++ [.logicImm .xor .a4 .a4 (-1), .li .t4 0, .addi .t3 k 1]))
    (countLoop .t3 fixBody)

/-- `64 w` division steps of `[q]` by `[d]`: the quotient in `[q]` (`w` words) and the
remainder in `[r]` (`[k] + 1` words, the divisor's `[k]` words and a word 0). -/
def divK (q r d : Nat) (k : Reg) : Prog isa :=
  .seq (init r) (.seq (.loop (stepK q r d k) (.nonzero .s7)) (fixK r d k))

/-- `divK` with `k = w`, the remainder in `[r]` (`t` is not used). -/
def div (q r d _t : Nat) : Prog isa := divK q r d .s9

end VG.Impl.Rsa.RISCV64.Div
