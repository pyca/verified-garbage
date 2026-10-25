module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.KeyWs

/-!
# Fixed-iteration division for the RSA key operations on PPC64LE

`div q r d t`: `32 w` steps of bit-serial division (`Proof/Rsa/KeyMath.lean`'s
`divStep`) of the dividend in array `q` (`w` digits) by the divisor in array
`d` (`w` digits and an extra digit 0), the remainder in array `r` (`w + 1`
digits) and array `t` a temporary (`w + 1` digits). Each step shifts the
quotient and the remainder left by one bit together, the quotient's top bit
into the remainder, computes `[t] := [r] - [d]` and, if it did not borrow,
keeps it as the remainder (a masked selection) and sets the quotient's new
low bit. The quotient ends in array `q` and the remainder in `r`; a divisor
of 0 still runs the same steps.

The steps count down in `r4`, and the new quotient bit is in `r10`; every
address is computed from the working space's base (`ptr`), so the addresses
and branches depend only on `w` and the base.
-/

@[expose] public section

namespace VG.Impl.Rsa.PPC64LE.Div

open VG.PPC64LE VG.Impl.Rsa.PPC64LE.Keys

/-- One digit of a left shift at `r5`, the carry in and out in `r9`. -/
def shlBody : List Instr :=
  [.load .w .r0 .r5 0, .lsl .r3 .r0 1, .logic .or .r3 .r3 .r9, .store .w .r3 .r5 0,
    .lsr .d .r9 .r0 31, .addi .r5 .r5 4]

/-- One word of a left shift at `r5`, the carry in and out in `r9`. -/
def shlWBody : List Instr :=
  [.load .d .r0 .r5 0, .lsl .r3 .r0 1, .logic .or .r3 .r3 .r9, .store .d .r3 .r5 0,
    .lsr .d .r9 .r0 63, .addi .r5 .r5 8]

/-- The quotient (`w` digits) and the remainder (`w + 1`) shifted left
together: `w / 2` words each, and the remainder's top digit. -/
def shift (q r : Nat) : Prog isa :=
  .seq (.block (ptr .r5 q ++ [.li .r9 0]))
    (.seq (evenW (.seq (.block [.lsr .d .r8 .r29 1]) (countLoop .r8 shlWBody))
        (.seq (.block [.addi .r8 .r29 0]) (countLoop .r8 shlBody)))
      (.seq (.block (ptr .r5 r))
        (evenW (.seq (.block [.lsr .d .r8 .r29 1]) (.seq (countLoop .r8 shlWBody) (.block shlBody)))
          (.seq (.block [.addi .r8 .r29 1]) (countLoop .r8 shlBody)))))

/-- `[t] := [r] - [d]` over `w + 1` digits, the borrow in `r9`: `w / 2`
words with the carry bit, then the top digit, whose difference in 64 bits
has the borrow in its sign bit. -/
def subtract (r d t : Nat) : Prog isa :=
  .seq (.block (ptr .r5 t ++ ptr .r6 r ++ ptr .r7 d))
    (evenW (.seq (.block [.lsr .d .r8 .r29 1, .subc .r0 .r8 .r8]) (.seq (countLoop .r8 subWBody)
        (.block [.load .w .r0 .r6 0, .load .w .r3 .r7 0, .sube .r0 .r0 .r3, .store .w .r0 .r5 0,
          .lsr .d .r9 .r0 63])))
      (.seq (.block [.addi .r8 .r29 1, .li .r9 0]) (countLoop .r8 subBody)))

/-- The new quotient bit `1 - borrow` into `r10`, and the mask `0 - r10`
into `r9`. -/
def bit : List Instr := [.li .r10 1, .logic .xor .r10 .r10 .r9, .li .r0 0, .sub .r9 .r0 .r10]

/-- The top digit of `mask ? [t] : [r]` into `[r]`. -/
def selTop : List Instr :=
  [.load .w .r0 .r6 0, .load .w .r3 .r7 0, .logic .xor .r3 .r3 .r0, .logic .and .r3 .r3 .r9,
    .logic .xor .r3 .r3 .r0, .store .w .r3 .r5 0]

/-- `[r] := mask ? [t] : [r]` over `w + 1` digits: `w / 2` words and the top
digit for an even `w`, else digits. -/
def keep (r t : Nat) : Prog isa :=
  .seq (.block (ptr .r5 r ++ ptr .r6 r ++ ptr .r7 t))
    (evenW (.seq (.block [.lsr .d .r8 .r29 1]) (.seq (countLoop .r8 selWBody) (.block selTop)))
      (.seq (.block [.addi .r8 .r29 1]) (countLoop .r8 selBody)))

/-- The quotient bit or'ed into the quotient's low digit, and one step less. -/
def setBit (q : Nat) : List Instr :=
  ptr .r5 q ++ [.load .w .r0 .r5 0, .logic .or .r0 .r0 .r10, .store .w .r0 .r5 0, .subi .r4 .r4 1]

/-- One step. -/
def step (q r d t : Nat) : Prog isa :=
  .seq (shift q r) (.seq (subtract r d t) (.seq (.block bit) (.seq (keep r t) (.block (setBit q)))))

/-- The remainder zeroed, and `32 w` steps to count. -/
def init (r : Nat) : Prog isa :=
  .seq (.block (ptr .r5 r ++ [.addi .r8 .r29 1, .li .r0 0]))
    (.seq (countLoop .r8 [.store .w .r0 .r5 0, .addi .r5 .r5 4]) (.block [.lsl .r4 .r29 5]))

/-- `32 w` division steps of `[q]` by `[d]`: the quotient in `[q]` and the
remainder in `[r]`. -/
def div (q r d t : Nat) : Prog isa := .seq (init r) (.loop (step q r d t) (.nonzero .d .r4))

end VG.Impl.Rsa.PPC64LE.Div
