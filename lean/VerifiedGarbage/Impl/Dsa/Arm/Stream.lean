module

public import VerifiedGarbage.Impl.Dsa.Arm.Checks

/-! # Reduction of a big-endian byte string, byte by byte, on 32-bit ARM

Each byte doubles the residue in the result slot eight times and adds the
byte, as the x86 code does. The source pointer is in `r11` and its end in
`lr`, which the arithmetic leaves alone; both are public.
-/

@[expose] public section
namespace VG.Impl.Dsa.Arm
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic

/-- Double the residue while carrying a public counter from `r1` to `r0`.
The addition does not use `r1`; conditional subtraction does not use `r0`. -/
def countedDouble (n : Nat) : Prog isa :=
  .seq (addDigits (contextMod n) (accS n) (resS n) (resS n)) <|
  .seq (.block [.mov .r0 (.reg .r1)]) (csubD (contextMod n) (accS n) (resS n))

/-- `k` modular doublings of the result slot, for `k < 2¹⁶`. -/
def doubles (n k : Nat) : Prog isa :=
  if k = 0 then .block [] else
    .seq (.block [.movw .r0 (BitVec.ofNat 16 k)])
      (.loop (.seq (.block [.mov .r1 (.reg .r0)])
        (.seq (countedDouble n) (.block [.subs .r0 .r0 (.imm 1)]))) .ne)

/-- Append a byte to the residue; the product slot holds the byte as a
zero-padded integer. The modulus exceeds 255. -/
def reduceStep (n : Nat) : Prog isa :=
  .seq (doubles n 8) (addD (contextMod n) (accS n) (resS n) (resS n) (prodS n))

/-- One byte: the byte at `r11` into the product slot's low word, then
`r11` moves up a byte. -/
def streamStep (n : Nat) : Prog isa :=
  .seq (.block ([.ldrb .r4 .r11 0] ++ ptr .r10 (prodS n) ++ [.str .r4 .r10 0])) <|
  .seq (reduceStep n) (.block [.dp .add .r11 .r11 (.imm 1), .cmp .r11 (.reg .lr)])

/-- The `lr - r11` bytes at `r11`, which may be none, reduced modulo the
context's modulus, into the result slot. -/
def reduceStream (n : Nat) : Prog isa :=
  .seq (zeros (2 * n) (resS n)) <| .seq (zeros (2 * n) (prodS n)) <|
  .seq (.block [.cmp .r11 (.reg .lr)])
    (.ite .eq (.block []) (.loop (streamStep n) .ne))

/-- `[resS] = [modS] - amount`. -/
def modulusMinus (n amount : Nat) : Prog isa :=
  .seq (setConst (2 * n) (prodS n) amount) (subWords (2 * n) (resS n) (modS n) (prodS n))

/-- Multiply ordinary integers in the base and exponent slots into the result
slot: the first multiplication encodes one operand, the second removes that
factor of R while multiplying. -/
def ordinaryMul (n : Nat) : Prog isa :=
  .seq (mul (contextMod n) invO (accS n) (prodS n) (baseS n) (rrS n))
    (mul (contextMod n) invO (accS n) (resS n) (expS n) (prodS n))

/-- Add reduced ordinary integers in the base and exponent slots. -/
def ordinaryAdd (n : Nat) : Prog isa :=
  addD (contextMod n) (accS n) (resS n) (baseS n) (expS n)

end VG.Impl.Dsa.Arm
