module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.KeyWs

/-!
# Operations of `vg_rsa_keygen_key` on PPC64LE, beyond the key routines'

On the working space of the RSA key operations (`Impl/Rsa/PPC64LE/KeyWs.lean`):

* slot operations on flags of 0 or 1: `notS d a` (`d := 1 - a`),
  `andNotS d a b` (`d := (1 - a) b`) and `selS d a b c` (`d := c ? b : a`);
* `setDigit j x`: the digit of `[j]` at the byte offset in `r6` := `x`;
* `mul K`: `[aMo] := [aMa] ([aMb] mod 2^K) mod 2^(32 w)`, bit by bit from the
  bottom of `[aMb]`, `K` in `r11`: each step adds `[aMa]` to `[aMo]` under the
  mask of `[aMb]`'s low bit, doubles `[aMa]` and halves `[aMb]`. A sum is a
  difference with a negation, `x + y = x - (0 - y)`, modulo `2^(32 w)`.

The arrays of `mul` are given by the caller; it uses `r0`, `r3`, `r5`–`r9`
and `r11`, and the slot `sl` for the bit.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.PPC64LE.Key

open VG.PPC64LE VG.Impl.Rsa.PPC64LE.Keys

/-- The slot `d` := 1 - the slot `a`. -/
def notS (d a : Nat) : List Instr :=
  [.load .w .r0 .r31 a, .li .r3 1, .logic .xor .r0 .r0 .r3, .store .w .r0 .r31 d]

/-- The slot `d` := (1 - the slot `a`) and the slot `b`. -/
def andNotS (d a b : Nat) : List Instr :=
  [.load .w .r0 .r31 a, .li .r3 1, .logic .xor .r0 .r0 .r3, .load .w .r3 .r31 b,
    .logic .and .r0 .r0 .r3, .store .w .r0 .r31 d]

/-- The slot `d` := the slot `b` if the slot `c` is 1, the slot `a` if it is 0:
`a ^ ((a ^ b) & c)`. -/
def selS (d a b c : Nat) : List Instr :=
  [.load .w .r0 .r31 a, .load .w .r3 .r31 b, .logic .xor .r3 .r3 .r0, .load .w .r9 .r31 c,
    .logic .and .r3 .r3 .r9, .logic .xor .r0 .r0 .r3, .store .w .r0 .r31 d]

/-- The digit of `[j]` at the byte offset in `r6` := `x`. -/
def setDigit (j x : Nat) : List Instr := ptr .r5 j ++ [.add .r5 .r5 .r6, .li .r0 x, .store .w .r0 .r5 0]

/-- `[o] := [o] + [a]` modulo `2^(32 w)`, through `n`: `[o] - (0 - [a])`. -/
def addTo (o a n z : Nat) : Prog isa := .seq (sub3 n z a) (sub3 o o n)

/-- One step of `mul`: the bit of `[b]` into `sl`, `[m] := bit ? [a] : 0`,
`[o] += [m]`, `[a] += [a]`, `[b] /= 2`, and one step less. -/
def mulStep (o a b m n z sl : Nat) : Prog isa := seqs ([
  .block (bitOf sl b),
  sel m z a sl, addTo o m n z, addTo a a n z,
  .block [.li .r9 0],
  half b,
  .block [.subi .r11 .r11 1]])

/-- `r11` steps of `mulStep`. -/
def mulLoop (o a b m n z sl : Nat) : Prog isa := .loop (mulStep o a b m n z sl) (.nonzero .d .r11)

end VG.Impl.RsaKeyGen.PPC64LE.Key
