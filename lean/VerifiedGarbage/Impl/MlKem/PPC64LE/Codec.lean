module

public import VerifiedGarbage.Impl.MlKem.PPC64LE.Poly

/-!
# ML-KEM on PPC64LE: `ByteEncode₁₂`, `ByteDecode₁₂`, `SamplePolyCBD₂` and the encapsulation key check

As on 32-bit ARM (`Impl/MlKem/Arm/Poly.lean`), with 64-bit registers: each
function is a loop with a straight-line body over its input, counted down
to zero, using only volatile registers and no stack. The model has no
masking instructions: fields of bytes are extracted with pairs of shifts.
Values are reduced modulo `q` with `fixup` (`Impl/MlKem/PPC64LE/Poly.lean`),
with `q` in `r8`.

* `vg_mlkem_encode12(f = r3, out = r4)`: a loop over the 128 pairs of
  coefficients, storing three bytes each; `r5` counting.
* `vg_mlkem_decode12(b = r3, f = r4)`: a loop over the 128 groups of three
  bytes, each two 12-bit fields, each reduced with one subtraction of `q`
  and a `fixup`.
* `vg_mlkem_cbd2(b = r3, f = r4)`: a loop over the 128 bytes, each two
  coefficients: `x - y` for the numbers of bits set `x` and `y` in two
  2-bit fields `v`, each `v - (v >> 1)`, reduced with `fixup`.
* `vg_mlkem768_check_ek(ek = r3)`: counts, in `r5`, the 12-bit fields of
  `ek[0 : 1152]` that are at least `q` (the sign bit of `3328 - F`), and
  returns 1 if there are none: `1 - ((0 - n) >> 63)`.

Every address is a pointer plus a constant, and every branch depends on a
counter: only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.MlKem.PPC64LE

open VG.PPC64LE

/-! ## `ByteEncode₁₂` and `ByteDecode₁₂` -/

def encode12Body : List Instr :=
  [.load .w .r6 .r3 0, .load .w .r7 .r3 4, .stb .r6 .r4 0, .lsr .d .r6 .r6 8, .lsl .r8 .r7 4,
   .add .r6 .r6 .r8, .stb .r6 .r4 1, .lsr .d .r7 .r7 4, .stb .r7 .r4 2, .addi .r3 .r3 8, .addi .r4 .r4 3,
   .subi .r5 .r5 1]

def encode12 : Prog isa := .seq (.block [.li .r5 128]) (.loop (.block encode12Body) (.nonzero .d .r5))

/-- The first field of a group, `b₀ + 256 (b₁ mod 16)`, reduced, stored. -/
def decode12Lo : List Instr :=
  [.lbz .r6 .r3 0, .lbz .r7 .r3 1, .lsl .r7 .r7 60, .lsr .d .r7 .r7 52, .add .r6 .r6 .r7,
   .sub .r6 .r6 .r8] ++ fixup .r6 .r7 .r8 ++ [.store .w .r6 .r4 0]

/-- The second field of a group, `⌊b₁ / 16⌋ + 16 b₂`, reduced, stored. -/
def decode12Hi : List Instr :=
  [.lbz .r6 .r3 1, .lsr .d .r6 .r6 4, .lbz .r7 .r3 2, .lsl .r7 .r7 4, .add .r6 .r6 .r7,
   .sub .r6 .r6 .r8] ++ fixup .r6 .r7 .r8 ++ [.store .w .r6 .r4 4]

def decode12Body : List Instr :=
  decode12Lo ++ decode12Hi ++ [.addi .r3 .r3 3, .addi .r4 .r4 8, .subi .r5 .r5 1]

def decode12 : Prog isa :=
  .seq (.block [.li .r5 128, .li .r8 3329]) (.loop (.block decode12Body) (.nonzero .d .r5))

/-! ## `SamplePolyCBD₂` -/

/-- The number of bits set in the 2-bit field `v` of the byte at `r3` from
bit `k` (`k ≤ 6`), into `r`: `v - (v >> 1)`, with `r9` a temporary. -/
def pop2 (r : Reg) (k : Nat) : List Instr :=
  [.lbz r .r3 0, .lsl r r (62 - k), .lsr .d r r 62, .lsr .d .r9 r 1, .sub r r .r9]

/-- The coefficient of the nibble of the byte at `r3` from bit `k`, stored
at `r4 + off`. -/
def cbdCoeff (k off : Nat) : List Instr :=
  pop2 .r6 k ++ pop2 .r7 (k + 2) ++ [.sub .r6 .r6 .r7] ++ fixup .r6 .r7 .r8 ++ [.store .w .r6 .r4 off]

def cbd2Body : List Instr :=
  cbdCoeff 0 0 ++ cbdCoeff 4 4 ++ [.addi .r3 .r3 1, .addi .r4 .r4 8, .subi .r5 .r5 1]

def cbd2 : Prog isa :=
  .seq (.block [.li .r5 128, .li .r8 3329]) (.loop (.block cbd2Body) (.nonzero .d .r5))

/-! ## The encapsulation key check -/

/-- Adds 1 to `r5` if the field in `r6` is at least `q`. -/
def countBad : List Instr := [.li .r7 3328, .sub .r7 .r7 .r6, .lsr .d .r7 .r7 63, .add .r5 .r5 .r7]

def checkEkBody : List Instr :=
  [.lbz .r6 .r3 1, .lsl .r6 .r6 60, .lsr .d .r6 .r6 52, .lbz .r7 .r3 0, .add .r6 .r6 .r7] ++ countBad ++
  [.lbz .r6 .r3 1, .lsr .d .r6 .r6 4, .lbz .r7 .r3 2, .lsl .r7 .r7 4, .add .r6 .r6 .r7] ++ countBad ++
  [.addi .r3 .r3 3, .subi .r4 .r4 1]

def checkEk : Prog isa :=
  .seq (.block [.li .r4 384, .li .r5 0])
    (.seq (.loop (.block checkEkBody) (.nonzero .d .r4))
      (.block [.li .r6 0, .sub .r6 .r6 .r5, .lsr .d .r6 .r6 63, .li .r3 1, .sub .r3 .r3 .r6]))

end VG.Impl.MlKem.PPC64LE
