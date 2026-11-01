module

public import VerifiedGarbage.Impl.MlKem.RISCV64.Poly

/-!
# ML-KEM on RISC-V: `ByteEncode₁₂`, `ByteDecode₁₂`, `SamplePolyCBD₂` and the encapsulation key check

As on PPC64LE (`Impl/MlKem/PPC64LE/Codec.lean`): each function is a loop
with a straight-line body over its input, counted down to zero, using only
registers the calling convention lets it clobber and no stack. Fields of
bytes are extracted with pairs of shifts. Values are reduced modulo `q`
with `fixup` (`Impl/MlKem/RISCV64/Poly.lean`), with `q` in `a5`.

* `vg_mlkem_encode12(f = a0, out = a1)`: a loop over the 128 pairs of
  coefficients, storing three bytes each; `a2` counting.
* `vg_mlkem_decode12(b = a0, f = a1)`: a loop over the 128 groups of three
  bytes, each two 12-bit fields, each reduced with one subtraction of `q`
  and a `fixup`.
* `vg_mlkem_cbd2(b = a0, f = a1)`: a loop over the 128 bytes, each two
  coefficients: `x - y` for the numbers of bits set `x` and `y` in two
  2-bit fields `v`, each `v - (v >> 1)`, reduced with `fixup`.
* `vg_mlkem768_check_ek(ek = a0)`: counts, in `a2`, the 12-bit fields of
  `ek[0 : 1152]` that are at least `q` (the sign bit of `3328 - F`, with
  `3328` in `a5`), and
  returns 1 if there are none: `1 - ((0 - n) >> 63)`.

Every address is a pointer plus a constant, and every branch depends on a
counter: only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.MlKem.RISCV64

open VG.RISCV64

/-! ## `ByteEncode₁₂` and `ByteDecode₁₂` -/

def encode12Body : List Instr :=
  [.load .w .a3 .a0 0, .load .w .a4 .a0 4, .store .b .a3 .a1 0, .shift .srl .d .a3 .a3 8, .shift .sll .d .a5 .a4 4,
   .add .a3 .a3 .a5, .store .b .a3 .a1 1, .shift .srl .d .a4 .a4 4, .store .b .a4 .a1 2, .addi .a0 .a0 8, .addi .a1 .a1 3,
   .addi .a2 .a2 (-1)]

def encode12 : Prog isa := .seq (.block [.li .a2 128]) (.loop (.block encode12Body) (.nonzero .a2))

/-- The first field of a group, `b₀ + 256 (b₁ mod 16)`, reduced, stored. -/
def decode12Lo : List Instr :=
  [.load .b .a3 .a0 0, .load .b .a4 .a0 1, .shift .sll .d .a4 .a4 60, .shift .srl .d .a4 .a4 52, .add .a3 .a3 .a4,
   .sub .a3 .a3 .a5] ++ fixup .a3 .a4 .a5 ++ [.store .w .a3 .a1 0]

/-- The second field of a group, `⌊b₁ / 16⌋ + 16 b₂`, reduced, stored. -/
def decode12Hi : List Instr :=
  [.load .b .a3 .a0 1, .shift .srl .d .a3 .a3 4, .load .b .a4 .a0 2, .shift .sll .d .a4 .a4 4, .add .a3 .a3 .a4,
   .sub .a3 .a3 .a5] ++ fixup .a3 .a4 .a5 ++ [.store .w .a3 .a1 4]

def decode12Body : List Instr :=
  decode12Lo ++ decode12Hi ++ [.addi .a0 .a0 3, .addi .a1 .a1 8, .addi .a2 .a2 (-1)]

def decode12 : Prog isa :=
  .seq (.block ([.li .a2 128] ++ liq .a5 3329)) (.loop (.block decode12Body) (.nonzero .a2))

/-! ## `SamplePolyCBD₂` -/

/-- The number of bits set in the 2-bit field `v` of the byte at `a0` from
bit `k` (`k ≤ 6`), into `r`: `v - (v >> 1)`, with `a6` a temporary. -/
def pop2 (r : Reg) (k : Nat) : List Instr :=
  [.load .b r .a0 0, .shift .sll .d r r (62 - k), .shift .srl .d r r 62, .shift .srl .d .a6 r 1, .sub r r .a6]

/-- The coefficient of the nibble of the byte at `a0` from bit `k`, stored
at `a1 + off`. -/
def cbdCoeff (k off : Nat) : List Instr :=
  pop2 .a3 k ++ pop2 .a4 (k + 2) ++ [.sub .a3 .a3 .a4] ++ fixup .a3 .a4 .a5 ++ [.store .w .a3 .a1 off]

def cbd2Body : List Instr :=
  cbdCoeff 0 0 ++ cbdCoeff 4 4 ++ [.addi .a0 .a0 1, .addi .a1 .a1 8, .addi .a2 .a2 (-1)]

def cbd2 : Prog isa :=
  .seq (.block ([.li .a2 128] ++ liq .a5 3329)) (.loop (.block cbd2Body) (.nonzero .a2))

/-! ## The encapsulation key check -/

/-- Adds 1 to `a2` if the field in `a3` is at least `q`, with `3328` in `a5`. -/
def countBad : List Instr := [.sub .a4 .a5 .a3, .shift .srl .d .a4 .a4 63, .add .a2 .a2 .a4]

def checkEkBody : List Instr :=
  [.load .b .a3 .a0 1, .shift .sll .d .a3 .a3 60, .shift .srl .d .a3 .a3 52, .load .b .a4 .a0 0, .add .a3 .a3 .a4] ++ countBad ++
  [.load .b .a3 .a0 1, .shift .srl .d .a3 .a3 4, .load .b .a4 .a0 2, .shift .sll .d .a4 .a4 4, .add .a3 .a3 .a4] ++ countBad ++
  [.addi .a0 .a0 3, .addi .a1 .a1 (-1)]

def checkEk : Prog isa :=
  .seq (.block ([.li .a1 384, .li .a2 0] ++ liq .a5 3328))
    (.seq (.loop (.block checkEkBody) (.nonzero .a1))
      (.block [.li .a3 0, .sub .a3 .a3 .a2, .shift .srl .d .a3 .a3 63, .li .a0 1, .sub .a0 .a0 .a3]))

end VG.Impl.MlKem.RISCV64
