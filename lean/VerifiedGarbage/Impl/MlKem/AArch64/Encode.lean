module

public import VerifiedGarbage.Impl.MlKem.AArch64.Cbd16
public import VerifiedGarbage.Impl.MlKem.AArch64.Codec16
import VerifiedGarbage.Impl.MlKem.AArch64.Ntt

/-!
# ML-KEM on AArch64: the modulus check of the encapsulation key

* `checkEk(ek = x0) -> w0`: the modulus check of ML-KEM-768 (and, with
  `checkEkWith 128`, of ML-KEM-1024), eight 12-bit fields at a time: for each
  of the 96 (128) groups of 12 bytes of `ek[0 : 1152]` (`ek[0 : 1536]`),
  `tbl` puts the three bytes of each pair of fields in the low bytes of a
  word, and `and` and `ushr` take its two fields. `cmhs`
  with `q` sets each word of a field at least `q` to all ones, and `orr`
  gathers them in `v19`; after the loop, `uaddlv` sums its four words, and
  `(sum - 1) >> 63` returns 1 if the sum is 0, and 0 otherwise.

Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64

open VG.AArch64

/-! ## `checkEk` -/

/-- The eight fields of the 12 bytes in `x9` and `x10`, those at least `q` gathered in `v19`. -/
def ckMath : List Instr :=
  [.vop (.dup .d2 .v0 .x9), .vop (.ins .d2 .v0 1 .x10),
    .vop (.tbl .v1 .v0 .v16), .vop (.logic .and .v2 .v1 .v17), .vop (.shift .ushr .s4 .v3 .v1 12),
    .vop (.cmp .hs .s4 .v2 .v2 .v18), .vop (.cmp .hs .s4 .v3 .v3 .v18),
    .vop (.logic .orr .v19 .v19 .v2), .vop (.logic .orr .v19 .v19 .v3)]

/-- A group of 12 bytes at `x0`. -/
def checkEkBody : List Instr :=
  [.ldr .x .x9 .x0 0, .ldr .w .x10 .x0 8] ++ ckMath ++ [.addImm .x .x0 .x0 12, .subImm .x .x11 .x11 1]

/-- The check of the `n` groups of 12 bytes of a key. -/
def checkEkWith (n : Nat) : Prog isa :=
  .seq (.block (Codec16.maskVec .v16 [0,1,2,255,3,4,5,255,6,7,8,255,9,10,11,255] ++
      [.movz .x .x9 4095 0, .vop (.dup .s4 .v17 .x9), .movz .x .x9 3329 0, .vop (.dup .s4 .v18 .x9),
        .vop (.movi0 .v19), .movz .x .x11 (BitVec.ofNat 16 n) 0])) <|
  .seq (.loop (.block checkEkBody) (.nonzero .x .x11))
    (.block [.vop (.uaddlv .s4 .v20 .v19), .umov .x .x9 .v20 0, .subImm .x .x0 .x9 1, .lsr .x .x0 .x0 63])

/-- The check of ML-KEM-768 (`k = 3`): 96 groups. -/
abbrev checkEk : Prog isa := checkEkWith 96

end VG.Impl.MlKem.AArch64
