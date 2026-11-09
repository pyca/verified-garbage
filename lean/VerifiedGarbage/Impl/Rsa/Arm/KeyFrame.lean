module

public import VerifiedGarbage.Impl.Rsa.Arm.MulMod
public import VerifiedGarbage.Impl.Rsa.Arm.CrtValues
public import VerifiedGarbage.Impl.Bignum.Arm.PcFn
public import VerifiedGarbage.Impl.Bignum.Arm.MontOp
public import VerifiedGarbage.Impl.Bignum.Arm.Square

/-! # A function in the key working space on ARMv7: its frame and wrapper

The frame of 56 bytes that `vg_rsa_recover_primes_det` pushes, as
`vg_rsa_public_checked` does (word 0 then holds the base of the Montgomery
working space, word 1 `p`, word 2 `q`), its arguments' offsets above it, and
the wrapper around its body (`codeWith`): the entry, the check of `n` (an
invalid modulus writes zeros at once, `fail`), the loads of `n`, `e` and `d`
into the key working space at `scratch` (`Impl/Rsa/Arm/KeyWs.lean`) with
`w = 2 ⌈n_len / 8⌉ + 2` words of 32 bits, the product `M = d e` (`prod`), by
`mulMod` modulo `2^(32 W - 1)` over the `8 e_len` bits of `e` with the
working space read with `W = 2 w + 2` words, and the factors written under
the mask (`stores`). `clrTop` clears the words of an array above
Montgomery multiplication's numbers, which key generation, Miller–Rabin and
FFDH use too.
-/

@[expose] public section

namespace VG.Impl.Rsa.Arm.Recover
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Rsa.Arm.Keys

/-! ## The frame

After the push of `r0`–`r12` and `lr`, the stack arguments start at byte
56: `n`, `n_len`, `e`, `e_len`, `d`, `d_len`, `scratch`, `scratch_len`. -/

def oP : Nat := 4
def oQ : Nat := 8
def aoN : Nat := 56
def aoK : Nat := 60
def aoE : Nat := 64
def aoEl : Nat := 68
def aoD : Nat := 72
def aoDl : Nat := 76
def aoS : Nat := 80

/-! ## The header

Bytes 0–19 are the division's (16: `w`), 100–112 the shared routines', and
132 the mask of the result (`CrtValues.sMask`, which `CrtValues.store`
reads). -/

def sMask : Nat := 132

/-! ## The arrays

With `w` words: Montgomery multiplication's arrays are 20–27 (its operands
`n` (20), `y` (21), `R² mod n` (24), `g^(2^i)` (25), the multiplicand (26)
and the square (27)); `n`, 1, 0, `R mod n`, `n - R mod n`, and two
temporaries; the division's four. Arrays 0–14 are `inverse`'s. -/

def mBase : Nat := 20
def aN : Nat := 32
def aW : Nat := 37
/-- The number of arrays. -/
def nArr : Nat := 44

/-- With `W` words: zero, `e`, `d`, `M`, the modulus of the product, the
temporaries 5–8 of `mulMod` (and of the halvings), `r` and its copy. -/
def wZ : Nat := 0
def wE : Nat := 1
def wD : Nat := 2
def wM : Nat := 3
def wMod : Nat := 4
def wT : Nat := 5
/-! ## Contexts -/

/-- The base of the working space into `r8`. -/
def ctxB : List Instr := [.ldrSp .r8 aoS]

/-- `w` into `r9` and its stride into `r7`. -/
def ctxw : List Instr := [.ldr .r9 .r8 16] ++ stride

/-- `W = 2 w + 2` into `r9` and its stride into `r7`. -/
def ctxW : List Instr := [.ldr .r9 .r8 16, .mov .r9 (.shifted .r9 .lsl 1), .dp .add .r9 .r9 (.imm 2)] ++ stride

/-! ## Entry and exits -/

/-- `p` saved at frame word 1; `n` and `n_len` into `r4` and `r6`, and `n`
checked: Z if it is valid. -/
def entry : List Instr :=
  [.addSp .r12 0, .str .r0 .r12 oP, .ldrSp .r4 aoN, .ldrSp .r6 aoK] ++ modulusCheck

/-- Zeros to the output whose pointer is at frame byte `o`. -/
def zeroOut (o : Nat) : Prog isa := .seq (.block [.ldrSp .r0 o, .ldrSp .lr aoK, .mov .r2 (.imm 0)]) maskBytes

/-- Zeros to `p` and `q`, and 0 returned. -/
def fail : Prog isa := seqs [zeroOut oP, zeroOut oQ, .block [.mov .r0 (.imm 0)]]

/-! ## The numbers -/

/-- `w = 2 ⌈n_len / 8⌉ + 2`, the stride, `w` into the division's header,
and every array zeroed. -/
def setupK : List Instr :=
  ctxB ++ [.ldrSp .r9 aoK, .dp .add .r9 .r9 (.imm 7), .mov .r9 (.shifted .r9 .lsr 3),
    .mov .r9 (.shifted .r9 .lsl 1), .dp .add .r9 .r9 (.imm 2)] ++ stride ++
  [.str .r9 .r8 16, .dp .add .r0 .r8 (.imm (BitVec.ofNat 32 hdr)), .mov .lr (.imm (BitVec.ofNat 32 nArr)),
    .mul .lr .lr .r7, .mov .lr (.shifted .lr .lsr 2), .mov .r3 (.imm 0)]

/-- `[j] :=` the bytes of the stack arguments at `o` and `o + 4`. -/
def loadArg (o j : Nat) : List (Prog isa) := [.block [.ldrSp .r4 o, .ldrSp .r6 (o + 4)], CrtValues.load j]

/-- `n`, `e` and `d` read (`e` and `d` to the arrays `wE` and `wD` with `W`). -/
def loads : Prog isa := seqs ([.block setupK, zero] ++ loadArg aoN aN ++ loadArg aoE (2 * wE) ++
  loadArg aoD (2 * wD))

/-- The top word of `[j]` := `2^31`: `[j] = 2^(32 w - 1)` if it was zero. -/
def setTop (j : Nat) : List Instr :=
  ptr .r0 j ++ [.dp .add .r0 .r0 (.shifted .r9 .lsl 2), .dp .sub .r0 .r0 (.imm 4),
    .mov .r1 (.imm 0x80000000), .str .r1 .r0 0]

/-- With `W`: the modulus `2^(32 W - 1)`, and `8 e_len` steps. -/
def prodSet : List Instr := ctxW ++ setTop wMod ++ [.ldrSp .r6 aoEl, .mov .r6 (.shifted .r6 .lsl 3)]

/-- `M := d e`. -/
def prod : Prog isa := .seq (.block prodSet) (mulMod wZ wE wD wM wMod wT)

/-! ## Montgomery multiplication's working space -/

/-- The words above the low `w - 2` of `[j]` cleared. -/
def clrTop (j : Nat) : List Instr :=
  ptr .r0 j ++ [.dp .add .r0 .r0 (.shifted .r9 .lsl 2), .dp .sub .r0 .r0 (.imm 8), .mov .r1 (.imm 0),
    .str .r1 .r0 0, .str .r1 .r0 4]

/-! ## The factors -/

/-- The word above the `w` of `[j]` cleared, as the division's divisor needs. -/
def clrW (j : Nat) : List Instr :=
  ptr .r0 j ++ [.dp .add .r0 .r0 (.shifted .r9 .lsl 2), .mov .r1 (.imm 0), .str .r1 .r0 0]

/-- The factors written out under the mask, and the mask returned. -/
def stores : Prog isa := seqs [
  .block [.ldrSp .r10 oP, .ldrSp .r11 aoK], CrtValues.store 5,
  .block [.ldrSp .r10 oQ, .ldrSp .r11 aoK], CrtValues.store 6,
  .block [.ldr .r0 .r8 sMask]]

/-- `body` in the frame, after the entry, and the restore. -/
def codeWith (body : Prog isa) : Prog isa :=
  .frame (.push [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (.seq (.block entry) (.seq body (.block PcFn.restore))) (.pop .r12 56)

end VG.Impl.Rsa.Arm.Recover
