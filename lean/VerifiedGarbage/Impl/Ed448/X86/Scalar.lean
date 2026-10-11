module

public import VerifiedGarbage.Impl.X448.X86

/-!
# Ed448 scalar arithmetic on x86 (32-bit)

Arithmetic modulo the subgroup order `L = 2^446 - c` (`c < 2^224`), on a
remainder of twenty-eight 16-bit limbs in 32-bit words of the working space,
X448's representation on this target. Every product is of two 16-bit numbers
(`mul`, keeping the low word).

Reduction consumes the input sixteen bits at a time, from the top: the
remainder `r < L` (limbs `r₀, …, r₂₇`, so `r₂₇ < 2^14`) becomes
`v = 2^16 r + w` for the next chunk `w`, which is `h 2^446 + l` with
`h = r₂₆ >> 14 + 4 r₂₇ < 2^16` and `l` the limbs `w, r₀, …, r₂₅,
r₂₆ mod 2^14`; so `v ≡ l + h c` (mod L) since `2^446 ≡ c`, and `l + h c`
is below `2^446 + 2^240 < 2L` (`fold`, into `TF`). One carry pass computes
it (X448's `carryPass`): `h` times the fourteen limbs of `c`, each product
and limb below `2^32` with the carry. A conditional subtraction of `L`
(`reduceT`) leaves `v mod L`: `K = 2^448 - L` added to `TF`, into the
remainder, carries out of 448 bits exactly when `v ≥ L`, and the sum or
`TF` is selected with the mask `-carry`.

Multiply-add reduces its three inputs, multiplies two of them with X448's
rows (`row`, into X448's `ACC`), reduces the product's fifty-six limbs, and
adds the third, with a last conditional subtraction.

Every step runs for all limbs, independent of their values: no branch but on
the loop counter `ebp`, and every address a pointer plus a constant or the
counter. The working space's base is in `edi` (as for X448), the input's in
`esi` and `h` in `ecx`; the callee-saved registers are saved in the working
space's first 16 bytes (as X448 saves them), and the chunk `w` at `W`. The
arguments stay on the stack (cdecl), read when needed.
-/

@[expose] public section

namespace VG.Impl.Ed448.X86

open VG.X86
open VG.Impl.X448.X86 (at_ sc ld st carryPass row mulPre ACC)

/-! ## The layout of the working space -/

/-- The chunk `w` being folded in. -/
def W : Nat := 16
/-- The folded value `l + h c`. -/
def TF : Nat := 64
/-- The remainder of reduction, and of the product in multiply-add. -/
def RA : Nat := 192
/-- The reduced `k`, `s` and `r` of multiply-add. -/
def SK : Nat := 320
def SS : Nat := 448
def SR : Nat := 576

/-! ## Constants -/

/-- The 16-bit limbs of `c = 2^446 - L`, lowest first. -/
def cLimbs : List Nat :=
  [0xbb0d, 0x54a7, 0x3d6d, 0xdc87, 0x70aa, 0x723a, 0x3d8d, 0xde93, 0xc96f, 0x5129, 0x24b6,
    0x3bb1, 0xdc16, 0x8335]

/-- Limb `k` of `c`. -/
def cLimb (k : Nat) : Nat := cLimbs.getD k 0

/-- Limb `k` of `K = 2^448 - L = 3 · 2^446 + c`. -/
def kLimb (k : Nat) : Nat := if k = 27 then 0xc000 else cLimb k

/-! ## One chunk -/

/-- `h = r₂₆ >> 14 + 4 r₂₇` into `ecx`, for the remainder at `o`
(`r₂₇ < 2^14`, so rotating it right by 30 shifts it left by 2); no carry in
`ebx`. -/
def foldHead (o : Nat) : List Instr :=
  [ld .ecx (o + 104), .shift .shr .ecx 14, ld .eax (o + 108), .shift .ror .eax 30,
    .alu .add .ecx (.reg .eax), .mov .ebx (.imm 0)]

/-- Limb `k` of `l + h c` before carrying, into `eax`: `h` (in `ecx`) times
limb `k` of `c` below limb 14, plus the chunk `w` (at `W`) or the limb below
of the remainder at `o` (the top one masked to 14 bits). -/
def foldSrc (o k : Nat) : List Instr :=
  if k = 0 then
    [.mov .eax (.imm (BitVec.ofNat 32 (cLimb 0))), .mul .ecx, .alu .add .eax (.mem (sc W))]
  else if k < 14 then
    [.mov .eax (.imm (BitVec.ofNat 32 (cLimb k))), .mul .ecx,
      .alu .add .eax (.mem (sc (o + 4 * (k - 1))))]
  else if k < 27 then [ld .eax (o + 4 * (k - 1))]
  else [ld .eax (o + 104), .alu .and .eax (.imm 16383)]

/-- `2^16 r + w`, reduced below `2L`, into `TF`. -/
def fold (o : Nat) : List Instr := foldHead o ++ carryPass .edi TF (foldSrc o)

/-- Limb `k` of `TF + K` before carrying, into `eax`. -/
def csubSrc (k : Nat) : List Instr :=
  if k < 14 ∨ k = 27 then
    [ld .eax (TF + 4 * k), .alu .add .eax (.imm (BitVec.ofNat 32 (kLimb k)))]
  else [ld .eax (TF + 4 * k)]

/-- Limb `k` of the remainder at `o`: itself under the mask `ecx`, else limb
`k` of `TF`. -/
def selectStep (o k : Nat) : List Instr :=
  [ld .eax (TF + 4 * k), ld .edx (o + 4 * k), .alu .xor .edx (.reg .eax),
    .alu .and .edx (.reg .ecx), .alu .xor .eax (.reg .edx), st .eax (o + 4 * k)]

/-- `TF` (below `2L`) reduced modulo `L` into the remainder at `o`: `TF + K`
into `o`, carrying out of 448 bits (`ebx`) exactly when `TF ≥ L`, and then
the sum if it carried or `TF`. -/
def reduceT (o : Nat) : List Instr :=
  [.mov .ebx (.imm 0)] ++ carryPass .edi o csubSrc ++
    [.mov .ecx (.imm 0), .alu .sub .ecx (.reg .ebx)] ++ (List.range 28).flatMap (selectStep o)

/-- The remainder at `o` and the chunk at `W` folded and reduced. -/
def step (o : Nat) : List Instr := fold o ++ reduceT o

/-! ## Reducing an input -/

/-- The next two bytes from the top of the input at `esi` to `W` (`ebp`
counts its bytes down). -/
def readBytes : List Instr :=
  [.alu .sub .ebp (.imm 2), .mov .edx (.reg .esi), .alu .add .edx (.reg .ebp),
    .movzx8 .eax (at_ .edx 0), .movzx8 .edx (at_ .edx 1), .shift .ror .edx 24,
    .alu .add .eax (.reg .edx), st .eax W]

def byteStep (o : Nat) : List Instr := readBytes ++ step o ++ [.alu .cmp .ebp (.imm 0)]

/-- The remainder at `o` set to zero. -/
def zeroR (o : Nat) : List Instr :=
  .mov .eax (.imm 0) :: (List.range 28).map fun k => st .eax (o + 4 * k)

/-- The remainder at `o` of the 114 bytes at `esi`. -/
def reduce114 (o : Nat) : Prog isa :=
  .seq (.block (zeroR o ++ [.mov .ebp (.imm 114)])) (.loop (.block (byteStep o)) .ne)

/-- The remainder at `o` of the 57 bytes at `esi`: their top byte, then the
twenty-eight chunks below it. -/
def reduce57 (o : Nat) : Prog isa :=
  .seq (.block (zeroR o ++ [.movzx8 .eax (at_ .esi 56), st .eax o, .mov .ebp (.imm 56)]))
    (.loop (.block (byteStep o)) .ne)

/-! ## Entry and exit -/

/-- The callee-saved registers saved at the working space, whose address is
the argument at `[esp + d]`, through `eax` (as X448 saves them), and its base
into `edi`. -/
def save (d : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .esp d)), .store (at_ .eax 0) .ebx, .store (at_ .eax 4) .esi,
    .store (at_ .eax 8) .edi, .store (at_ .eax 12) .ebp, .mov .edi (.reg .eax)]

/-- Limb `k` of the remainder at `o` as two bytes at `esi`. -/
def packLimb (o k : Nat) : List Instr :=
  [ld .eax (o + 4 * k), .store8 (at_ .esi (2 * k)) .al, .shift .shr .eax 8,
    .store8 (at_ .esi (2 * k + 1)) .al]

/-- The remainder at `o` to the 57 bytes of the output (the argument at
`[esp + 4]`): twenty-eight limbs and a zero byte; then the callee-saved
registers restored (X448's `restore`). -/
def finish (o : Nat) : List Instr :=
  .mov .esi (.mem (at_ .esp 4)) :: (List.range 28).flatMap (packLimb o) ++
    [.mov .eax (.imm 0), .store8 (at_ .esi 56) .al] ++ Impl.X448.X86.restore

/-- `vg_ed448_scalar_reduce(out = [esp + 4], wide = [esp + 8], scratch = [esp + 12])`. -/
def scalarReduce : Prog isa :=
  .seq (.block (save 12 ++ [.mov .esi (.mem (at_ .esp 8))])) <|
  .seq (reduce114 RA) (.block (finish RA))

/-! ## Multiply-add -/

/-- The remainder at `o` of the 57 bytes at the argument at `[esp + d]`. -/
def reduceArg (d o : Nat) : Prog isa := .seq (.block [.mov .esi (.mem (at_ .esp d))]) (reduce57 o)

/-- `k`, `s` and `r` (at `[esp + 12]`, `[esp + 16]`, `[esp + 8]`) reduced to
`SK`, `SS` and `SR`. -/
def inputs : Prog isa :=
  .seq (reduceArg 12 SK) <| .seq (reduceArg 16 SS) (reduceArg 8 SR)

/-- The product of the remainders at `SK` and `SS`, at `ACC`. -/
def product : Prog isa := .seq (.block mulPre) (.loop (.block (row SK SS)) .ne)

/-- The next limb of the product from the top to `W` (`ebp` counts its bytes
down). -/
def readLimb : List Instr :=
  [.alu .sub .ebp (.imm 4), .mov .edx (.reg .edi), .alu .add .edx (.reg .ebp),
    .mov .eax (.mem (at_ .edx ACC)), st .eax W]

def limbStep : List Instr := readLimb ++ step RA ++ [.alu .cmp .ebp (.imm 0)]

/-- The remainder at `RA` of the fifty-six product limbs at `ACC`. -/
def reduceProduct : Prog isa :=
  .seq (.block (zeroR RA ++ [.mov .ebp (.imm 224)])) (.loop (.block limbStep) .ne)

/-- Limb `k` of the product's remainder plus the reduced `r`, into `eax`. -/
def addSrc (k : Nat) : List Instr := [ld .eax (RA + 4 * k), .alu .add .eax (.mem (sc (SR + 4 * k)))]

/-- The sum of the product's remainder and the reduced `r`, into `TF`. -/
def addPass : List Instr := [.mov .ebx (.imm 0)] ++ carryPass .edi TF addSrc

/-- `vg_ed448_scalar_mul_add(out = [esp + 4], r = [esp + 8], k = [esp + 12],
s = [esp + 16], scratch = [esp + 20])`: `k mod L` to `SK`, `s mod L` to
`SS`, `r mod L` to `SR`; their product's limbs at `ACC`, reduced to `RA`,
plus `SR` into `TF`, reduced. -/
def scalarMulAdd : Prog isa :=
  .seq (.block (save 20)) <| .seq inputs <| .seq product <| .seq reduceProduct <|
    .block (addPass ++ reduceT RA ++ finish RA)

end VG.Impl.Ed448.X86
