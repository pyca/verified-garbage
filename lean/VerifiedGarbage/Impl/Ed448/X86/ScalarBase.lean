module

public import VerifiedGarbage.Impl.X448.BaseTable
public import VerifiedGarbage.Impl.Ed448.Formulas
public import VerifiedGarbage.Impl.Ed448.X86.Scalar
public import VerifiedGarbage.Spec.Ed448

/-!
# Ed448 base-point multiplication on x86 (32-bit)

`vg_ed448_scalar_base(out = [esp + 4], scalar = [esp + 8], scratch = [esp + 12])`:
the encoding of `[s]B` for the 456-bit little-endian scalar `s`, without
pruning.

Field elements are X448's on this target (fourteen 32-bit words in the
128-byte slots of the working space, `Impl/X448/X86.lean`), and so is the
field arithmetic: multiplications (and squarings, as multiplications of a
slot by itself), additions and subtractions, which are calls of the field
functions `vg_gf448_r32_*` (their arguments in the 20 bytes of stack below
the return address), the constant-time swap, the inversion, the full
reduction of slot 1 and its output. Points are the
specification's projective coordinates `(X : Y : Z)`. As in X448, `edi`
holds the working space and `esi` the loop counter; the callee-saved
registers are saved in the working space's first 16 bytes
(`Impl/Ed448/X86/Scalar.lean`'s `save`).

The scalar's bits are expanded into bytes at `BITS` (byte `t` is bit `t`), as
X448 expands its scalar. They are 114 nibbles `n`, each standing for the signed
digit `n - 8`, so that

`s = 16 (G + Σ (n_{2j+1} - 8) 256^j) + G + Σ (n_{2j} - 8) 256^j`, `G = 8 Σ 256^j`

(`j < 57`). Two accumulators, `A` (slots 0–2) and `C` (slots 3–5), start at the
affine point `[G] B`; slots 10 and 11 hold 1 and `d`, and the others zero
(`combVal`). Step `j` (`combStep`) adds both digits of table `j`, which holds
`[m 256^j] B` for `m = 1 … 8` (the static `combSym`, 57 tables of 896 bytes,
`Impl/X448/BaseTable.lean`), the odd one to `A` and the even one to `C`: the
entry of the digit's magnitude is selected into slots 8 and 9 (`selectT` reads
every entry of the table, and ORs in its words under the mask of its index being
the magnitude; entry 0 is the neutral point), its `x` is negated if the digit is
negative (`negSel`), and the affine point is added (`addAff`: RFC 8032 §5.2.4's
addition). So the same instructions run, at the same addresses, whatever the
digits. The result is `16 A + C` (`combFinish`): four doublings (RFC 8032
§5.2.4's formulas, `Impl/Ed448/Formulas.lean`'s `doubleOps`) and an addition
(`addOps`). It is then encoded (§5.2.2): `Z` inverted with X448's addition
chain, `x = X/Z` (into slot 1) fully reduced and its low bit written as the top
bit of the output's 57th byte, and `y = Y/Z` fully reduced and written as its
first 56 bytes.

The address of the static comes from a balanced frame (`symPush`) and is kept in
the working space, at `TPTR`.

The only branches are on the loop counters, and every address is a pointer
plus a constant or a counter, so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.Ed448.X86

open VG.X86
open VG.Impl.X448.X86 (at_ sc ld st slot BITS X2 Op ops freeze invert bitsLoop copy)

/-! ## Field programs on the slots -/

/-- A field operation (`Impl/Ed448/Formulas.lean`) as X448's. -/
def toOp : FOp → Impl.X448.X86.Op
  | .mul o a b => .mul (slot o) (slot a) (slot b)
  | .sqr o a => .mul (slot o) (slot a) (slot a)
  | .add o a b => .add (slot o) (slot a) (slot b)
  | .sub o a b => .sub (slot o) (slot a) (slot b)

def field (l : List FOp) : Prog isa := ops (l.map toOp)

/-! ## Initial slots -/

/-- The initial value of slot `i` for verification: `R = (0 : 1 : 1)`, `Q` the base point and
`d`, and zero elsewhere. -/
def initVal (i : Nat) : Nat :=
  if i = 0 then Spec.Ed448.identity.X.val
  else if i = 1 then Spec.Ed448.identity.Y.val
  else if i = 2 then Spec.Ed448.identity.Z.val
  else if i = 8 then Spec.Ed448.basePoint.X.val
  else if i = 9 then Spec.Ed448.basePoint.Y.val
  else if i = 10 then Spec.Ed448.basePoint.Z.val
  else if i = 11 then Spec.Ed448.d.val
  else 0

/-- The initial value of slot `i` for the fixed-base comb: both accumulators (slots 0–2 and 3–5)
the affine point `[G] B`, 1 and `d` in slots 10 and 11, and zero elsewhere. -/
def combVal (i : Nat) : Nat :=
  if i = 0 ∨ i = 3 then Impl.X448.baseG57.1.val
  else if i = 1 ∨ i = 4 then Impl.X448.baseG57.2.val
  else if i = 2 ∨ i = 5 ∨ i = 10 then 1
  else if i = 11 then Spec.Ed448.d.val
  else 0

/-- Word `k` of the value `v`. -/
def initLimb (v k : Nat) : Nat := v / 2 ^ (32 * k) % 2 ^ 32

/-- Word `k` of slot `i`, whose value is `v`, through `ebp = edi + 64`, the address of slot 0,
if it is not zero (the slots are zeroed first). -/
def initStep (v i k : Nat) : List Instr :=
  if initLimb v k = 0 then []
  else [.mov .eax (.imm (BitVec.ofNat 32 (initLimb v k))), .store (at_ .ebp (128 * i + 4 * k)) .eax]

def initSlot (v i : Nat) : List Instr := (List.range 14).flatMap (initStep v i)

/-- The 704 words of the slots zeroed, through `ebp` from `edi + 64` (`eax`
counts them down). -/
def zeroSlots : Prog isa :=
  .seq (.block [.mov .ebp (.reg .edi), .alu .add .ebp (.imm 64), .mov .ebx (.imm 0), .mov .eax (.imm 704)])
    (.loop (.block [.store (at_ .ebp 0) .ebx, .alu .add .ebp (.imm 4), .alu .sub .eax (.imm 1)]) .ne)

/-- Every slot `i` set to its initial value `v i`. The stores are through `ebp`, not
`edi`: the taint analysis records public words it stores at known offsets of
the working space, and the constants (the base point and `d`) would stay in
that record through the whole ladder, slowing every check of a store. -/
def initSlots (v : Nat → Nat) : Prog isa :=
  .seq zeroSlots (.block ([.mov .ebp (.reg .edi), .alu .add .ebp (.imm 64)] ++
    (List.range 22).flatMap fun i => initSlot (v i) i))

/-! ## The scalar's bits -/

/-- All 456 bits of the scalar (the argument at `[esp + 8]`), by `bitsLoop`. -/
def baseBits : Prog isa := .seq (.block [.mov .esi (.mem (at_ .esp 8))]) (bitsLoop BITS 57)

/-- The callee-saved registers saved, the slots initialized and the scalar's bits. -/
def baseEntry : Prog isa := .seq (.block (save 12)) (.seq (initSlots combVal) baseBits)

/-! ## Pieces of a selection -/

/-- `ebx = -(ecx = i)`: the mask of entry `i`, for the index `ecx < 16`. -/
def selMask (i : Nat) : List Instr :=
  [.mov .eax (.reg .ecx), .alu .xor .eax (.imm (BitVec.ofNat 32 i)), .alu .sub .eax (.imm 1),
    .shift .shr .eax 31, .mov .ebx (.imm 0), .alu .sub .ebx (.reg .eax)]

/-- The slot at `o` zeroed (`eax` is zero). -/
def zeroSlot (o : Nat) : List Instr := (List.range 14).flatMap fun j => [st .eax (o + 4 * j)]

/-- `T` (slots 3–5) into `R` (slots 0–2). -/
def takeOps : List Op := [.copy (slot 0) (slot 3), .copy (slot 1) (slot 4), .copy (slot 2) (slot 5)]

/-! ## The fixed-base comb -/

/-- The word of the working space holding the address of the tables. -/
def TPTR : Nat := 4096

/-- The static holding the comb's tables. -/
def combSym : String := "VG_X448_COMB"

/-- Word `i` (of 64 bits) of the tables: table `j = i / 112` takes 896 bytes, the `x` and then the
`y` of its entries `m + 1 = 1 … 8`, seven words each. -/
def combWord (i : Nat) : BitVec 64 :=
  let e := Impl.X448.baseTable (i / 112) (i % 56 / 7 + 1)
  BitVec.ofNat 64 ((if i % 112 < 56 then e.1 else e.2).val / 2 ^ (64 * (i % 7)))

/-- The words of the 57 tables, as the static `combSym` holds them. -/
def combWords : List (BitVec 64) := (List.range (57 * 112)).map combWord

/-- The static the comb reads. -/
def combConsts : List (String × List (BitVec 64)) := [(combSym, combWords)]

/-- The static's address, obtained in a balanced four-byte CALL frame (`symPush`; the saved
`eip` is popped into `ecx`), to `TPTR`. -/
def tblSetup : Prog isa :=
  .seq (.frame (.symPush .eax combSym) (.block []) (.pop .ecx 1)) (.block [st .eax TPTR])

/-- `ebp = edi + 8 esi`: the bits of table `esi`'s digits are at `ebp + BITS` (even) and
`ebp + BITS + 4` (odd). -/
def digitPtr : List Instr :=
  [.mov .ebp (.reg .esi), .alu .add .ebp (.reg .ebp), .alu .add .ebp (.reg .ebp), .alu .add .ebp (.reg .ebp),
    .alu .add .ebp (.reg .edi)]

/-- `ecx` = the nibble `b₀ + 2b₁ + 4b₂ + 8b₃` of the bits at `ebp + o`. -/
def nibble (o : Nat) : List Instr :=
  [.movzx8 .ecx (at_ .ebp (o + 3)), .movzx8 .eax (at_ .ebp (o + 2)), .alu .add .ecx (.reg .ecx),
    .alu .add .ecx (.reg .eax), .movzx8 .eax (at_ .ebp (o + 1)), .alu .add .ecx (.reg .ecx),
    .alu .add .ecx (.reg .eax), .movzx8 .eax (at_ .ebp o), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .eax)]

/-- From the nibble `n` in `ecx`: `|n - 8|` into `ecx`. -/
def magnitude : List Instr :=
  [.alu .sub .ecx (.imm 8), .mov .eax (.reg .ecx), .shift .shr .eax 31, .mov .ebx (.imm 0),
    .alu .sub .ebx (.reg .eax), .alu .xor .ecx (.reg .ebx), .alu .sub .ecx (.reg .ebx)]

/-- `ebp` = the address of table `esi`: the static's, plus 896 bytes a table (`eax = 128 esi`,
added seven times). -/
def tblPtr : List Instr :=
  [.mov .eax (.reg .esi)] ++ List.replicate 7 (.alu .add .eax (.reg .eax)) ++
    [ld .ebp TPTR] ++ List.replicate 7 (.alu .add .ebp (.reg .eax))

/-- Word `j` at `ebp + c`, under the mask `ebx`, ORed into word `j` of the slot at `o`. -/
def selWordT (o c j : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .ebp (c + 4 * j))), .alu .and .eax (.reg .ebx),
    .alu .or .eax (.mem (sc (o + 4 * j))), st .eax (o + 4 * j)]

def selCoordT (o c : Nat) : List Instr := (List.range 14).flatMap (selWordT o c)

/-- Entry `m + 1` of the table ORed into slots 8 (`x`) and 9 (`y`) if it is the digit's. -/
def selEntryT (m : Nat) : List Instr :=
  selMask (m + 1) ++ selCoordT (slot 8) (56 * m) ++ selCoordT (slot 9) (448 + 56 * m)

/-- The entry of index `ecx` of the table at `ebp` into slots 8 and 9; entry 0 is the neutral
point `(0, 1)`. -/
def selectT : List Instr :=
  .mov .eax (.imm 0) :: zeroSlot (slot 8) ++ zeroSlot (slot 9) ++
    selMask 0 ++ [.alu .and .ebx (.imm 1), st .ebx (slot 9)] ++ (List.range 8).flatMap selEntryT

/-- The magnitude of the digit whose bits are at `BITS + o` into `ecx`, and the address of table
`esi` into `ebp`. -/
def digitLoad (o : Nat) : List Instr := digitPtr ++ nibble (BITS + o) ++ magnitude ++ tblPtr

/-- `(X : Y : Z) + (x, y)` (RFC 8032 §5.2.4, for `Z₂ = 1` and `d = -39081`) into slots `x`, `y` and
`z`, for `(X : Y : Z)` there and `(x, y)` in slots 8 and 9, with the temporaries 12–18. -/
def addAff (x y z : Nat) : List Op := [
  .mul (slot 12) (slot z) (slot z), .mul (slot 13) (slot x) (slot 8), .mul (slot 14) (slot y) (slot 9),
  .mul (slot 15) (slot 13) (slot 14), .mulSmall (slot 15) (slot 15), .add (slot 16) (slot x) (slot y),
  .add (slot 17) (slot 8) (slot 9), .mul (slot 16) (slot 16) (slot 17), .sub (slot 16) (slot 16) (slot 13),
  .sub (slot 16) (slot 16) (slot 14), .sub (slot 17) (slot 14) (slot 13), .add (slot 18) (slot 12) (slot 15),
  .sub (slot 12) (slot 12) (slot 15), .mul (slot 13) (slot z) (slot 18), .mul (slot x) (slot 13) (slot 16),
  .mul (slot 13) (slot z) (slot 12), .mul (slot y) (slot 13) (slot 17), .mul (slot z) (slot 18) (slot 12)]

/-- The entry's `x` negated if the digit is negative, that is if the top bit of its nibble is clear
(`ebx` = the bit less 1), by swapping slots 8 and 12, which holds `-x` (slot 21 is zero). -/
def negSel (o : Nat) : List Instr :=
  digitPtr ++ [.movzx8 .ebx (at_ .ebp (BITS + o + 3)), .alu .sub .ebx (.imm 1)] ++
    Impl.X448.X86.cswap (slot 8) (slot 12)

/-- The digit at `BITS + o` added to the accumulator in slots `x`, `y` and `z`. -/
def digitAdd (o x y z : Nat) : Prog isa :=
  .seq (.block (digitLoad o)) <| .seq (.block selectT) <| .seq (ops [.sub (slot 12) (slot 21) (slot 8)]) <|
  .seq (.block (negSel o)) (ops (addAff x y z))

/-- Step `esi = j`: the odd digit of table `j` added to `A` (slots 0–2), the even one to `C` (slots
3–5). ZF is clear while another step follows. -/
def combStep : Prog isa :=
  .seq (digitAdd 4 0 1 2) <| .seq (digitAdd 0 3 4 5) <| .block [.alu .add .esi (.imm 1), .alu .cmp .esi (.imm 57)]

/-- The 57 steps. -/
def combLoop : Prog isa := .seq (.block [.mov .esi (.imm 0)]) (.loop combStep .ne)

/-- `A` doubled four times. -/
def double4 : Prog isa :=
  .seq (.block [.mov .esi (.imm 4)]) (.loop (.seq (field doubleOps) (.block [.alu .sub .esi (.imm 1)])) .ne)

/-- `C` into slots 8–10. -/
def copyC : List Op := [.copy (slot 8) (slot 3), .copy (slot 9) (slot 4), .copy (slot 10) (slot 5)]

/-- `16 A + C` into slots 0–2. -/
def combFinish : Prog isa := .seq double4 <| .seq (ops copyC) <| ops (addOps.map toOp ++ takeOps)

/-- `[s] B` into slots 0–2, from the bits of `s` and the initial slots. -/
def combBase : Prog isa := .seq tblSetup (.seq combLoop combFinish)

/-! ## The encoding -/

/-- The output's address into `esi`, and the low bit of the fully reduced
`x` (slot 1) as the top bit of its 57th byte. -/
def signBit : List Instr :=
  [.mov .esi (.mem (at_ .esp 4)), ld .eax X2, .alu .and .eax (.imm 1), .shift .ror .eax 25,
    .store8 (at_ .esi 56) .al]

/-- `1/Z` into slot 21, `y = Y/Z` into slot 4 and `x = X/Z` into slot 1; `x`
fully reduced and its low bit written; `y` copied into slot 1, fully reduced
and written to the output's first 56 bytes; then the callee-saved registers
restored. -/
def baseEncode : Prog isa :=
  .seq invert <| .seq (ops [.mul (slot 4) (slot 1) (slot 21), .mul X2 (slot 0) (slot 21)]) <|
    .block (freeze ++ signBit ++ copy X2 (slot 4) ++ freeze ++
      (List.range 14).flatMap Impl.X448.X86.packWord ++ Impl.X448.X86.restore)

/-- `vg_ed448_scalar_base(out = [esp + 4], scalar = [esp + 8], scratch = [esp + 12])`. -/
def scalarBase : Prog isa := .seq baseEntry (.seq combBase baseEncode)

end VG.Impl.Ed448.X86
