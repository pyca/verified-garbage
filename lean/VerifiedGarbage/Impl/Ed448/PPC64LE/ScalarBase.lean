module

public import VerifiedGarbage.Impl.X448.PPC64LE
public import VerifiedGarbage.Spec.Ed448
public import VerifiedGarbage.Impl.Ed448.Comb

/-!
# Ed448 on PPC64LE: base-point multiplication

`vg_ed448_scalar_base(out = r3, scalar = r4, scratch = r5)`: the encoding of
`[s]B` for the 456-bit little-endian scalar `s`, without pruning.

X448's field code on this target (`Impl/X448/PPC64LE.lean`) does the
arithmetic: field elements are fourteen 32-bit limbs in the 56-byte slots
of the working space, and the operations are X448's `mul`, `add`, `sub`,
`cswap`, `invert` and `freeze`. Points are the specification's projective
coordinates `(X : Y : Z)`. The working space's base is in `r6`, as in
X448.

The multiplication is RISC-V's four-column comb (`combLoop`, below): `R`
starts as the neutral point `(0 : 1 : 1)` (`combInit`), and each of 114 rows
doubles it and adds the affine table entry of four bits of the scalar, 114
apart. The table's sixteen entries (`Impl/Ed448/Comb.lean`) are built once
at `CTAB`, past the field slots (`tabBuild`), and every row reads all of them
(`combSelect`). The scalar's bits are expanded into bytes at X448's `BITS`
(byte `t` is bit `t`), as X448 expands its scalar. Finally `R` is encoded
(§5.2.2): `Z` inverted (X448's `invert`, `Z` being in its slot `Z2`),
`x = X/Z` fully reduced into `out` for its low bit, then `y = Y/Z`, and the
bit as the top bit of the 57th byte.

The slots `P`, `T`, the addition's temporaries and `sel` serve verification's
equation (`VerifyEquation.lean`), whose loop runs RFC 8032's addition
(`addition`) of `R` and `P`.

The function writes only volatile registers, the link register and `r14`,
which it loads back before it returns; it calls the two functions of the
comb's point operations (below). The only branches are on the loop counters, and
every address is a pointer plus a constant or a counter, so only the
pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.Ed448.PPC64LE

open VG.PPC64LE
open VG.Impl.X448.PPC64LE (mul add sub cswap invert freeze bitsBody BITS R X2 Z2)

/-! ## The slots -/

def RX : Nat := X2
def RY : Nat := 0
def RZ : Nat := Z2
def PX : Nat := 168
def PY : Nat := 224
def PZ : Nat := 280
def DK : Nat := 336
def TX : Nat := 392
def TY : Nat := 448
def TZ : Nat := 504
/-- The addition's temporaries (`B` and `E` are in `TY` and `TZ`, `H`'s
second factor and `AF` in `TX`, `AG` in `TY`, which they leave in time). -/
def TA : Nat := 560
def TC : Nat := 616
def TD : Nat := 672
def TF : Nat := 728
def TG : Nat := 784
def TH : Nat := R
/-! ## Constants -/

/-- Word `k` of `v`, as `lis` and `ori` build it and `stw` stores it. -/
def constLimb (o v k : Nat) : List Instr :=
  [.lis .r7 (BitVec.ofNat 16 (v / 2 ^ (32 * k + 16))), .ori .r7 .r7 (BitVec.ofNat 16 (v / 2 ^ (32 * k))),
    .store .w .r7 .r6 (o + 4 * k)]

/-- The element `v` into the slot at `o`. -/
def constField (o v : Nat) : List Instr := (List.range 14).flatMap (constLimb o v)

/-! ## The bits of the scalar -/

/-- `BITS[8i + j] = bit j of scalar[i]`, for the 57 bytes at `r4`. -/
def baseBits : Prog isa :=
  .seq (.block [.addi .r9 .r6 0, .li .r11 57]) (.loop (.block bitsBody) (.nonzero .d .r11))

/-! ## The loop -/

/-- Limb `k` of `[q]`, or of `[r]` if the mask `r11` is all ones, into limb
`k` of `[o]`. -/
def selStep (o q r k : Nat) : List Instr :=
  [.load .w .r5 .r6 (q + 4 * k), .load .w .r7 .r6 (r + 4 * k), .logic .xor .r7 .r7 .r5,
    .logic .and .r7 .r7 .r11, .logic .xor .r5 .r5 .r7, .store .w .r5 .r6 (o + 4 * k)]

def sel (o q r : Nat) : List Instr := (List.range 14).flatMap (selStep o q r)

/-- `T = R + P` (RFC 8032 §5.2.4's addition, in its order): `A = Z₁Z₂`,
`B = A²`, `C = X₁X₂`, `D = Y₁Y₂`, `E = dCD`, `F = B - E`, `G = B + E`,
`H = (X₁ + Y₁)(X₂ + Y₂)`, `X₃ = AF(H - C - D)`, `Y₃ = AG(D - C)`,
`Z₃ = FG`. -/
def addition : Prog isa :=
  .seq (mul TA RZ PZ) <| .seq (mul TY TA TA) <| .seq (mul TC RX PX) <| .seq (mul TD RY PY) <|
  .seq (mul TZ DK TC) <| .seq (mul TZ TZ TD) <| .seq (.block (sub TF TY TZ)) <|
  .seq (.block (add TG TY TZ)) <| .seq (.block (add TH RX RY)) <| .seq (.block (add TX PX PY)) <|
  .seq (mul TH TH TX) <| .seq (mul TX TA TF) <| .seq (.block (sub TH TH TC)) <|
  .seq (.block (sub TH TH TD)) <| .seq (mul TX TX TH) <| .seq (mul TY TA TG) <|
  .seq (.block (sub TH TD TC)) <| .seq (mul TY TY TH) (mul TZ TF TG)

/-! ## The encoding -/

/-- `1/Z` into `R`; `x = X/Z` fully reduced into `out`, and its low bit as
bit 7 of `r12`; `y = Y/Z` fully reduced into `out`, and the bit as the top
bit of its 57th byte. -/
def baseEncode : Prog isa :=
  .seq invert <| .seq (mul X2 RX R) <|
  .seq (.block (freeze ++ [.lbz .r12 .r3 0, .li .r9 1, .logic .and .r12 .r12 .r9, .lsl .r12 .r12 7])) <|
  .seq (mul X2 RY R) (.block (freeze ++ [.stb .r12 .r3 56]))

/-! ## The four-column comb

The base-point multiplication proper (`scalarBase`): RISC-V's comb
(`Impl/Ed448/RISCV64/ScalarBase.lean`, x86-64's: `Impl/Ed448/Comb.lean`'s
table of the sixteen affine points `[i₀ + 2¹¹⁴ i₁ + 2²²⁸ i₂ + 2³⁴² i₃] B`),
114 rows from the top, each a doubling of `R` (`combDblOps`, RFC 8032 §5.2.4's
doubling), the table entry of the row's four bits selected by a full masked
scan (`combSelect`) into `(SX : SY : 1)`, and its addition to `R` in place
(`combAddOps`, the addition with `Z₂ = 1`). The table is built once at `CTAB`,
past the field slots, from literals (`tabBuild`).

A conditional branch reaches 32 KiB, and a row of inlined field operations
is longer, so the two point operations are functions the loop calls,
`vg_ed448_r32_double` and `vg_ed448_r32_add_affine`: X448's field
operations on the slots at `r6`, which they write only volatile registers
of (`r4`, `r5`, `r7`–`r11`), so that the row's counter stays in `r3` across
the calls. While the loop runs, the return address is kept at `LRS`, and
`out` in the nonvolatile `r14`, whose value is kept at `R14S` and loaded back
before the function returns (a value loaded from memory is secret to the
constant-time analysis, so `out` itself never goes through memory). -/

/-- The selected entry `(x, y)`. -/
def SX : Nat := 168
def SY : Nat := 224

/-- The point operations' temporaries. -/
def U0 : Nat := 280
def U1 : Nat := 392
def U2 : Nat := 448
def U3 : Nat := 504
def U4 : Nat := 560
def U5 : Nat := 616
def U6 : Nat := 672
def U7 : Nat := 728
def U8 : Nat := 784

/-- The table: entry `i`'s `x` at `CTAB + 112 i`, its `y` at `CTAB + 112 i + 56`. -/
def CTAB : Nat := 2048

/-- The return address and the caller's `r14`, while the loop runs: past the table. -/
def LRS : Nat := 3840
def R14S : Nat := 3848

/-- A field operation of X448's. -/
inductive COp where
  | mul (o x y : Nat)
  | add (o x y : Nat)
  | sub (o x y : Nat)

def COp.code : COp → Prog isa
  | .mul o x y => Impl.X448.PPC64LE.mul o x y
  | .add o x y => .block (Impl.X448.PPC64LE.add o x y)
  | .sub o x y => .block (Impl.X448.PPC64LE.sub o x y)

/-- The operations in order. -/
def opsProg : List COp → Prog isa
  | [] => .block []
  | op :: ops => .seq op.code (opsProg ops)

/-- `R = 2R` (RFC 8032 §5.2.4): `B = (X + Y)²`, `C = X²`, `D = Y²`,
`E = C + D`, `H = Z²`, `J = E - 2H`, `X = (B - E) J`, `Y = E (C - D)`,
`Z = E J`. -/
def combDblOps : List COp :=
  [.add U0 RX RY, .mul U0 U0 U0, .mul U1 RX RX, .mul U2 RY RY, .add U3 U1 U2, .mul U4 RZ RZ,
    .add U5 U4 U4, .sub U5 U3 U5, .sub U6 U0 U3, .mul RX U6 U5, .sub U7 U1 U2, .mul RY U3 U7,
    .mul RZ U3 U5]

/-- `R = R + (SX : SY : 1)` (RFC 8032 §5.2.4's addition with `A = Z₁`):
`B = Z₁²`, `C = X₁x`, `D = Y₁y`, `E = dCD`, `F = B - E`, `G = B + E`,
`H = (X₁ + Y₁)(x + y)`, `X₃ = Z₁F(H - C - D)`, `Y₃ = Z₁G(D - C)`,
`Z₃ = FG`, each coordinate of `R` written once its last use is past. -/
def combAddOps : List COp :=
  [.mul U1 RZ RZ, .mul U2 RX SX, .mul U3 RY SY, .mul U4 DK U2, .mul U4 U4 U3, .sub U5 U1 U4,
    .add U6 U1 U4, .add U7 RX RY, .add U8 SX SY, .mul U7 U7 U8, .mul U8 RZ U5, .sub U7 U7 U2,
    .sub U7 U7 U3, .mul RX U8 U7, .mul U8 RZ U6, .sub U7 U3 U2, .mul RY U8 U7, .mul RZ U5 U6]

/-- The doubling, a function. -/
def callDbl : Prog isa := .call "vg_ed448_r32_double" (opsProg combDblOps)

/-- The affine addition, a function. -/
def callAdd : Prog isa := .call "vg_ed448_r32_add_affine" (opsProg combAddOps)

/-- The table at `CTAB`. -/
def tabBuild : List Instr :=
  (List.range 16).flatMap fun i =>
    constField (CTAB + 112 * i) (Comb.entry i).1.val ++ constField (CTAB + 112 * i + 56) (Comb.entry i).2.val

/-- `R = (0 : 1 : 1)` and `d`. -/
def combInit : List Instr :=
  constField RX Spec.Ed448.identity.X.val ++ constField RY Spec.Ed448.identity.Y.val ++
    constField RZ Spec.Ed448.identity.Z.val ++ constField DK Spec.Ed448.d.val

/-- The row's index into `r10`: bits `t`, `t + 114`, `t + 228` and `t + 342`
of the scalar (`t = r3`), as `i₀ + 2 i₁ + 4 i₂ + 8 i₃`. -/
def combDigit : List Instr :=
  [.add .r9 .r6 .r3, .lbz .r10 .r9 (BITS + 342), .lbz .r8 .r9 (BITS + 228),
    .add .r10 .r10 .r10, .add .r10 .r10 .r8, .lbz .r8 .r9 (BITS + 114), .add .r10 .r10 .r10,
    .add .r10 .r10 .r8, .lbz .r8 .r9 BITS, .add .r10 .r10 .r10, .add .r10 .r10 .r8]

/-- Doubleword `k` of entry `i` into doubleword `k` of `(SX, SY)` if the
mask `r11` is all ones. -/
def selWord (i k : Nat) : List Instr :=
  [.load .d .r4 .r6 (SX + 8 * k), .load .d .r5 .r6 (CTAB + 112 * i + 8 * k), .logic .and .r5 .r5 .r11,
    .logic .or .r4 .r4 .r5, .store .d .r4 .r6 (SX + 8 * k)]

/-- Entry `i`, under the mask `r11 = -((i ⊕ r10) - 1 >> 63)`: all ones
exactly when `r10 = i`. -/
def selEntry (i : Nat) : List Instr :=
  [.li .r4 i, .logic .xor .r4 .r4 .r10, .subi .r4 .r4 1, .lsr .d .r4 .r4 63, .li .r11 0,
    .sub .r11 .r11 .r4] ++ (List.range 14).flatMap (selWord i)

/-- `(SX, SY)` zeroed, then every entry scanned. -/
def combSelect : List Instr :=
  .li .r4 0 :: (List.range 14).flatMap (fun k => [.store .d .r4 .r6 (SX + 8 * k)]) ++
    (List.range 16).flatMap selEntry

/-- One row, `t = r3 - 1`. -/
def combStep : Prog isa :=
  .seq (.block [.subi .r3 .r3 1]) <| .seq callDbl <| .seq (.block (combDigit ++ combSelect)) callAdd

/-- The 114 rows, from 113 down to 0. -/
def combLoop : Prog isa := .seq (.block [.li .r3 114]) (.loop combStep (.nonzero .d .r3))

/-- The return address and `r14` kept, and `out` into `r14`. -/
def combSave : List Instr := [.mflr .r7, .store .d .r7 .r6 LRS, .store .d .r14 .r6 R14S, .addi .r14 .r3 0]

/-- And loaded back. -/
def combRestore : List Instr := [.load .d .r7 .r6 LRS, .mtlr .r7, .addi .r3 .r14 0, .load .d .r14 .r6 R14S]

/-- `vg_ed448_scalar_base(out = r3, scalar = r4, scratch = r5)`. -/
def scalarBase : Prog isa :=
  .seq (.block (.addi .r6 .r5 0 :: combSave ++ combInit ++ tabBuild)) <| .seq baseBits <|
    .seq combLoop <| .seq (.block combRestore) baseEncode

end VG.Impl.Ed448.PPC64LE
