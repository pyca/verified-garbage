import VerifiedGarbage.Impl.Ed25519.X86_64.BaseOdd
import VerifiedGarbage.Impl.Ed25519.X86_64.Cached
import VerifiedGarbage.Impl.Ed25519.X86_64.Point64

/-!
# Verification's equation with signed sliding windows

Verification may leak its inputs, so its scalars `S` and `k` are public. It computes
`[k]A - [S]B` with one chain of doublings (`dblOpsH`), one per bit, from the top. Both scalars
are first recoded into signed odd digits (`recodeAll`): `k`'s below 16 in absolute value, at
least five bits apart, from a table of `±[1]A … ±[15]A` built at run time (byte 5376); `S`'s
below 128, at least eight bits apart, from the static `baseOddSym` of `∓[1]B … ∓[127]B`;
both cached for addition (`[Y - X, Y + X, 2dT, 2Z]`, `addCachedOps`). Each position with a
nonzero digit adds its entry; a doubling computes `T`, which only an addition reads, only
before one. `k`'s bytes above its low 32 that are zero (`skipZero`), and the leading zero
digits, are skipped: they would only double the identity. The equation `[S]B = R + [k]A`
holds exactly when the result equals `-R`, which the projective comparison `pointEqual`
checks.

The additions, and the table's doubling, are the point operations `pt` (`Point64.Ops`): in the
code, calls of `vg_ed25519_r64_add_cached_ext` and `_proj` and of `vg_ed25519_r64_double_ext`
(`Point64.calls`), which run as their bodies would inlined (`Point64.bodies`), as the proofs
take them. The chain's doublings, one per bit, stay inline (`dblIn`): as calls, saving and
restoring the registers they write would cost more than their code saves.
-/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64
open VG.Impl.X25519.X86_64 (at_ sc stores loads)

/-- A table entry addressed by `rax` to slots 4–7. -/
def pointFromTableQ : List Instr :=
  (List.range 4).flatMap fun j => fromTableWords (32 * j) ++ stores (192 + 32 * j) .r8 .r9 .r10 .r11

/-- `rax` = byte `o` of the scratch. -/
def tableStart (o : Nat) : List Instr := [.movImm64 .rax (BitVec.ofNat 64 o), .alu .add .rax (.reg .rdi)]

/-- Doubles slots 0–3 in place with `dbl-2008-hwcd` (for `a = -1`) with every coordinate
negated, the same point, which saves a subtraction: `A = X²`, `B = Y²`, `C = 2Z²`, `E = 2XY`,
`G = B - A`, `F = C - G`, `H = A + B`, and `X = EF`, `Y = GH`, `Z = FG`, and `T = EH` if `t`
(only an addition reads `T`): the comb's doublings (`vg_ed25519_scalar_base`) and the chain's
(`dblIn`). -/
def dblOpsH (t : Bool) : List FieldOp :=
  [.sqr 8 0, .sqr 9 1, .sqr2 10 2, .mul2 11 0 1,
    .sub 12 9 8, .sub 13 10 12, .add 14 8 9, .mul 0 11 13, .mul 1 12 14, .mul 2 13 12] ++
    if t then [.mul 3 11 14] else []

/-- Four doublings: three without `T`, with the counter `rsi`, then one with it. -/
def double4 (fld : Arith) : Prog isa :=
  .seq (.block [.mov32 .rsi (.imm 3)]) (.seq
    (.loop (.block (fieldCode fld (dblOpsH false) ++ [.alu .sub .rsi (.imm 1)])) .ne)
    (.block (fieldCode fld (dblOpsH true))))

/-- Slots 8–11 = the point in slots 0–3 cached for addition, `[Y - X, Y + X, 2dT, 2Z]`
(`d` in slot 16). -/
def cacheOps : List FieldOp := [.sub 8 1 0, .add 9 1 0, .mul2 10 3 16, .add 11 2 2]

/-- Slots 8–11 to the table entry addressed by `rax`. -/
def cachedToTable : List Instr :=
  (List.range 4).flatMap fun j => loads (320 + 32 * j) .r8 .r9 .r10 .r11 ++ tableWords (32 * j)

/-- Slots 0–3 negated in place, `(-X, Y, Z, -T)` (slot 8 holds `0`). -/
def negOps : List FieldOp := [.const 8 0, .sub 0 8 0, .sub 3 8 3]

/-- The point in slots 0–3 to entries `rbx` (cached) and `rbx + 1` (its negation, cached) of
the table at byte 5376, keeping it in slots 0–3. -/
def aTableStore (fld : Arith) : List Instr :=
  fieldCode fld cacheOps ++ tableAddr 5376 ++ cachedToTable ++ fieldCode fld (negOps ++ cacheOps) ++
    tableAddr 5504 ++ cachedToTable ++ fieldCode fld negOps

/-- `[2]A` cached at byte 3216 (doubled by `vg_ed25519_r64_double_ext`), then `[1]A` (from byte
7424) into slots 0–3 and entries 0 and 1. -/
def aTableInit (fld : Arith) (pt : Point64.Ops) : Prog isa :=
  .seq (.block (tableStart 7424 ++ pointFromTable)) <| .seq (pt.dbl true) <|
    .block (fieldCode fld cacheOps ++ tableStart 3216 ++ cachedToTable ++ tableStart 7424 ++
      pointFromTable ++ ([.mov32 .rbx (.imm 0)] : List Instr) ++ aTableStore fld ++ [.mov32 .rbx (.imm 2)])

/-- Slots 0–3 plus `[2]A` (by `vg_ed25519_r64_add_cached_ext`), to entries `rbx` and `rbx + 1`. -/
def aTableBody (fld : Arith) (pt : Point64.Ops) : Prog isa :=
  .seq (.block (tableStart 3216 ++ pointFromTableQ)) <| .seq (pt.add true) <|
    .block (aTableStore fld ++ [.alu .add .rbx (.imm 2), .alu .cmp .rbx (.imm 16)])

/-- Entries `2m` and `2m + 1` (`m < 8`) of the table at byte 5376 are `[2m + 1]A` and
`-[2m + 1]A`, cached. -/
def aTable (fld : Arith) (pt : Point64.Ops) : Prog isa := .seq (aTableInit fld pt) (.loop (aTableBody fld pt) .ne)

/-- `rbx` = byte `counter` of the scalar at the pointer stored at byte `ptr` of the scratch,
plus `add`. -/
def digitByte (ptr add : Nat) : List Instr :=
  [.mov .rsi (.mem (sc ptr)), .alu .add .rsi (.imm (BitVec.ofNat 32 add)), .mov .rax (.mem (sc 56)),
    .movzx8 .rbx { base := .rsi, index := some .rax }]

/-! ## The scalars' digits

Each scalar is recoded into signed digits, odd and below `2 ^ (w - 1)` in absolute value, at
least `w` positions apart (`k` with `w = 5`, `S` with `w = 8`), from its lowest bit: at bit
`i`, with the carry `c` from below, a bit equal to `c` gives a zero digit (and keeps `c`);
otherwise the `w` bits from `i` plus `c` make an odd `W`, the digit `W` (carry 0) or
`W - 2 ^ w` (carry 1), and the next `w - 1` digits are zero. A digit `d` is stored as the
byte `u = d` if positive and `u = 1 - d` if negative, the table entry `u - 1`: entries `2m`
and `2m + 1` are `[2m + 1]` and `-[2m + 1]` of the point. Position `p`'s digit of `k` is at byte
`2048 + 2p`, `S`'s at byte `2049 + 2p`. -/

/-- The digits' array, 1056 bytes from byte 2048, zeroed (`rax` = 0). -/
def zeroDigits : List Instr :=
  ([.mov32 .rax (.imm 0)] : List Instr) ++ (List.range 132).map fun j => .store (sc (2048 + 8 * j)) .rax

/-- `k`'s 64 bytes to byte 3104 of the scratch, followed by eight zero bytes; `S`'s 32 to byte
3176, followed by eight zero bytes. -/
def copyScalars : List Instr :=
  [.mov .rsi (.mem (sc 7952))] ++
    ((List.range 8).flatMap fun j => [.mov .rax (.mem (at_ .rsi (8 * j))), .store (sc (3104 + 8 * j)) .rax]) ++
    [.mov .rsi (.mem (sc 7944))] ++
    ((List.range 4).flatMap fun j =>
      [.mov .rax (.mem (at_ .rsi (32 + 8 * j))), .store (sc (3176 + 8 * j)) .rax]) ++
    [.mov32 .rax (.imm 0), .store (sc 3168) .rax, .store (sc 3208) .rax]

/-- `rbx` = the scalar copied at byte `src` from bit `rsi` on (at least 57 bits): the word at its
byte `rsi / 8`, shifted right by `rsi % 8` with conditional moves. -/
def recodeBits (src : Nat) : List Instr :=
  [.mov .rax (.reg .rsi), .shift .shr .rax 3,
    .mov .rbx (.mem { base := .rdi, index := some .rax, disp := (src : Int) }),
    .mov .rcx (.reg .rsi), .alu .and .rcx (.imm 7)] ++
  ([4, 2, 1].flatMap fun k =>
    [.mov .rdx (.reg .rbx), .shift .shr .rdx k, .alu .test .rcx (.imm (BitVec.ofNat 32 k)),
      .cmov .ne .rbx (.reg .rdx)])

/-- ZF set if bit `rsi` (in `rbx`) equals the carry `r8`. -/
def recodeTest : List Instr := [.mov .rax (.reg .rbx), .alu .and .rax (.imm 1), .alu .cmp .rax (.reg .r8)]

/-- The digit at bit `rsi`: `W` = the `w` bits plus the carry, its byte to the array (`dst` 0
for `k`, 1 for `S`), and `rsi` moved `w` bits on. -/
def recodeWindow (w dst : Nat) : Prog isa :=
  .seq (.block [.alu .and .rbx (.imm (BitVec.ofNat 32 (2 ^ w - 1))), .alu .add .rbx (.reg .r8),
      .alu .cmp .rbx (.imm (BitVec.ofNat 32 (2 ^ (w - 1))))])
    (.seq (.ite .b (.block [.mov32 .r8 (.imm 0)])
      (.block [.mov32 .rax (.imm (BitVec.ofNat 32 (2 ^ w + 1))), .alu .sub .rax (.reg .rbx),
        .mov .rbx (.reg .rax), .mov32 .r8 (.imm 1)]))
    (.block [.mov .rax (.reg .rsi), .alu .add .rax (.reg .rax),
      .store8 { base := .rdi, index := some .rax, disp := ((2048 + dst : Nat) : Int) } .rbx,
      .alu .add .rsi (.imm (BitVec.ofNat 32 w))]))

/-- One step of the recoding, from bit `rsi` with the carry `r8`. -/
def recodeStep (src w dst : Nat) : Prog isa :=
  .seq (.block (recodeBits src ++ recodeTest))
    (.ite .e (.block [.alu .add .rsi (.imm 1)]) (recodeWindow w dst))

/-- The last carry, if any, as the digit 1 at bit `rsi`. -/
def recodeEnd (dst : Nat) : Prog isa :=
  .seq (.block [.alu .test .r8 (.reg .r8)]) (.ite .ne
    (.block [.mov .rax (.reg .rsi), .alu .add .rax (.reg .rax), .mov32 .rbx (.imm 1),
      .store8 { base := .rdi, index := some .rax, disp := ((2048 + dst : Nat) : Int) } .rbx])
    (.block []))

/-- The recoding of the scalar copied at byte `src`, while `rsi` is below the bound that `bound`
compares it with (CF set while it is). -/
def recode (src w dst : Nat) (bound : List Instr) : Prog isa :=
  .seq (.block [.mov32 .rsi (.imm 0), .mov32 .r8 (.imm 0)])
    (.seq (.loop (.seq (recodeStep src w dst) (.block bound)) .b) (recodeEnd dst))

/-- `k`'s bound: the bits of the `c` bytes left by `skipZero` (the counter). -/
def boundK : List Instr := [.mov .rax (.mem (sc 56)), .shift .shl .rax 3, .alu .cmp .rsi (.reg .rax)]

/-- `S`'s bound: its 256 bits. -/
def boundS : List Instr := [.alu .cmp .rsi (.imm 256)]

/-- The counter from `c` bytes to `8c + 9` positions, one above the highest digit's. -/
def setTop : List Instr :=
  [.mov .rax (.mem (sc 56)), .shift .shl .rax 3, .alu .add .rax (.imm 9), .store (sc 56) .rax]

/-- Both scalars' digits. -/
def recodeAll : Prog isa :=
  .seq (.block (zeroDigits ++ copyScalars)) (.seq (recode 3104 5 0 boundK)
    (.seq (recode 3176 8 1 boundS) (.block setTop)))

/-! ## The windows -/

/-- ZF set if both digits at the counter's position are zero. -/
def digitsAt : List Instr :=
  [.mov .rax (.mem (sc 56)), .alu .add .rax (.reg .rax),
    .movzx8 .rbx { base := .rdi, index := some .rax, disp := 2048 },
    .movzx8 .rcx { base := .rdi, index := some .rax, disp := 2049 }, .alu .or .rbx (.reg .rcx)]

/-- `rbx` = the digit's byte at the counter's position (`dst` 0 for `k`, 1 for `S`), ZF set if
it is zero. -/
def digitAt (dst : Nat) : List Instr :=
  [.mov .rax (.mem (sc 56)), .alu .add .rax (.reg .rax),
    .movzx8 .rbx { base := .rdi, index := some .rax, disp := ((2048 + dst : Nat) : Int) }, .alu .test .rbx (.reg .rbx)]

/-- Add entry `rbx - 1` of the table at byte `o` (by `add`), unless `rbx` is zero. -/
def addDigit (o : Nat) (add : Prog isa) : Prog isa :=
  .ite .ne (.seq (.block [.alu .sub .rbx (.imm 1)]) (.seq (.block (tableAddr o ++ pointFromTableQ)) add))
    (.block [])

/-- `rax` = entry `rbx` of the static `baseOddSym`, 128 bytes an entry, from the static's
address at byte 7960 of the scratch. -/
def baseAddr : List Instr :=
  [.mov .rax (.reg .rbx), .movImm64 .rcx 128, .mul .rcx, .mov .rcx (.mem (sc 7960)),
    .alu .add .rax (.reg .rcx)]

/-- Add the cached `[dec d](-B)`, entry `rbx - 1` of the static, unless `rbx` is zero, without
`T`: it is a position's last addition. -/
def addBase (pt : Point64.Ops) : Prog isa :=
  .ite .ne (.seq (.block [.alu .sub .rbx (.imm 1)]) (.seq (.block (baseAddr ++ pointFromTableQ))
    (pt.add false))) (.block [])

/-- The digits at the counter's position added: `k`'s from the table at byte 5376, with `T` only
if `S`'s is nonzero, then `S`'s from the static. -/
def addsAt (pt : Point64.Ops) : Prog isa :=
  .seq (.block (digitAt 1)) (.ite .ne
    (.seq (.block (digitAt 0)) (.seq (addDigit 5376 (pt.add true))
      (.seq (.block (digitAt 1)) (addBase pt))))
    (.seq (.block (digitAt 0)) (addDigit 5376 (pt.add false))))

/-- A doubling of the chain, inline, computing `T` if `t`. -/
def dblIn (fld : Arith) (t : Bool) : Prog isa := .block (fieldCode fld (dblOpsH t))

/-- One doubling, computing `T` only if a digit at the counter's position will read it. -/
def dblAt (fld : Arith) : Prog isa :=
  .seq (.block digitsAt) (.ite .ne (dblIn fld true) (dblIn fld false))

/-- The position below: the counter moved down, a doubling and its digits. -/
def stepAt (fld : Arith) (pt : Point64.Ops) : Prog isa :=
  .seq (.block batchBegin) (.seq (dblAt fld) (.seq (addsAt pt) (.block batchTest)))

/-- Below the highest position, while both digits are zero and the accumulator is the identity:
the counter moved down, and ZF clear while the skipping goes on. -/
def skipTop : Prog isa :=
  .seq (.block (batchBegin ++ digitsAt)) (.ite .ne (.block [.alu .cmp .rax (.reg .rax)]) (.block batchTest))

/-- The windows, from the counter one above the highest digit's position, the accumulator the
identity: the leading zero digits skipped, then a doubling and the digits at each position. -/
def windowsWith (fld : Arith) (pt : Point64.Ops) : Prog isa :=
  .seq (.loop skipTop .ne) (.seq (addsAt pt) (.seq (.block batchTest)
    (.ite .ne (.loop (stepAt fld pt) .ne) (.block []))))

/-- The windows, calling the point additions with the field multiplications `fld`. -/
def windows (fld : Arith) : Prog isa := windowsWith fld (Point64.bodies fld)

/-! ## Skipping the leading zero bytes of `k` -/

/-- The counter moved back up by one, and ZF set: the skipping stops. -/
def skipStop : List Instr :=
  [.mov .rax (.mem (sc 56)), .alu .add .rax (.imm 1), .store (sc 56) .rax, .alu .cmp .rax (.reg .rax)]

/-- The counter `c` moved down to `c - 1`, and byte `c - 1` of `k`, ZF set if it is zero. -/
def skipLoad : List Instr := batchBegin ++ digitByte 7952 0 ++ [.alu .test .rbx (.reg .rbx)]

/-- ZF set when the counter is 32. -/
def counterCmp : List Instr := [.mov .rbx (.mem (sc 56)), .alu .cmp .rbx (.imm 32)]

/-- Below a zero byte, the counter stays down; ZF is clear while another byte of `k` alone
may be skipped. -/
def skipBody : Prog isa :=
  .seq (.block skipLoad) (.ite .ne (.block skipStop) (.block counterCmp))

/-- Skip the leading zero bytes of `k` above its low 32: they would only double the
identity. A challenge reduced modulo L has 32 of them. -/
def skipZero : Prog isa := .loop skipBody .ne

/-- `-R` from byte 7552 into slots 4–7. -/
def negR (fld : Arith) : List Instr :=
  tableStart 7552 ++ pointFromTableQ ++ fieldCode fld [.const 8 0, .sub 4 8 4, .sub 7 8 7]

def windowSetup : List Instr := constField 16 Spec.Ed25519.d

def windowInit (fld : Arith) : List Instr := constPoint fld Spec.Ed25519.identity ++ mulCounterInit 64

end VG.Impl.Ed25519.X86_64
