module

public import VerifiedGarbage.Impl.Ed25519.X86_64.CombTable
public import VerifiedGarbage.Impl.Ed25519.X86_64.VerifyWindow
public import VerifiedGarbage.Impl.Ed25519.X86_64.PointSelect

/-!
# Ed25519: base-point multiplication with a comb

The scalar's 52 chunks `n_i` of five bits (from the bits at byte 768 of the
scratch, one per byte; chunk 51 is bit 255 alone) give
`[s]B = Σ n_i [32^i]B = Σ d_i [32^i]B + [32 G + G]B` for the digits
`d_i = n_i - 16`, from `-16` to `15`, and `G = 16 Σ_{j < 26} 1024^j`.
Table `j` holds `[k]([1024^j]B)` for `k ≤ 16`, so, from `[G]B`, the odd
digits `d_{2j+1}` are added first, one from each table, as the entry `|d|` or
its negation; five doublings multiply their sum by 32, and `[G]B` is added
again; then the even digits `d_{2j}` are added from the same tables. That is
54 additions of affine cached points and five doublings.

The digit is secret: the tables are in the static `combSym` (`combWords`),
and the entry of table `j` for the digit's magnitude is selected in constant
time, every entry of the table loaded, 16 bytes at a time, at an address that
depends only on `j`, and kept (`pand`, `por`) under a mask that is all ones
exactly for the magnitude (in both quadwords of `xmm15`); a zero magnitude
selects zeros, which become the identity's `[1, 1, 0]`. The entry is negated,
or not, with the mask of the digit's sign (at byte 1152) by exchanging `Y - X`
and `Y + X` and choosing between `2dT` and its negation. The entries are
affine (`Z = 1`), so an addition multiplies by `2Z = 2` with an addition
(`pointAddAffine`). The loop's counter `rbx`, the bit index `rcx` and the
table index `r9` are public.
-/

@[expose] public section

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64
open VG.Impl.X25519.X86_64 (sc zero4 store4)

/-- Byte of the scratch holding the mask of the digit's sign. -/
def combSignMask : Nat := 1152

/-- A bit of the expanded scalar, at bit index `rcx + i`. -/
def combBit (dst : Reg) (i : Nat) : Instr :=
  .movzx8 dst { base := .rdi, index := some .rcx, disp := 768 + i }

/-- `rax` = the chunk `b₀ + 2b₁ + 4b₂ + 8b₃ + 16b₄` of the bits at index `rcx`, by Horner's
rule. -/
def combDigit : List Instr :=
  [combBit .rax 4, .alu .add .rax (.reg .rax), combBit .rdx 3, .alu .add .rax (.reg .rdx),
    .alu .add .rax (.reg .rax), combBit .rdx 2, .alu .add .rax (.reg .rdx),
    .alu .add .rax (.reg .rax), combBit .rdx 1, .alu .add .rax (.reg .rdx),
    .alu .add .rax (.reg .rax), combBit .rdx 0, .alu .add .rax (.reg .rdx)]

/-- `rax` = the top chunk, bit 255 alone, at index `rcx`. -/
def combDigitTop : List Instr := [combBit .rax 0]

/-- From the chunk `n` in `rax`: the sign's mask (all ones if `n < 16`, from the borrow of
`n - 16`) to byte `combSignMask`, and `|n - 16|` into `rax`. -/
def combSign : List Instr :=
  [.alu .sub .rax (.imm 16), .alu .sbb .rdx (.reg .rdx), .store (sc combSignMask) .rdx,
    .alu .xor .rax (.reg .rdx), .alu .sub .rax (.reg .rdx)]

/-! ## The selection, from the tables in the static `combSym` -/

/-- The accumulators of the selection: `xmm0`–`xmm5`, sixteen bytes of the entry each. -/
def combAcc (c : Nat) : XReg := [XReg.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5].getD c .xmm0

/-- `[rdx + d]`: byte `d` of the table at `rdx`. -/
def combTblAt (d : Nat) : MemOp := { base := .rdx, disp := d }

/-- `rcx` all ones if `r8 = v`, else zero (`v < 2^31`). -/
def combEqMask (v : Nat) : List Instr :=
  [.mov32 .rcx (.imm (BitVec.ofNat 32 v)), .alu .xor .rcx (.reg .r8), .alu .cmp .rcx (.imm 1),
    .alu .sbb .rcx (.reg .rcx)]

/-- Entry `m` (from 1) of the table at `rdx`, its six 16-byte pieces kept in the
accumulators under the mask of `r8 = m`. -/
def combSelEntry (m : Nat) : List Instr :=
  combEqMask m ++ [.xop (.movq .xmm15 .rcx), .xop (.bin .punpcklqdq .xmm15 .xmm15)] ++
  (List.range 6).flatMap fun c =>
    [.movdquLoad .xmm14 (combTblAt (combEntryBytes * (m - 1) + 16 * c)),
      .xop (.bin .pand .xmm14 .xmm15), .xop (.bin .por (combAcc c) .xmm14)]

/-- `rdx` = the address of table `rdx = j`, the static's plus `j` tables, through `rax` and
`rcx`. -/
def combSelSetup : List Instr :=
  [.mov .rax (.reg .rdx), .mov32 .rcx (.imm (BitVec.ofNat 32 combTblBytes)), .mul .rcx,
    .leaSym .rdx combSym, .alu .add .rdx (.reg .rax)]

/-- The entry of the table at `rdx` for the magnitude `r8` to slots 4–6: the accumulators
cleared, every entry kept under its mask, and stored (zero for a zero magnitude). -/
def combSelPass : List Instr :=
  (List.range 6).map (fun c => .xop (.bin .pxor (combAcc c) (combAcc c))) ++
  (List.range 16).flatMap (fun m => combSelEntry (m + 1)) ++
  (List.range 6).map fun c => .movdquStore (sc (offset 4 + 16 * c)) (combAcc c)

/-- For a zero magnitude `r8`, the identity's `Y - X = Y + X = 1` (the low words of slots 4
and 5 or'd with 1), through `rax` and `rcx`. -/
def combSelOne : List Instr :=
  [.mov .rcx (.reg .r8), .alu .cmp .rcx (.imm 1), .alu .sbb .rcx (.reg .rcx), .alu .and .rcx (.imm 1),
    .mov .rax (.mem (sc (offset 4))), .alu .or .rax (.reg .rcx), .store (sc (offset 4)) .rax,
    .mov .rax (.mem (sc (offset 5))), .alu .or .rax (.reg .rcx), .store (sc (offset 5)) .rax]

/-- Entry `r8` of table `rdx` (`combCached`, without its `2Z`) to slots 4–6. -/
def combSelect : List Instr := combSelSetup ++ combSelPass ++ combSelOne

/-- Sixteen bytes at `d` and at `e` exchanged if the mask in both quadwords of
`xmm15` is all ones: the `x ⊕ ((x ⊕ y) ∧ m)` of `cswap`, in `xmm0`–`xmm2`, so
that two loads and two stores exchange what eight and five instructions per
word did. Only SSE2, which every target of this code has. -/
def swapPieceX (d e : Nat) : List Instr :=
  [.movdquLoad .xmm0 (sc d), .movdquLoad .xmm1 (sc e), .xop (.bin .movdqa .xmm2 .xmm0),
    .xop (.bin .pxor .xmm2 .xmm1), .xop (.bin .pand .xmm2 .xmm15),
    .xop (.bin .pxor .xmm0 .xmm2), .xop (.bin .pxor .xmm1 .xmm2),
    .movdquStore (sc d) .xmm0, .movdquStore (sc e) .xmm1]

/-- The slots at `o` and `o + 32` exchanged if the mask `rcx` is all ones. -/
def swapFieldX (o : Nat) : List Instr :=
  [.xop (.movq .xmm15 .rcx), .xop (.bin .punpcklqdq .xmm15 .xmm15)] ++
    swapPieceX o (o + 32) ++ swapPieceX (o + 16) (o + 48)

/-- `2p - [x]` into `r8`–`r11` (`≡ -[x]`, for any four words): a borrow of
`2²⁵⁶ - 38 - [x]` is `2²⁵⁶ ≡ 38` too many, subtracted once, which cannot
borrow again, since the difference is then above `2²⁵⁶ - 76`. (`0 - [x]`, as
`sub` computes it, has to correct a second time: the borrow leaves a
difference below 38.) -/
def negWords (x : Nat) : List Instr :=
  [.movImm64 .r8 (BitVec.ofNat 64 (2 ^ 64 - 38)), .alu .sub .r8 (.mem (sc x)),
    .movImm64 .r9 (BitVec.allOnes 64), .alu .sbb .r9 (.mem (sc (x + 8))),
    .movImm64 .r10 (BitVec.allOnes 64), .alu .sbb .r10 (.mem (sc (x + 16))),
    .movImm64 .r11 (BitVec.allOnes 64), .alu .sbb .r11 (.mem (sc (x + 24))),
    .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)] ++
    [.alu .sub .r8 (.reg .rax), .alu .sbb .r9 (.imm 0), .alu .sbb .r10 (.imm 0),
      .alu .sbb .r11 (.imm 0), .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)]

/-- `[x]` negated if the mask `rcx` is all ones: `2p - [x]`, or `[x]` itself,
which `cmove` keeps (`test` sets `ZF` exactly for a zero mask). -/
def negField (x : Nat) : List Instr :=
  negWords x ++ [.alu .test .rcx (.reg .rcx), .cmov .e .r8 (.mem (sc x)),
    .cmov .e .r9 (.mem (sc (x + 8))), .cmov .e .r10 (.mem (sc (x + 16))),
    .cmov .e .r11 (.mem (sc (x + 24)))] ++ store4 x

/-- The cached point in slots 4–6 negated if the sign's mask is all ones:
`[Y - X, Y + X, 2dT]` becomes `[Y + X, Y - X, -2dT]`, by exchanging slots 4
and 5 and negating slot 6 under the mask in `rcx`. -/
def combNeg : List Instr :=
  [.mov .rcx (.mem (sc combSignMask))] ++ swapFieldX (offset 4) ++ negField (offset 6)

/-- `rcx` = the bit index of chunk `2 rbx + 1` (odd chunks, `rbx < 26`) or `2 (rbx - 26)`,
and `r9` = its table, `rbx` or `rbx - 26`. -/
def combIndex : Prog isa :=
  .seq (.block [.mov .rcx (.reg .rbx), .alu .add .rcx (.reg .rcx), .mov .r9 (.reg .rcx),
    .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .r9),
    .mov .r9 (.reg .rbx), .alu .cmp .rbx (.imm 26)])
    (.ite .b (.block [.alu .add .rcx (.imm 5)])
      (.block [.alu .sub .rcx (.imm 260), .alu .sub .r9 (.imm 26)]))

/-- The chunk at `rcx` into `rax`: bit 255 alone for step `rbx = 25` (chunk 51), else five
bits. -/
def combChunk : Prog isa :=
  .seq (.block [.alu .cmp .rbx (.imm 25)]) (.ite .e (.block combDigitTop) (.block combDigit))

/-- Five doublings: `double4`'s, and one with `T`. -/
def combDouble (fld : Arith) : Prog isa :=
  .seq (double4 fld) (.block (fieldCode fld (dblOpsH true)))

/-- `[G]B` added to slots 0–3. -/
def combAddG (fld : Arith) : List Instr :=
  fieldCode fld [.const 4 combGCached.X, .const 5 combGCached.Y, .const 6 combGCached.Z] ++
    pointAddAffine fld

/-- Step `rbx`: before the even digits, the five doublings and `[G]B`; then the digit's entry
of table `r9` (selected by `sel`, `combSelect` or `combSelectY`), negated for a negative digit,
added. -/
def combStep (fld : Arith) (sel : List Instr := combSelect) : Prog isa :=
  .seq (.block [.alu .cmp .rbx (.imm 26)]) <|
  .seq (.ite .e (.seq (combDouble fld) (.block (combAddG fld))) (.block [])) <|
  .seq combIndex <|
  .seq combChunk <|
  .seq (.block (combSign ++ [.mov .r8 (.reg .rax), .mov .rdx (.reg .r9)] ++ sel)) <|
  .block (combNeg ++ pointAddAffine fld ++ [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 52)])

/-- `[s]B` into slots 0–3, for the scalar bits expanded into bytes 768 onward, the entries
selected by `sel`. -/
def combMultiply (fld : Arith) (sel : List Instr := combSelect) : Prog isa :=
  .seq (.block (constPoint fld combG ++ [.mov32 .rbx (.imm 0)]))
    (.loop (combStep fld sel) .ne)

end VG.Impl.Ed25519.X86_64
