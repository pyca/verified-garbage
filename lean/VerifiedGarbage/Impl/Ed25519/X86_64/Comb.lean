import VerifiedGarbage.Impl.Ed25519.X86_64.CombTable
import VerifiedGarbage.Impl.Ed25519.X86_64.VerifyWindow
import VerifiedGarbage.Impl.Ed25519.X86_64.PointSelect

/-!
# Ed25519: base-point multiplication with a comb

The scalar's 64 nibbles `n_i` (4-bit digits, from the bits at byte 768 of the
scratch) give `[s]B = Σ n_i [16^i]B = Σ d_i [16^i]B + [16 G + G]B` for the
digits `d_i = n_i - 8`, from `-8` to `7`, and `G = 8 Σ_{j < 32} 256^j`.
Table `j` holds `[k]([256^j]B)` for `k ≤ 8`, so, from `[G]B`, the odd digits
`d_{2j+1}` are added first, one from each table, as the entry `|d|` or its
negation; four doublings multiply their sum by 16, and `[G]B` is added again;
then the even digits `d_{2j}` are added from the same tables. That is 65
additions of affine cached points and four doublings.

The digit is secret: the tables are in the static `combSym` (`combWords`),
and the entry of table `j` for the digit's magnitude is selected in constant
time, every entry of the table loaded, 16 bytes at a time, at an address that
depends only on `j`, and kept (`pand`, `por`) under a mask that is all ones
exactly for the magnitude (in both quadwords of `xmm15`); a zero magnitude
selects zeros, which become the identity's `[1, 1, 0]`. The entry is negated,
or not, with the mask of the digit's sign (at byte 1152) by exchanging `Y - X`
and `Y + X` and choosing between `2dT` and its negation. The entries are
affine (`Z = 1`), so an addition multiplies by `2Z = 2` with an addition
(`pointAddAffine`). The loop's counter `rbx` and the table index `rdx` are
public.
-/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64
open VG.Impl.X25519.X86_64 (sc zero4 store4)

/-- Byte of the scratch holding the mask of the digit's sign. -/
def combSignMask : Nat := 1152

/-- A bit of the expanded scalar, at bit index `rcx + i`. -/
def combBit (dst : Reg) (i : Nat) : Instr :=
  .movzx8 dst { base := .rdi, index := some .rcx, disp := 768 + i }

/-- `rax` = the digit `b₀ + 2b₁ + 4b₂ + 8b₃` of the bits at index `rcx`, by Horner's rule. -/
def combDigit : List Instr :=
  [combBit .rax 3, .alu .add .rax (.reg .rax), combBit .rdx 2, .alu .add .rax (.reg .rdx),
    .alu .add .rax (.reg .rax), combBit .rdx 1, .alu .add .rax (.reg .rdx),
    .alu .add .rax (.reg .rax), combBit .rdx 0, .alu .add .rax (.reg .rdx)]

/-- From the nibble `n` in `rax`: the sign's mask (all ones if `n < 8`, from the borrow of
`n - 8`) to byte `combSignMask`, and `|n - 8|` into `rax`. -/
def combSign : List Instr :=
  [.alu .sub .rax (.imm 8), .alu .sbb .rdx (.reg .rdx), .store (sc combSignMask) .rdx,
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
  (List.range 8).flatMap (fun m => combSelEntry (m + 1)) ++
  (List.range 6).map fun c => .movdquStore (sc (offset 4 + 16 * c)) (combAcc c)

/-- For a zero magnitude `r8`, the identity's `Y - X = Y + X = 1` (the low words of slots 4
and 5 or'd with 1), through `rax` and `rcx`. -/
def combSelOne : List Instr :=
  [.mov .rcx (.reg .r8), .alu .cmp .rcx (.imm 1), .alu .sbb .rcx (.reg .rcx), .alu .and .rcx (.imm 1),
    .mov .rax (.mem (sc (offset 4))), .alu .or .rax (.reg .rcx), .store (sc (offset 4)) .rax,
    .mov .rax (.mem (sc (offset 5))), .alu .or .rax (.reg .rcx), .store (sc (offset 5)) .rax]

/-- Entry `r8` of table `rdx` (`combCached`, without its `2Z`) to slots 4–6. -/
def combSelect : List Instr := combSelSetup ++ combSelPass ++ combSelOne

/-- The cached point in slots 4–6 negated if the sign's mask is all ones:
`[Y - X, Y + X, 2dT]` becomes `[Y + X, Y - X, -2dT]`, by exchanging slots 4
and 5, and slots 6 and 8 (`-2dT`), under the mask in `rcx`. -/
def combNeg (fld : Arith) : List Instr :=
  fieldCode fld [.const 9 0, .sub 8 9 6] ++ [.mov .rcx (.mem (sc combSignMask))] ++
    swapFields [(4, 5), (6, 8)]

/-- `rcx` = the bit index of digit `2 rbx + 1` (odd digits, `rbx < 32`) or `2 (rbx - 32)`. -/
def combIndex : Prog isa :=
  .seq (.block [.mov .rcx (.reg .rbx), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx),
    .alu .add .rcx (.reg .rcx), .alu .cmp .rbx (.imm 32)])
    (.ite .b (.block [.alu .add .rcx (.imm 4)]) (.block [.alu .sub .rcx (.imm 256)]))

/-- `[G]B` added to slots 0–3. -/
def combAddG (fld : Arith) : List Instr :=
  fieldCode fld [.const 4 combGCached.X, .const 5 combGCached.Y, .const 6 combGCached.Z] ++
    pointAddAffine fld

/-- Step `rbx`: before the even digits, the four doublings and `[G]B`; then the digit's entry
of table `rbx mod 32`, negated for a negative digit, added. -/
def combStep (fld : Arith) : Prog isa :=
  .seq (.block [.alu .cmp .rbx (.imm 32)]) <|
  .seq (.ite .e (.seq (double4 fld) (.block (combAddG fld))) (.block [])) <|
  .seq combIndex <|
  .seq (.block (combDigit ++ combSign ++ [.mov .r8 (.reg .rax), .mov .rdx (.reg .rbx),
    .alu .and .rdx (.imm 31)] ++ combSelect)) <|
  .block (combNeg fld ++ pointAddAffine fld ++ [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 64)])

/-- `[s]B` into slots 0–3, for the scalar bits expanded into bytes 768 onward. -/
def combMultiply (fld : Arith) : Prog isa :=
  .seq (.block (constPoint fld combG ++ [.mov32 .rbx (.imm 0)]))
    (.loop (combStep fld) .ne)

end VG.Impl.Ed25519.X86_64
