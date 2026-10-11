import VerifiedGarbage.Impl.Ed25519.X86.Point32
import VerifiedGarbage.Impl.Ed25519.CombTable
import VerifiedGarbage.Impl.Ed25519.X86.PointSelect
import VerifiedGarbage.Impl.Ed25519.X86.PointLoop

/-!
# Ed25519: base-point multiplication with a comb, two digits per table

The scalar's 64 nibbles `n_i` (from its bits, expanded one per byte at byte
7168 of the workspace) give `[s]B = Σ d_i [16^i]B + [17 G]B` for the digits
`d_i = n_i - 8`, from `-8` to `7`, and `G = 8 Σ_{j < 32} 256^j`. Table `j`
holds `[k]([256^j]B)` for `k ≤ 8` (`combCached`), affine and cached. Step `j`
selects from table `j` the entries of both digits that use it, `d_{2j+1}` and
`d_{2j}`, sharing each candidate's load between the two selections, and
adds them, or their negations, to two accumulators, which start at `[G]B`:
`A` (slots 0–3) for the odd digits and `B` (slots 17–20) for the even ones.
At the end, `[s]B = 16 A + B`: four doublings and one addition. That is 64
additions of affine cached points (seven multiplications each), four
doublings and one addition, as ref10's `ge_scalarmult_base` (and so
OpenSSL's) does with its signed radix-16 table. The additions to `A` are calls
of `vg_ed25519_r32_add_affine`, the doublings calls of `vg_ed25519_r32_double`
and the last addition a call of `vg_ed25519_r32_point_add`; the additions to
`B` are inline (`addEvenOps`), and come first in each step, since the calls'
working space includes the slots of `B`'s entry.

The digits are secret: their entries are selected in constant time. The
masks of the nine magnitudes `k = 0 … 8` of each digit (all ones exactly for
`|d|`) are stored in the workspace (`combOddMasks`, `combEvenMasks`). The 32
tables (of the entries `k = 1 … 8`, 768 bytes each) are the static `combSym`
(`combWords`), whose address the function stores at byte `combTbl` of the
workspace (`combAddr`). Each word of a candidate is loaded from the table once,
ANDed with both digits' masks and ORed into `ebx` (odd) and `ebp` (even): every
entry of the table is read, at addresses from the static's and the loop's
counter. Each entry is negated, or not, with the mask of its digit's sign
(`combOddSign`, `combEvenSign`: all ones if the nibble is below 8), by
exchanging `Y - X` and `Y + X` and choosing between `2dT` and its negation.
The loop's counter `esi`, which is also the table index, is public, and so are
the addresses of the bits (`edi + 8 esi` plus a constant).
-/

namespace VG.Impl.Ed25519.X86

open VG.X86
open VG.Impl.X25519.X86 (sc at_)

/-- Byte of the workspace holding the odd digit's nine masks, a word each. -/
def combOddMasks : Nat := 1024

/-- Byte of the workspace holding the even digit's nine masks. -/
def combEvenMasks : Nat := 1088

/-- Byte of the workspace holding the mask of the odd digit's sign. -/
def combOddSign : Nat := 1152

/-- Byte of the workspace holding the mask of the even digit's sign. -/
def combEvenSign : Nat := 1156

/-- The same addition, of the even digits' entry in slots 13–15 to their accumulator in
slots 17–20. -/
def addEvenOps : List FieldOp := [
  .sub 8 18 17, .mul 8 8 13, .add 9 18 17, .mul 9 9 14, .mul 10 20 15, .add 11 19 19,
  .add 12 9 8, .sub 8 9 8, .add 9 11 10, .sub 10 11 10,
  .mul 17 8 10, .mul 18 9 12, .mul 19 10 9, .mul 20 8 12]

/-- Four doublings, calls of `vg_ed25519_r32_double`, with the counter `esi`. -/
def double4 : Prog isa :=
  .seq (.block [.mov .esi (.imm 4)]) (.loop (.seq Point32.doubleCall (.block [.alu .sub .esi (.imm 1)])) .ne)

/-- `edx = edi + 8 esi`: the bits of the table `esi`'s digits are at `edx + 7168` (even) and
`edx + 7172` (odd). -/
def combBits : List Instr :=
  [.mov .edx (.reg .esi), .alu .add .edx (.reg .edx), .alu .add .edx (.reg .edx),
    .alu .add .edx (.reg .edx), .alu .add .edx (.reg .edi)]

/-- `eax` = the nibble `b₀ + 2b₁ + 4b₂ + 8b₃` of the bits at `edx + o`, by Horner's rule. -/
def combNibble (o : Nat) : List Instr :=
  [.movzx8 .eax (at_ .edx (o + 3)), .alu .add .eax (.reg .eax), .movzx8 .ecx (at_ .edx (o + 2)),
    .alu .add .eax (.reg .ecx), .alu .add .eax (.reg .eax), .movzx8 .ecx (at_ .edx (o + 1)),
    .alu .add .eax (.reg .ecx), .alu .add .eax (.reg .eax), .movzx8 .ecx (at_ .edx o),
    .alu .add .eax (.reg .ecx)]

/-- From the nibble `n` in `eax`: the sign's mask (all ones if `n < 8`, from the borrow of
`n - 8`) to byte `sign`, and `|n - 8|` into `eax`. -/
def combSign (sign : Nat) : List Instr :=
  [.alu .sub .eax (.imm 8), .alu .sbb .ecx (.reg .ecx), .store (sc sign) .ecx,
    .alu .xor .eax (.reg .ecx), .alu .sub .eax (.reg .ecx)]

/-- The mask of candidate `k` to byte `masks + 4k`: all ones if `eax = k`, else zero
(`eax ⊕ k - 1` borrows exactly when `eax = k`). -/
def combMask (masks k : Nat) : List Instr :=
  [.mov .ecx (.reg .eax), .alu .xor .ecx (.imm (BitVec.ofNat 32 k)), .alu .sub .ecx (.imm 1),
    .alu .sbb .ecx (.reg .ecx), .store (sc (masks + 4 * k)) .ecx]

/-- The masks of the nine candidates. -/
def combMaskAll (masks : Nat) : List Instr := (List.range 9).flatMap (combMask masks)

/-- The odd digit `d_{2j+1}` (bits at `edx + 7172`): its sign's and magnitudes' masks; then
the even digit `d_{2j}` (bits at `edx + 7168`): its masks. -/
def combDigits : List Instr :=
  combBits ++ combNibble 7172 ++ combSign combOddSign ++ combMaskAll combOddMasks ++
    combNibble 7168 ++ combSign combEvenSign ++ combMaskAll combEvenMasks

/-- Word `w` of a field element. -/
def feWord (v : Spec.X25519.Fe) (w : Nat) : BitVec 32 := BitVec.ofNat 32 (v.val / (2 ^ 32) ^ w)

/-! ## The tables -/

/-- The static holding the comb's tables. -/
def combSym : String := "VG_ED25519_COMB"

/-- Byte of the workspace holding the static's address. -/
def combTbl : Nat := 1160

/-- Word `i` (of 64 bits) of the tables: table `j = i / 96` takes 768 bytes, the `Y - X`
(`c = 0`), the `Y + X` (`c = 1`) and the `2dT` (`c = 2`) of its entries `m + 1 = 1 … 8`, four
words each. -/
def combWord (i : Nat) : BitVec 64 :=
  let e := combCached (i / 96) (i % 32 / 4 + 1)
  BitVec.ofNat 64 ((if i % 96 < 32 then e.X else if i % 96 < 64 then e.Y else e.Z).val /
    2 ^ (64 * (i % 4)))

/-- The words of the 32 tables, as the static `combSym` holds them. -/
def combWords : List (BitVec 64) := (List.range (32 * 96)).map combWord

/-- The static the comb reads. -/
def combConsts : List (String × List (BitVec 64)) := [(combSym, combWords)]

/-- The static's address, obtained in a balanced four-byte CALL frame (`symPush`; the saved
`eip` is popped into `ecx`), stored at byte `combTbl` of the workspace, whose address is
argument `i`. -/
def combAddr (i : Nat) : Prog isa :=
  .seq (.frame (.symPush .eax combSym) (.block []) (.pop .ecx 1))
    (.block [.mov .edx (.mem (at_ .esp (4 + 4 * i))), .store (at_ .edx combTbl) .eax])

/-- `ecx` = the address of table `esi`: the static's, plus 768 bytes a table (`eax = 256 esi`,
added three times). -/
def tblAddr : List Instr :=
  [.mov .eax (.reg .esi)] ++ List.replicate 8 (.alu .add .eax (.reg .eax)) ++
    [.mov .ecx (.mem (sc combTbl))] ++ List.replicate 3 (.alu .add .ecx (.reg .eax))

/-- Word `w` of candidate `k`, at `ecx + d`: loaded, masked with each digit's mask and ORed into
`ebx` (odd) and `ebp` (even). -/
def selectCand (d k : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .ecx d)), .mov .edx (.reg .eax),
    .alu .and .eax (.mem (sc (combOddMasks + 4 * k))),
    .alu .and .edx (.mem (sc (combEvenMasks + 4 * k))),
    .alu .or .ebx (.reg .eax), .alu .or .ebp (.reg .edx)]

/-- The start of word `w`'s selections: `1` for `|d| = 0` in word 0 of the identity's `Y - X`
and `Y + X` (`one`), else `0`. -/
def selectStart (one : Bool) (w : Nat) : List Instr :=
  if one && w == 0 then
    [.mov .ebx (.mem (sc combOddMasks)), .alu .and .ebx (.imm 1),
      .mov .ebp (.mem (sc combEvenMasks)), .alu .and .ebp (.imm 1)]
  else [.mov .ebx (.imm 0), .mov .ebp (.imm 0)]

/-- Word `w` of entry `|d|`'s coordinate `c` (at `ecx + 256 c`) for both digits, to bytes
`o + 4w` (odd) and `e + 4w` (even); entry 0's (the identity's) is `1` (if `one`) or `0`. -/
def selectWord (one : Bool) (c o e w : Nat) : List Instr :=
  selectStart one w ++
    (List.range 8).flatMap (fun m => selectCand (256 * c + 32 * m + 4 * w) (m + 1)) ++
    [.store (sc (o + 4 * w)) .ebx, .store (sc (e + 4 * w)) .ebp]

/-- Coordinate `c` of entry `|d|` for both digits, to bytes `o` (odd) and `e` (even). -/
def selectField (one : Bool) (c o e : Nat) : List Instr :=
  (List.range 8).flatMap fun w => selectWord one c o e w

/-- The entries of both digits from table `esi`: the odd one to slots 4–6, the even one to
slots 13–15. -/
def combSelect : List Instr :=
  tblAddr ++ selectField true 0 (offset 4) (offset 13) ++
    selectField true 1 (offset 5) (offset 14) ++ selectField false 2 (offset 6) (offset 15)

/-- The cached point in slots `a`, `b`, `c` negated if its digit is negative, that is if the
mask of its sign at byte `sign` is all ones: `[Y - X, Y + X, 2dT]` becomes
`[Y + X, Y - X, -2dT]`, by exchanging slots `a` and `b`, and slots `c` and 8 (`0 - 2dT`, with
zero in slot 21). -/
def combNeg (a b c : Slot) (sign : Nat) : List Instr :=
  fieldCode [.sub 8 21 c] ++ [.mov .ecx (.mem (sc sign))] ++ swapFields [(a, b), (c, 8)]

/-- Step `esi = j`: both digits' entries of table `j`, negated for negative digits, added to
their accumulators, `B`'s first. ZF is clear while another step follows. -/
def combStep : Prog isa :=
  .seq (.block combDigits) <|
  .seq (.block combSelect) <|
  .seq (.block (combNeg 13 14 15 combEvenSign ++ fieldCode addEvenOps ++ combNeg 4 5 6 combOddSign)) <|
  .seq Point32.affCall <|
  .block [.alu .add .esi (.imm 1), .alu .cmp .esi (.imm 32)]

/-- Both accumulators at `[G]B`, zero in slot 21, and the counter. -/
def combInit : List Instr :=
  fieldCode ([.const 21 0] ++ constPointOps combG ++
    [.const 17 combG.X, .const 18 combG.Y, .const 19 combG.Z, .const 20 combG.T]) ++
    [.mov .esi (.imm 0)]

/-- `16 A + B` into slots 0–3 (with `d` in slot 16). -/
def combFinish : Prog isa :=
  .seq double4 (.seq (.block (fieldCode [.copy 4 17, .copy 5 18, .copy 6 19, .copy 7 20])) Point32.addCall)

/-- `[s]B` into slots 0–3, for the scalar bits expanded into bytes 7168 onward, `d` in slot 16
and the tables' address at byte `combTbl`. -/
def combMultiply : Prog isa :=
  .seq (.block combInit) (.seq (.loop combStep .ne) combFinish)

end VG.Impl.Ed25519.X86
