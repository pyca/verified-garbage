import VerifiedGarbage.Impl.Ed25519.X86_64.Comb
import VerifiedGarbage.Impl.Ed25519.X86_64.Ifma

/-!
# Ed25519: base-point multiplication with a comb, with AVX512_IFMA

`Ifma.combMultiply` is `combMultiply`'s comb (the same digits, tables and
order of additions and doublings) with the accumulated point `(X, Y, Z, T)`
in the four lanes of `ymm0–ymm4`, as `Ifma.windows` keeps it, and each
addition of a table's entry done in two products of X25519's four-lane field
arithmetic (`mul4`):

1. `(Y - X, Y + X, T, Z) · (y - x, y + x, 2dt, 2) = (A, B, C, D)`;
2. with `E = B - A`, `F = D - C`, `G = D + C` and `H = B + A`,
   `(E, G, F, E) · (F, H, G, H) = (X', Y', Z', T')` (`dbl-2008-hwcd`'s last
   step, as `vdbl`'s).

The entry is selected as `combSelect` does but 32 bytes at a time
(`vselect`, into `ymm11–ymm13`, from the static `combSym`), the identity's
`1`s or'd in for a zero magnitude, and its words split into the limbs of the
lanes `(y - x, y + x, 2dt, 2)` (`eload`, with the slot `K2` holding `2`);
for a negative digit (the mask in `rcx`) the lanes `y - x` and
`y + x` are exchanged and `2dt` becomes `2¹¹ p - 2dt` (`vneg`). The five
doublings are `vdbl`'s, and `[G]B`'s entry is in slots 9–11, stored before the loop.

The loop runs between Intel's MXCSR prologue and epilogue (`withMx`, which
keeps MXCSR in `r11`; nothing in the loop writes `r11`). The digits, the
selection's masks and the sign are computed as `combMultiply` computes them,
and every address is the scratch or the static plus a public offset.
-/

namespace VG.Impl.Ed25519.X86_64.Ifma

open VG.X86_64
open VG.Impl.X25519.X86_64 (sc)
open VG.Impl.X25519.X86_64.Ifma (y ld st v srl sll perm blend zero lanes ord carry mul4 kb
  KM K19 KB0 KB1 OPL OPV)
open VG.Impl.Ed25519.X86_64 (offset combSym combEntryBytes combTblAt combEqMask combSelSetup combSignMask
  combIndex combChunk combSign constPointOps combG combGCached FieldOp fieldCode)

/-- The slot holding `2`, the entries' `2Z`. -/
def K2 : Nat := offset 7

/-- Before the loop: `[G]B` into slots 0–3, `2` into slot 7, and `[G]B`'s entry into slots
9–11. -/
def combConstOps : List FieldOp :=
  constPointOps combG ++ [.const 7 2, .const 9 combGCached.X, .const 10 combGCached.Y,
    .const 11 combGCached.Z]

/-! ## The entry, from its words -/

/-- From four rows of words in `ymm11–ymm14` (row `l`, word `k` in quadword `k` of
`ymm (11 + l)`), the limbs of the lanes into `ymm5–ymm9` (row `l` in lane `l`), as `vload`
splits slots 0–3 into `ymm0–ymm4`: the rows transposed, then shifted and masked. -/
def esplit : List Instr :=
  [v .vpunpcklqdq 5 11 12, v .vpunpckhqdq 6 11 12, v .vpunpcklqdq 7 13 14, v .vpunpckhqdq 8 13 14,
    .vop (.vperm2i128 (y 11) (y 5) (y 7) 0x20), .vop (.vperm2i128 (y 12) (y 6) (y 8) 0x20),
    .vop (.vperm2i128 (y 13) (y 5) (y 7) 0x31), .vop (.vperm2i128 (y 14) (y 6) (y 8) 0x31),
    ld 15 KM, v .vpand 5 11 15,
    srl 6 11 51, srl 10 15 13, v .vpand 10 12 10, sll 10 10 13, v .vpor 6 6 10,
    srl 7 12 38, srl 10 15 26, v .vpand 10 13 10, sll 10 10 26, v .vpor 7 7 10,
    srl 8 13 25, srl 10 15 39, v .vpand 10 14 10, sll 10 10 39, v .vpor 8 8 10,
    srl 9 14 12]

/-- The entry `[y - x, y + x, 2dt]` in `ymm11–ymm13` with `rax` (`1` for the identity, else
`0`) or'd into the first word of `y - x` and `y + x`, and `2` (slot `K2`), into the limbs of
the lanes of `ymm5–ymm9`. -/
def eload : List Instr :=
  [.vop (.vmovq (y 10) .rax), v .vpor 11 11 10, v .vpor 12 12 10, ld 14 K2] ++ esplit

/-- `vneg` with the mask already in each quadword of `ymm15`. -/
def vnegBody : List Instr :=
  (List.range 5).flatMap fun j =>
    [perm 10 (5 + j) (ord 1 0 2 3), ld 11 (kb j), v .vpsubq 11 11 (5 + j),
      blend 10 10 11 (lanes false false true false), v .vpxor 10 10 (5 + j), v .vpand 10 10 15,
      v .vpxor (5 + j) (5 + j) 10]

/-- The entry in the lanes of `ymm5–ymm9` negated if the mask `rcx` is all ones: lanes 0 and 1
exchanged, and lane 2 subtracted from the bias `2¹¹ p` (`kb`), under the mask in `ymm15`. -/
def vneg : List Instr :=
  [.vop (.vmovq (y 15) .rcx), .vop (.vpbroadcastq .l256 (y 15) (y 15))] ++ vnegBody

/-! ## An addition -/

/-- From `(X, Y, Z, T)` in `ymm0–ymm4`: `(Y - X, Y + X, T, Z)` into `ymm0–ymm4`, not carried
(with `ymm13` zero). -/
def vaddA : List Instr :=
  [zero 13] ++ (List.range 5).flatMap fun j =>
    [perm 10 j (ord 1 1 3 2), perm 11 j (ord 0 0 0 0), ld 12 (kb j), v .vpsubq 12 12 11,
      blend 11 11 12 (lanes true false false false), blend 11 11 13 (lanes false false true true),
      v .vpaddq j 10 11]

/-- `ymm0–ymm4` to `OPL`. -/
def vstA : List Instr := (List.range 5).map fun j => st (OPL + 32 * j) j

/-- From `(A, B, C, D)` in `ymm0–ymm4`: `(E, G, F, H) = (B - A, D + C, D - C, B + A)`, then
`(E, G, F, E)` into `ymm0–ymm4` and `(F, H, G, H)` into `ymm5–ymm9`, neither carried. -/
def vaddB : List Instr :=
  (List.range 5).flatMap fun j =>
    [perm 10 j (ord 1 3 3 1), perm 11 j (ord 0 2 2 0), ld 12 (kb j), v .vpsubq 12 12 11,
      blend 11 11 12 (lanes true false true false), v .vpaddq 10 10 11,
      perm j 10 (ord 0 1 2 0), perm (5 + j) 10 (ord 2 3 1 3)]

/-- The point in the lanes of `ymm0–ymm4` plus the entry in those of `ymm5–ymm9`. -/
def vadd : List Instr :=
  vaddA ++ carry id ++ vstA ++ mul4 OPL ++ vaddB ++ carry (5 + ·) ++ carry id ++ dblC ++ mul4 OPV

/-- The entry in `ymm11–ymm13` (with `rax` and the mask `rcx`) added to the point in the
lanes. -/
def ventry : List Instr := eload ++ vneg ++ carry (5 + ·) ++ vadd

/-! ## The selection -/

/-- Entry `m` (from 1) of the table at `rdx`, its three 32-byte pieces kept in `ymm11–ymm13`
under the mask of `r8 = m`. -/
def vselEntry (m : Nat) : List Instr :=
  combEqMask m ++ [.vop (.vmovq (y 15) .rcx), .vop (.vpbroadcastq .l256 (y 15) (y 15))] ++
  (List.range 3).flatMap fun c =>
    [.vmovdquLoad .l256 (y 10) (combTblAt (combEntryBytes * (m - 1) + 32 * c)),
      v .vpand 10 10 15, v .vpor (11 + c) (11 + c) 10]

/-- The entry of table `rdx = j` for the magnitude `r8` into `ymm11–ymm13` (zero for a zero
magnitude). -/
def vselect : List Instr :=
  combSelSetup ++ [zero 11, zero 12, zero 13] ++ (List.range 16).flatMap fun m => vselEntry (m + 1)

/-- `rax = 1` if the magnitude `r8` is zero (else `0`), and the sign's mask into `rcx`. -/
def combFlags : List Instr :=
  [.mov .rax (.reg .r8), .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 1),
    .mov .rcx (.mem (sc combSignMask))]

/-- `[G]B`'s entry into `ymm11–ymm13`, from slots 9–11, with `rax = rcx = 0`. -/
def gEntry : List Instr :=
  [.mov32 .rax (.imm 0), .mov32 .rcx (.imm 0), ld 11 (offset 9), ld 12 (offset 10), ld 13 (offset 11)]

/-! ## The comb -/

/-- Four doublings of the lanes, counted by `rsi`. -/
def vdbl4 : Prog isa :=
  .seq (.block [.mov32 .rsi (.imm 4)]) (.loop (.block (vdbl ++ [.alu .sub .rsi (.imm 1)])) .ne)

/-- Five doublings of the lanes: `vdbl4`'s, and one more. -/
def vdbl5 : Prog isa := .seq vdbl4 (.block vdbl)

/-- Step `rbx`: before the even digits, the five doublings and `[G]B`; then the digit's entry
of table `r9`, negated for a negative digit, added. -/
def combStep : Prog isa :=
  .seq (.block [.alu .cmp .rbx (.imm 26)]) <|
  .seq (.ite .e (.seq vdbl5 (.block (gEntry ++ ventry))) (.block [])) <|
  .seq combIndex <|
  .seq combChunk <|
  .block (combSign ++ [.mov .r8 (.reg .rax), .mov .rdx (.reg .r9)] ++ vselect ++ combFlags ++
    ventry ++ [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 52)])

/-- `[s]B` into slots 0–3, for the scalar bits expanded into bytes 768 onward: `[G]B` into
the lanes (through slots 0–3), the constants (`combConstOps`, `vload`'s), and the 52 steps with
MXCSR `0x1FBF`. -/
def combMultiply (fld : Arith) : Prog isa :=
  .seq (.block (fieldCode fld combConstOps ++ VG.Impl.X25519.X86_64.Ifma.consts ++ vload))
    (withMx (.seq (.block [.mov32 .rbx (.imm 0)]) (.seq (.loop combStep .ne) (.block vstore))))

end VG.Impl.Ed25519.X86_64.Ifma
