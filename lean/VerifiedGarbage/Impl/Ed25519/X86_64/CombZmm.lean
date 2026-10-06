import VerifiedGarbage.Impl.Ed25519.X86_64.CombIfma

/-!
# Ed25519: base-point multiplication with a comb, in `zmm` registers

`Zmm.combMultiply` is `Ifma.combMultiply`'s comb with two accumulated points,
one in each 256-bit half of `zmm0–zmm4` (half 0 in lanes 0 and 1 of each
register, half 1 in lanes 2 and 3): from `[G]B` in both, step `j` adds the
entry of table `j` for the odd digit `d_{2j+1}` to half 0 (`A`) and for the
even digit `d_{2j}` to half 1 (`B`), both at once. After the 26 steps, `A`
is doubled five times (as `ymm` lanes, `vdbl5`) and `B` added:
`[s]B = 32 A + B`, as in `combMultiply`'s order of additions.

Each `zmm` block of the step is the `ymm` code of `Ifma.combMultiply` with
each instruction on both halves at once (`toZ`): the same operation with
512-bit operands, each 32-byte row at `o` of the working space window
`[1024, 1792)` (the operands' slots and the constants) the 64-byte row at
`zrow o`, holding the row of each half, `vpblendd` a `vpternlogd` with a row
of dword masks (`maskRow`) through a register the block leaves free, and
`vperm2i128` two `vshufi32x4`. The selection is `Ifma.vselect`'s, each piece
of the table loaded once, as a `ymm` register, its two lanes copied to the
other half, and kept under the mask of each half's magnitude (`r8` for `A`,
`r10` for `B`); the digits' signs are in the slots `SGA` and `SGB`.

Everything runs between Intel's MXCSR prologue and epilogue (`withMx`), and
every address is the scratch or the static plus a public offset.
-/

namespace VG.Impl.Ed25519.X86_64.Zmm

open VG.X86_64
open VG.Impl.X25519.X86_64 (sc)
open VG.Impl.X25519.X86_64.Ifma (y ld st v perm zero mov blend lanes carry mul4 KM K19 KB0 KB1 OPL)
open VG.Impl.Ed25519.X86_64 (combSym combEntryBytes combTblAt combEqMask combSelSetup combSignMask
  combIndex combChunk combSign fieldCode FieldOp constPointOps combG offset)
open VG.Impl.Ed25519.X86_64.Ifma (esplit vnegBody vadd vdbl5 vload vstore withMx)

/-! ## The layout of the scratch beyond the `ymm` code's -/

/-- The 64-byte rows of the window `[1024, 1792)` of the `ymm` code. -/
def ZB : Nat := 4224
/-- The row of the `zmm` code for the 32-byte row at `o` of the `ymm` code. -/
def zrow (o : Nat) : Nat := ZB + 2 * (o - 1024)
/-- The rows of dword masks of `vpblendd`'s selectors (`blendSels`). -/
def ZMASK : Nat := 5760
/-- `(2, 0, 0, 0)` in each half: the entries' `2Z`. -/
def ZK2 : Nat := 6016
/-- The accumulated points at the end, `A` in the low 32 bytes of each row. -/
def ZACC : Nat := 6080
/-- The masks of the digits' signs, of `A` and of `B`. -/
def SGA : Nat := 6560
def SGB : Nat := 6568

/-- The selectors of the `vpblendd`s of the translated blocks. -/
def blendSels : List (BitVec 8) :=
  [lanes true false false false, lanes false false true true, lanes true false true false,
    lanes false false true false]

/-- The row of the masks of selector `sel`: each doubleword all ones if `sel` takes it from
`vpblendd`'s second source, in each half. -/
def maskRow (sel : BitVec 8) : Nat := ZMASK + 64 * blendSels.idxOf sel

/-! ## The translation -/

/-- The 512-bit operation of a 256-bit `VBinOp`. -/
def zbin : VBinOp → ZBinOp
  | .vpaddq => .vpaddq | .vpsubq => .vpsubq | .vpand => .vpandq | .vpor => .vporq
  | .vpxor => .vpxord | .vpunpcklqdq => .vpunpcklqdq | .vpunpckhqdq => .vpunpckhqdq
  | _ => .vpaddd

/-- `[rdi + o]` as `[rdi + zrow o]`. -/
def zmem (m : MemOp) : MemOp := { m with disp := (ZB : Int) + 2 * (m.disp - 1024) }

/-- An instruction of the `ymm` code on both halves (`t`: the free register of a blend). -/
def toZ (t : Nat) : Instr → List Instr
  | .vop (.vbin op .l256 d a b) => [.zop (.zbin (zbin op) d a b)]
  | .vop (.vshift .psllq .l256 d a n) => [.zop (.vshift .vpsllq d a n)]
  | .vop (.vshift .psrlq .l256 d a n) => [.zop (.vshift .vpsrlq d a n)]
  | .vop (.vpermq d a o) => [.zop (.vpermq d a o)]
  | .vop (.vpmadd52luq .l256 d a b) => [.zop (.vpmadd52 false d a b)]
  | .vop (.vpmadd52huq .l256 d a b) => [.zop (.vpmadd52 true d a b)]
  | .vop (.vmovdqa .l256 d a) => [.zop (.vmovdqa64 d a)]
  | .vop (.vpblendd .l256 d a b sel) =>
    [.vmovdqu32Load (y t) (sc (maskRow sel)), .zop (.vpternlogd (y t) a b 0xAC), .zop (.vmovdqa64 d (y t))]
  | .vop (.vperm2i128 d a b sel) =>
    [.zop (.vshufi32x4 d a b (if sel = 0x31 then 0xDD else 0x88)), .zop (.vshufi32x4 d d d 0xD8)]
  | .vmovdquLoad .l256 d m => [.vmovdqu32Load d (zmem m)]
  | .vmovdquStore .l256 m r => [.vmovdqu32Store (zmem m) r]
  | i => [i]

/-- A block of the `ymm` code on both halves. -/
def tzs (t : Nat) (is : List Instr) : List Instr := is.flatMap (toZ t)

/-- `zmm d` = the low halves of `zmm a` and `zmm b`. -/
def zlo (d a b : Nat) : Instr := .zop (.vshufi32x4 (y d) (y a) (y b) 0x44)

/-! ## The digits -/

/-- The even chunk `2 rbx` (through `rbx + 26`, as `combIndex` counts it): its magnitude into
`r10` and the mask of its sign to `SGB`; and the odd chunk `2 rbx + 1`: its magnitude into
`r8`, the mask of its sign to `SGA`, and the table `rbx` into `r9`. -/
def zdigits : Prog isa :=
  .seq (.block [.alu .add .rbx (.imm 26)]) <| .seq combIndex <| .seq combChunk <|
  .seq (.block ([.alu .sub .rbx (.imm 26)] ++ combSign ++
    [.mov .r10 (.reg .rax), .store (sc SGB) .rdx])) <|
  .seq combIndex <| .seq combChunk <|
  .block (combSign ++ [.mov .r8 (.reg .rax), .store (sc SGA) .rdx])

/-! ## The selection -/

/-- `rcx` all ones if `r10 = v`, else zero (`combEqMask` of `r10`). -/
def eqMaskB (v : Nat) : List Instr :=
  [.mov32 .rcx (.imm (BitVec.ofNat 32 v)), .alu .xor .rcx (.reg .r10), .alu .cmp .rcx (.imm 1),
    .alu .sbb .rcx (.reg .rcx)]

/-- Entry `m` (from 1) of the table at `rdx`, its three 32-byte pieces in both halves, kept in
`zmm11–zmm13` under the masks of `r8 = m` (half 0) and `r10 = m` (half 1). -/
def zselEntry (m : Nat) : List Instr :=
  combEqMask m ++ [.vop (.vmovq (y 15) .rcx), .zop (.vpbroadcastq (y 15) (y 15))] ++
  eqMaskB m ++ [.vop (.vmovq (y 14) .rcx), .zop (.vpbroadcastq (y 14) (y 14)), zlo 15 15 14] ++
  (List.range 3).flatMap fun c =>
    [.vmovdquLoad .l256 (y 10) (combTblAt (combEntryBytes * (m - 1) + 32 * c)), zlo 10 10 10,
      .zop (.zbin .vpandq (y 10) (y 10) (y 15)), .zop (.zbin .vporq (y (11 + c)) (y (11 + c)) (y 10))]

/-- `rax = 1` if the magnitude `g` is zero, else `0`. -/
def isZero (g : Reg) : List Instr :=
  [.mov .rax (.reg g), .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 1)]

/-- The entries of table `rdx = j` for the magnitudes `r8` and `r10` into the halves of
`zmm11–zmm13`, the identity's `1`s or'd in for a zero magnitude, and `2` (`ZK2`) into
`zmm14`: in each half the rows that `esplit` splits. -/
def zselect : List Instr :=
  combSelSetup ++ [zero 11, zero 12, zero 13] ++ (List.range 16).flatMap (fun m => zselEntry (m + 1)) ++
  isZero .r8 ++ [.vop (.vmovq (y 10) .rax)] ++ isZero .r10 ++ [.vop (.vmovq (y 9) .rax), zlo 10 10 9,
    .zop (.zbin .vporq (y 11) (y 11) (y 10)), .zop (.zbin .vporq (y 12) (y 12) (y 10)),
    .vmovdqu32Load (y 14) (sc ZK2)]

/-- The masks of the signs, `SGA` in half 0 and `SGB` in half 1 of `zmm15`. -/
def zsign : List Instr :=
  [.mov .rcx (.mem (sc SGA)), .vop (.vmovq (y 14) .rcx), .zop (.vpbroadcastq (y 14) (y 14)),
    .mov .rcx (.mem (sc SGB)), .vop (.vmovq (y 15) .rcx), .zop (.vpbroadcastq (y 15) (y 15)),
    zlo 15 14 15]

/-! ## The comb -/

/-- Step `rbx`: the two digits' entries of table `rbx`, negated for a negative digit, added to
the two halves. -/
def combStep : Prog isa :=
  .seq zdigits <|
  .block ([.mov .rdx (.reg .r9)] ++ zselect ++ tzs 15 esplit ++ zsign ++ tzs 12 vnegBody ++
    tzs 15 (carry (5 + ·)) ++ tzs 15 vadd ++ [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 26)])

/-- Before the loop: `[G]B` into slots 0–3, and `1`, `1`, `2d` and `2` into slots 12–15, the
factors that turn `(Y - X, Y + X, T, Z)` into a cached point. -/
def zConstOps : List FieldOp :=
  constPointOps combG ++ [.const 12 1, .const 13 1, .const 14 (Spec.Ed25519.d + Spec.Ed25519.d), .const 15 2]

/-- The two lanes of `ymm9` in both halves of `zmm9`, to the 64-byte row at `d`. -/
def dupStore (d : Nat) : List Instr := [zlo 9 9 9, .vmovdqu32Store (sc d) (y 9)]

/-- The rows of the `zmm` code: the constants of the window and slot 15's `2` doubled (`zrow`,
`ZK2`), the masks of `blendSels` (from zero and all ones, `vpblendd`'s own), all through `ymm9`;
and the lanes of `ymm0–ymm4` copied to both halves. -/
def zconsts : List Instr :=
  ([(KM, zrow KM), (K19, zrow K19), (KB0, zrow KB0), (KB1, zrow KB1), (offset 15, ZK2)].flatMap fun e =>
    ld 9 e.1 :: dupStore e.2) ++
  [zero 10, v .vpcmpeqd 11 11 11] ++
  ((List.range blendSels.length).flatMap fun k =>
    blend 9 10 11 (blendSels.getD k 0) :: dupStore (ZMASK + 64 * k)) ++
  (List.range 5).map fun j => zlo j j j

/-- After the steps: the halves to `ZACC`, before `A`, in the lanes of `ymm0–ymm4`, is doubled
five times (`vdbl5`). -/
def ztail1 : List Instr :=
  (List.range 5).map fun j => .vmovdqu32Store (sc (ZACC + 64 * j)) (y j)

/-- `32 A` (in the lanes) plus `B`: `B`'s `(Y - X, Y + X, T, Z)` times `(1, 1, 2d, 2)` (slots
12–15, split as an entry), its cached point, carried into `ymm5–ymm9` and added (`vadd`). -/
def ztail2 : List Instr :=
  ((List.range 5).map fun j => st (ZACC + 64 * j) j) ++
  ((List.range 5).map fun j => ld j (ZACC + 64 * j + 32)) ++
  Ifma.vaddA ++ carry id ++ Ifma.vstA ++
  [ld 11 (offset 12), ld 12 (offset 13), ld 13 (offset 14), ld 14 (offset 15)] ++ esplit ++
  mul4 OPL ++ ((List.range 5).map fun j => mov (5 + j) j) ++ carry (5 + ·) ++
  ((List.range 5).map fun j => ld j (ZACC + 64 * j)) ++ vadd

/-- `[s]B` into slots 0–3, for the scalar bits expanded into bytes 768 onward: `[G]B` into
both halves of the lanes, the constants, the 26 steps, and `32 A + B`, with MXCSR `0x1FBF`. -/
def combMultiply (fld : Arith) : Prog isa :=
  .seq (.block (fieldCode fld zConstOps ++ VG.Impl.X25519.X86_64.Ifma.consts ++ vload ++ zconsts))
    (withMx (.seq (.block [.mov32 .rbx (.imm 0)]) (.seq (.loop combStep .ne)
      (.seq (.block ztail1) (.seq vdbl5 (.block (ztail2 ++ vstore)))))))

end VG.Impl.Ed25519.X86_64.Zmm
