module

public import VerifiedGarbage.Impl.Ed25519.BaseMultiples
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.PointMul

/-!
# Verification's equation on PPC64LE with 4-bit windows

As on RISC-V (`Impl/Ed25519/RISCV64/VerifyWindow.lean`): verification may
leak its inputs, so its scalars `S` and `k` are public. It computes
`[k]A - [S]B` with one chain of doublings (`dblOps`), four per 4-bit window
of the scalars, from the top: each window adds `[a]A` for `k`'s digit `a`
from a table of the cached `[1]A … [15]A` built at run time (byte `TA`), and
`-[b]B` for `S`'s digit `b`, in the low 64 windows, from the static `bSym`'s
cached `-[1]B … -[15]B` (`negBaseCached`), read in place. A zero digit adds
nothing. The digits are read from the scalars' bytes as the windows need
them (`nibble`). The windows are 64 when the challenge is below `2^256`
(always, from `vg_ed25519_verify`), 128 otherwise. The window counter is
`r15`, the table index `r16`, the static's address `r19` and the digit
`r9`; the counters and the address are nonvolatile, which the field code
never writes.
-/

@[expose] public section

namespace VG.Impl.Ed25519.PPC64LE

open VG.PPC64LE

/-- The table of the cached `[1]A … [15]A`. -/
def TA : Nat := 1632

/-- Doubles slots 0–3 in place with `dbl-2008-hwcd` (for `a = -1`): `A = X²`, `B = Y²`,
`C = 2Z²`, `E = 2XY`, `G = B - A`, `F = C - G`, `H = A + B`, and `X = EF`, `Y = GH`,
`Z = FG`, `T = EH`, which are those of the double negated. -/
def dblOps : List FieldOp :=
  [.mul 8 0 0, .mul 9 1 1, .mul 10 2 2, .add 10 10 10, .mul 11 0 1, .add 11 11 11,
    .sub 12 9 8, .sub 13 10 12, .add 14 8 9, .mul 0 11 13, .mul 1 12 14, .mul 2 13 12, .mul 3 11 14]

/-- `dblOps` without `T = EH`: doubling reads only `X`, `Y` and `Z`, so a
doubling another doubling follows need not compute `T`. -/
def dblOpsXYZ : List FieldOp :=
  [.mul 8 0 0, .mul 9 1 1, .mul 10 2 2, .add 10 10 10, .mul 11 0 1, .add 11 11 11,
    .sub 12 9 8, .sub 13 10 12, .add 14 8 9, .mul 0 11 13, .mul 1 12 14, .mul 2 13 12]

/-- Adds the cached point in slots 4–7 (`[Y - X, Y + X, 2dT, 2Z]`) to slots 0–3. -/
def pointAddCachedOps : List FieldOp := [
  .sub 8 1 0, .mul 8 8 4,
  .add 9 1 0, .mul 9 9 5,
  .mul 10 3 6, .mul 11 2 7,
  .sub 12 9 8, .sub 13 11 10, .add 14 11 10, .add 15 9 8,
  .mul 0 12 13, .mul 1 14 15, .mul 2 13 14, .mul 3 12 15]

/-- `[Y - X, Y + X, 2dT, 2Z]` of the point in slots 17–20 into slots 0–3, with `d` in slot 16. -/
def cacheOps : List FieldOp := [.sub 0 18 17, .add 1 18 17, .add 2 20 20, .mul 2 2 16, .add 3 19 19]

/-- The 128 bytes at `r14` to slots 4–7. -/
def pointFromTableQ : List Instr :=
  (List.range 4).flatMap fun j => unpackField (192 + 32 * j) (32 * j)

/-- The point in slots 0–3, cached, to entry `r16` of the table at `TA`; slots 0–3 are kept. -/
def storeCached : Prog isa :=
  .seq (fieldCode (savePointOps ++ cacheOps)) (.seq (.block (tableAddr TA ++ pointToTable)) restorePoint)

/-- `A` (in slots 0–3) cached into the table's entry 0 and into slots 4–7. -/
def aTableInit : Prog isa :=
  .seq (.block [.li .r16 0]) (.seq storeCached (.block (tableAddr TA ++ pointFromTableQ ++ [.li .r16 1])))

/-- Entry `r16` = entry `r16 - 1` (in slots 0–3) + `A` (cached in slots 4–7), cached; `r7` is
nonzero while another entry follows. -/
def aTableBody : Prog isa :=
  .seq (fieldCode pointAddCachedOps) (.seq storeCached (.block [.addi .r16 .r16 1, .subi .r7 .r16 15]))

/-- Entries `j < 15` of the table at `TA` are the cached `[j + 1]A`, for `A` in slots 0–3. -/
def aTable : Prog isa := .seq aTableInit (.loop aTableBody (.nonzero .d .r7))

/-- The static holding the cached `-[1]B … -[15]B`. -/
def bSym : String := "VG_ED25519_VERIFY_NEG_BASE"

/-- Coordinate `c` of a point: `X`, `Y`, `Z`, `T` for `c = 0, 1, 2, 3`. -/
def pointCoord (q : Spec.Ed25519.Point) : Nat → Spec.X25519.Fe
  | 0 => q.X
  | 1 => q.Y
  | 2 => q.Z
  | _ => q.T

/-- Word `i` of the static: word `i % 4` of coordinate `i / 4 % 4` of `negBaseCached (i / 16)`,
128 bytes an entry, as a table entry holds it. -/
def bWord (i : Nat) : BitVec 64 :=
  BitVec.ofNat 64 ((pointCoord (negBaseCached (i / 16)) (i / 4 % 4)).val / 2 ^ (64 * (i % 4)))

/-- The words of the 15 entries, as the static `bSym` holds them. -/
def bWords : List (BitVec 64) := (List.range 240).map bWord

/-- The static verification reads. -/
def bConsts : List (String × List (BitVec 64)) := [(bSym, bWords)]

/-- `r9` = nibble `r15` of the 32-byte scalar at `p + o`: the byte's low nibble `lo` and high
nibble `hi`, and `lo + (hi - lo) · (r15 mod 2)`, without a branch or a shift by a register. -/
def nibble (p : Reg) (o : Nat) : List Instr :=
  [.lsr .d .r8 .r15 1, .add .r8 p .r8, .lbz .r9 .r8 o, .lsr .d .r10 .r9 4, .lsl .r9 .r9 60,
    .lsr .d .r9 .r9 60, .sub .r10 .r10 .r9, .lsl .r8 .r15 63, .lsr .d .r8 .r8 63, .mul .r10 .r10 .r8,
    .add .r9 .r9 .r10]

/-- Add entry `r9 - 1` of the table at `TA` (cached `[r9]A`), unless `r9` is zero. -/
def addA : Prog isa :=
  .ite (.nonzero .d .r9)
    (.seq (.block ([.subi .r16 .r9 1] ++ tableAddr TA ++ pointFromTableQ)) (fieldCode pointAddCachedOps))
    (.block [])

/-- Add entry `r9 - 1` of the static (cached `-[r9]B`), unless `r9` is zero. -/
def addB : Prog isa :=
  .ite (.nonzero .d .r9)
    (.seq (.block ([.subi .r7 .r9 1, .lsl .r7 .r7 7, .add .r14 .r19 .r7] ++ pointFromTableQ))
      (fieldCode pointAddCachedOps))
    (.block [])

/-- `S`'s digit, in the low 64 windows (`r7` zero when `r15 < 64`). -/
def windowB : Prog isa :=
  .seq (.block [.lsr .d .r7 .r15 6])
    (.ite (.zero .d .r7) (.seq (.block (nibble .r30 32)) addB) (.block []))

/-- One window: the counter down, four doublings, `k`'s digit, then `S`'s. -/
def windowStep : Prog isa :=
  .seq (.block [.subi .r15 .r15 1])
    (.seq (fieldCode (dblOpsXYZ ++ dblOpsXYZ ++ dblOpsXYZ ++ dblOps))
      (.seq (.block (nibble .r31 0)) (.seq addA windowB)))

/-- Before the windows, for `A` in slots 0–3: `d`, the table of `A`, the static's address and
the identity. -/
def strausPrep : Prog isa :=
  .seq (fieldCode [.const 16 Spec.Ed25519.d]) (.seq aTable
    (.seq (.block [.adrSym .r19 bSym]) (constPoint Spec.Ed25519.identity)))

/-- The `r15` windows, from the top: `[k]A - [S]B` into slots 0–3. -/
def windows : Prog isa := .loop windowStep (.nonzero .d .r15)

end VG.Impl.Ed25519.PPC64LE
