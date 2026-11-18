module

public import VerifiedGarbage.Impl.Ecdsa.X86
public import VerifiedGarbage.Impl.Weierstrass.X86.Naf
public import VerifiedGarbage.Impl.Weierstrass.JacMul
public import VerifiedGarbage.Impl.Weierstrass.JacDblA
public import VerifiedGarbage.Impl.Weierstrass.Rcb0

/-!
# A point's multiplication by windows on x86 (32-bit)

`Cfg.winMul px py`: `R = [k]P` for the affine point `P` of the curve at the
slots `px`, `py` (its `Z` the slot of one) and the number `k < 2^(8 len)`
whose bits are table 0 (`bitsAt c.n 0`, a byte each, as `bits` writes them),
in the working space of ECDSA's signature (`Impl/Ecdsa/X86.lean`), for any
curve, as on 32-bit ARM (`Cfg.mulBody`, `Impl/Ecdsa/Arm.lean`):

1. the table of `[e]P` for every `e < 2^w` in projective coordinates, past
   the three tables of bits (`winTbl`), from `O` and `P` by complete
   additions (`winBuild`): `w` is four bits, or three for coordinates of more
   than six words, whose sixteen multiples would not fit the working space;
2. `R = O`, and for each window of `k`, from the top (`winStep`):
   `R = 2^w R` with `R` in Jacobian coordinates, by the Jacobian doubling for
   the curve's `a` (`dblJMul` for `a = -3`, `dblJ0` for 0, `dblJa` for any
   other), and back, with `Y = 1` where `Z = 0` (`winQuad`); the window's
   digit (`winDigit`: of the bits the scalar has, for the top one); its entry
   of the table, into `T`; and `R = R + T` by the complete addition.

The digits are secret, so an entry is selected as the comb selects its own
(`Impl/Weierstrass/X86/TComb.lean`): every entry of the table is loaded, 16
bytes at a time, at an address that depends only on the table's (`edi` plus
a constant), and kept under a mask that is all ones exactly when its number
is the digit (`TCombCfg.selPassAt`, six pieces of an entry to a scan of the
table). An entry is `winPc` pieces of 16 bytes: the `24 n` bytes of a point,
and for an odd `n` the 8 bytes after them, which are the first of `T0`'s
slot where the entry is selected to `T`, a temporary of the additions. The
table is stored the same way, 16 bytes at a time (`Naf.copyPieces`), at
`edi` plus a constant and a multiple of the counter.

The counter is `esi`, which the field arithmetic's functions keep, the only
branches are on it, and every address is `edi` plus a constant or a multiple
of the counter: nothing but `edi` and `esp` may affect timing. The field
operations are calls of the Montgomery functions (`fprog`), which keep `edi`,
so the code needs 20 bytes of stack.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.X86

open VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass

namespace Cfg

variable (c : Cfg)

/-- The bits of a window: four, or three for coordinates of more than six
words, whose sixteen multiples would not fit the working space past the
tables of bits. -/
def winW : Nat := if c.n ≤ 6 then 4 else 3

/-- The windows of an encoded scalar's `8 len` bits. -/
def winJ : Nat := (8 * c.C.len + c.winW - 1) / c.winW

/-- The bits of the top window that are the scalar's. -/
def winTop : Nat := 8 * c.C.len - c.winW * (c.winJ - 1)

/-- Where the table of the point's multiples is: past the three tables of
bits. -/
def winTbl : Nat := bitsAt c.n 3

/-- The pieces of 16 bytes of an entry of the table: the `24 n` bytes of a
point, and 8 more for an odd `n`. -/
def winPc : Nat := (3 * c.n + 1) / 2

/-- The Jacobian doubling of the curve: for `a = -3`, for `a = 0`, or for
any `a`. -/
def winDbl : RcbSlots → Pt → Pt → List FOp :=
  if c.C.a + 3 = c.C.p then dblJMul else if c.C.a = 0 then dblJ0 else dblJa

/-- The windows' complete addition: Algorithm 7 for `a = 0`, else
Algorithm 1. -/
def winAdd : RcbSlots → Pt → Pt → Pt → List FOp := if c.C.a = 0 then rcb0 else rcb

/-- The table's complete addition of the point, which is affine: Algorithm 8
for `a = 0`, else Algorithm 1. -/
def winAddM : RcbSlots → Pt → Pt → Pt → List FOp := if c.C.a = 0 then rcb0m else rcb

/-- Zero, as a point (`toJ` and `fromJ` add zero to copy). -/
def zeroPt : Pt := c.pt ZERO ZERO ZERO

/-- The comb whose scan of a table (`TCombCfg.selPassAt`) selects an entry of
the windows' table into `T`: entries of `winPc` pieces, `2^winW` of them
(the comb's `H`), numbered from 1. Only its `M.n`, `w` and `E` are read. -/
def winScan : TCombCfg where
  M := { c.MP' with n := c.winPc }
  F := c.SP
  ptr := 0
  S := c.rcbSlots
  A := c.pt RX RY RZ
  E := c.pt TX TY TZ
  D := c.pt DX DY DZ
  neg := c.sl TMP
  zero := c.sl ZERO
  bits := bitsAt c.n 0
  kbytes := 8 * c.C.len
  tsym := ""
  w := c.winW + 1
  J := c.winJ
  start := (0, 0)
  one := 0

/-- The window `esi` of the scalar, plus one, into `ebx`: of the bits the
scalar has, for the top one (the test of the counter is public). -/
def winDigit : Prog isa :=
  .seq (.block [.alu .cmp .esi (.imm (BitVec.ofNat 32 (c.winJ - 1)))]) <|
  .seq (.ite .e (.block (winIndex c.winW ++ hornerBits (bitsAt c.n 0) c.winTop))
    (.block (winIndex c.winW ++ hornerBits (bitsAt c.n 0) c.winW)))
    (.block [.mov .ebx (.reg .eax), .alu .add .ebx (.imm 1)])

/-- `edx` = the table's address. -/
def winTblPtr : List Instr := [.mov .edx (.reg .edi), .alu .add .edx (.imm (BitVec.ofNat 32 c.winTbl))]

/-- The scans of the table at `edx`, six pieces of an entry each, from pass
`i`, for `k` more: the entry whose number is `ebx` into `T`. -/
def winPasses : Nat → Nat → List Instr
  | 0, _ => []
  | k + 1, i => c.winScan.selPassAt (6 * i) (min 6 (c.winPc - 6 * i)) ++ winPasses k (i + 1)

/-- The entry `ebx - 1` of the table into `T`. -/
def winSel : List Instr := c.winTblPtr ++ c.winPasses ((c.winPc + 5) / 6) 0

/-- `edx` = the address of entry `esi` of the table, through `eax` and
`ecx`. -/
def winEntryAddr : List Instr :=
  [.mov .eax (.reg .esi), .mov .ecx (.imm (BitVec.ofNat 32 (16 * c.winPc))), .mul .ecx,
    .mov .edx (.reg .edi), .alu .add .edx (.imm (BitVec.ofNat 32 c.winTbl)), .alu .add .edx (.reg .eax)]

/-- `T` stored as entry `esi` of the table. -/
def winStore : List Instr :=
  c.winEntryAddr ++ Naf.copyPieces c.winPc (fun i => sc (c.sl TX + 16 * i)) (fun i => TCombCfg.tblAt (16 * i))

/-- `k` doublings from the Jacobian `p` (alternately into `q` and back), then
`R` = the result in projective coordinates. -/
def winDbls : Nat → Pt → Pt → Prog isa
  | 0, p, _ => fprog c.SP (fromJ c.rcbSlots p c.zeroPt (c.pt RX RY RZ))
  | k + 1, p, q => .seq (fprog c.SP (c.winDbl c.rcbSlots p q)) (winDbls k q p)

/-- `R = 2^winW R`: to Jacobian coordinates in `D`, the doublings between `D`
and `T`, back to `R`, then `Y = 1` where `Z` is zero. -/
def winQuad : Prog isa :=
  .seq (fprog c.SP (toJ c.rcbSlots (c.pt RX RY RZ) c.zeroPt (c.pt DX DY DZ))) <|
  .seq (c.winDbls c.winW (c.pt DX DY DZ) (c.pt TX TY TZ))
    (.block (c.nonzero (c.sl RZ) ++ ([.mov .ecx (.reg .edx)] : List Instr) ++
      sel (2 * c.n) (c.sl RY) (c.sl ONEP) (c.sl RY)))

/-- One window: `esi -= 1`, `R = 2^winW R`, the entry `T` of the window, and
`R = R + T`. -/
def winStep : Prog isa :=
  .seq (.block [decCounter]) <| .seq c.winQuad <| .seq c.winDigit <|
  .seq (.block c.winSel) <|
  .seq (fprog c.SP (c.winAdd c.rcbSlots (c.pt RX RY RZ) (c.pt TX TY TZ) (c.pt DX DY DZ)))
    (.block (copyPt c.n (c.pt RX RY RZ) (c.pt DX DY DZ) ++ [testCounter]))

/-- Entry `esi + 1` of the table, for the point at `px`, `py`: `T = D + P`,
stored, and `D = T`; then `ZF` once every entry is there. -/
def winBuildStep (px py : Nat) : Prog isa :=
  .seq (fprog c.SP (c.winAddM c.rcbSlots (c.pt DX DY DZ) (c.pt px py ONEP) (c.pt TX TY TZ))) <|
  .block (([.alu .add .esi (.imm 1)] : List Instr) ++ c.winStore ++
    copyPt c.n (c.pt DX DY DZ) (c.pt TX TY TZ) ++
    ([.alu .cmp .esi (.imm (BitVec.ofNat 32 (2 ^ c.winW - 1)))] : List Instr))

/-- The table: `O`, `P`, then `[e]P` for `e` from 2, each through `T`. -/
def winBuild (px py : Nat) : Prog isa :=
  .seq (.block (copyPt c.n (c.pt TX TY TZ) (c.pt ZERO ONEP ZERO) ++ ([.mov .esi (.imm 0)] : List Instr) ++
    c.winStore ++ copyPt c.n (c.pt TX TY TZ) (c.pt px py ONEP) ++
    copyPt c.n (c.pt DX DY DZ) (c.pt px py ONEP) ++ ([.mov .esi (.imm 1)] : List Instr) ++ c.winStore))
    (.loop (c.winBuildStep px py) .ne)

/-- `R = [k]P` for the point `P` at `px`, `py`, `ONEP` and the number `k`
whose bits are table 0: the table of `P`'s multiples, `R = O`, then the
windows. -/
def winMul (px py : Nat) : Prog isa :=
  .seq (c.winBuild px py) <|
  .seq (.block (copyPt c.n (c.pt RX RY RZ) (c.pt ZERO ONEP ZERO) ++
    ([.mov .esi (.imm (BitVec.ofNat 32 c.winJ))] : List Instr)))
    (.loop c.winStep .ne)

end Cfg

end VG.Impl.Ecdsa.X86
