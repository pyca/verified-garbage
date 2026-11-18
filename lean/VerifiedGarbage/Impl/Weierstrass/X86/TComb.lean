module

public import VerifiedGarbage.Impl.Weierstrass.X86
import VerifiedGarbage.Impl.Weierstrass.TCombWords

/-!
# Short Weierstrass curves on x86 (32-bit): a fixed-base comb from tables in memory

`[k]G` for the fixed point `G` and a scalar `k < 2^(w J)` whose bits are a
table of bytes (byte `t` is bit `t`, as `bits` writes it), from `J` tables of
constants in memory (the `static` `tsym`, `Artifact.consts`, whose address
the code forms with `symPush`): table `j` holds `[m 2^(wj)]G` for
`m = 1 … H` (`H = 2^(w-1)`), affine and in Montgomery form, entry `m` at
`16 n (m - 1)` bytes into the table (`x` then `y`, `n` words each), the
tables `16 n H` bytes apart (`tcombWords`). With the windows `k_j` of `w`
bits of `k` and the digits `d_j = k_j - H ∈ [-H, H)`,
`k = c + Σ d_j 2^(wj)` for `c = H Σ_{j<J} 2^(wj)`: the accumulator `A`
starts at `[c]G` (a constant), and iteration `j` adds the entry of table `j`
for `|d_j|` (or the point at infinity for `d_j = 0`), negated if `d_j < 0`,
by the complete addition (`rcb`, with `a` and `3b` in `S`), for
`j = J - 1` down to `0`: `J` additions, and no doublings (`comb`). This is
the comb of `Impl/Weierstrass/AArch64/TComb.lean`, with the same tables;
`TCombJ.lean` has the comb with Booth's digits and Jacobian additions, on
the same tables and selection.

The digits are secret, so their entries are selected in constant time: every
entry of the table is loaded, 16 bytes at a time, at an address that depends
only on `j` (public), into `xmm6`, and kept (`pand`, `por`) under a mask in
all four dwords of `xmm7` that is all ones exactly when its index is the
magnitude (`selEntryAt`); the entry accumulates in `xmm0`, …, `xmm5`, six
pieces to a scan of the table (`selPassAt`: coordinates of more than three
words take two), and is stored to `E`'s `x` and `y`, which are adjacent. The
entry's `Z` is `1` (Montgomery's, `R mod p`) unless the magnitude is zero,
when the entry is `(0 : 1 : 0)`. The negation computes `0 - y` and selects it
by the mask of the digit's sign.

The static's address is obtained in a four-byte stack frame with `symPush`
before the comb, and kept in the working space (`ptr`). The counter is `esi`,
and products of it with constants are by `mul`: the model has no left shift.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86

open VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass

/-- What the comb needs: the field, the complete addition's slots, the
accumulator `A`, the selected entry `E` (`E.y = E.x + 8 n`), the sum `D`, a
slot for `-y` and one holding zero, the table of the scalar's bits, the
digits' width `w` and number `J`, the name of the static holding the tables,
the start `[c]G` and `R mod p`, both in Montgomery form. -/
structure TCombCfg where
  M : Mod
  /-- The functions of the field arithmetic. -/
  F : Impl.Weierstrass.Mont.Modulus
  /-- Four-byte scratch slot retaining the public table pointer. -/
  ptr : Nat
  S : RcbSlots
  A : Pt
  E : Pt
  D : Pt
  neg : Nat
  zero : Nat
  bits : Nat
  /-- The bytes of the table of bits the scalar's bits fill; the code clears
  those up to `w J`. -/
  kbytes : Nat
  tsym : String
  w : Nat
  J : Nat
  start : Nat × Nat
  one : Nat

/-- The accumulators of the selection: `xmm0`, `xmm1`, …, sixteen bytes of the
entry each. -/
def selAcc (c : Nat) : XReg :=
  [XReg.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5].getD c .xmm0

/-- `ecx = edi + w (esi)`, through `eax` and `edx`. -/
def winIndex (w : Nat) : List Instr :=
  [.mov .eax (.reg .esi), .mov .ecx (.imm (BitVec.ofNat 32 w)), .mul .ecx, .mov .ecx (.reg .eax), .alu .add .ecx (.reg .edi)]

/-- `[ecx + d]`: byte `d` of the window at `ecx`. -/
def winByte (d : Nat) : MemOp := { base := .ecx, disp := d }

/-- `eax = Σ_{i<k} b_i 2^i` for the bytes `b_i` at `edi + ecx + d + i`, by
Horner's rule from the top, through `edx`. -/
def hornerBits : Nat → Nat → List Instr
  | _, 0 => [.mov .eax (.imm 0)]
  | d, k + 1 => hornerBits (d + 1) k ++ [.alu .add .eax (.reg .eax), .movzx8 .edx (winByte d),
      .alu .add .eax (.reg .edx)]

/-- From the window `v` in `eax`: `|v - H|` into `eax` and `ebx`, through `edx`. -/
def magnitudeH (H : Nat) : List Instr :=
  [.alu .sub .eax (.imm (BitVec.ofNat 32 H)), .mov .edx (.reg .eax), .shift .shr .edx 31,
    .mov .ebx (.imm 0), .alu .sub .ebx (.reg .edx), .alu .xor .eax (.reg .ebx), .alu .sub .eax (.reg .ebx),
    .mov .ebx (.reg .eax)]

/-- `ecx` all ones if `ebx = v`, else zero (`v < 2^31`). -/
def eqMask (v : Nat) : List Instr :=
  [.mov .ecx (.imm (BitVec.ofNat 32 v)), .alu .xor .ecx (.reg .ebx), .alu .cmp .ecx (.imm 1),
    .alu .sbb .ecx (.reg .ecx)]

/-- `[o] = [a]` for a point. -/
def copyPt (n : Nat) (o a : Pt) : List Instr := copy (2 * n) o.x a.x ++ copy (2 * n) o.y a.y ++ copy (2 * n) o.z a.z

namespace TCombCfg

variable (K : TCombCfg)

/-- `H = 2^(w-1)`, the entries of a table. -/
def H : Nat := 2 ^ (K.w - 1)

/-- The bytes of a table. -/
def tblBytes : Nat := 16 * K.M.n * K.H

/-- `[edx + d]`: byte `d` of the table at `edx`. -/
def tblAt (d : Nat) : MemOp := { base := .edx, disp := d }

/-- Pieces `c₀ …` (`cnt` of them, 16 bytes each, `cnt ≤ 6`) of entry `m` (from 1) of the table at
`edx`, kept in the accumulators under the mask of `ebx = m`. -/
def selEntryAt (c₀ cnt m : Nat) : List Instr :=
  eqMask m ++ [.xop (.movd .xmm7 .ecx), .xop (.pshufd .xmm7 .xmm7 0)] ++
  (List.range cnt).flatMap fun c =>
    [.movdquLoad .xmm6 (tblAt (16 * K.M.n * (m - 1) + 16 * c₀ + 16 * c)), .xop (.bin .pand .xmm6 .xmm7),
      .xop (.bin .por (selAcc c) .xmm6)]

/-- `edx` = table `esi`'s address, from the retained pointer at `ptr`,
through `eax` and `ecx`. -/
def selSetup : List Instr :=
  [.mov .eax (.reg .esi), .mov .ecx (.imm (BitVec.ofNat 32 K.tblBytes)), .mul .ecx,
    .mov .edx (.mem (sc K.ptr)), .alu .add .edx (.reg .eax)]

/-- Pieces `c₀ …` (`cnt` of them) of the entry of the table at `edx` for the magnitude in `ebx`
into `E`'s `x` and `y`: the accumulators cleared, every entry kept under its mask, and stored. -/
def selPassAt (c₀ cnt : Nat) : List Instr :=
  (List.range cnt).map (fun c => .xop (.bin .pxor (selAcc c) (selAcc c))) ++
  (List.range K.H).flatMap (fun m => K.selEntryAt c₀ cnt (m + 1)) ++
  (List.range cnt).map fun c => .movdquStore (sc (K.E.x + 16 * c₀ + 16 * c)) (selAcc c)

/-- The entry of table `esi` for the magnitude in `ebx` into `E`'s `x` and
`y`: its `n` pieces of 16 bytes in one scan of the table, or, for more than the six
accumulators, the first six in one and the others in a second. -/
def selPass : List Instr :=
  if K.M.n ≤ 6 then K.selPassAt 0 K.M.n else K.selPassAt 0 6 ++ K.selPassAt 6 (K.M.n - 6)

/-- `y = R` if the magnitude in `ebx` is zero (when the selected `y` is zero),
and `Z = R` unless it is, through `eax`, `ecx` and `edx`. -/
def selOne : List Instr :=
  setConst K.M.n K.E.z K.one ++
  [.mov .ecx (.reg .ebx), .alu .cmp .ecx (.imm 1), .alu .sbb .ecx (.reg .ecx)] ++
  sel (2 * K.M.n) K.E.y K.E.y K.E.z ++ sel (2 * K.M.n) K.E.z K.E.z K.zero

/-- The entry of table `esi` for the magnitude in `ebx` into `E`. -/
def select : List Instr := K.selSetup ++ K.selPass ++ K.selOne

/-- The digit's magnitude into `eax` and `ebx`: its window and `|k - H|`. -/
def digit : List Instr := winIndex K.w ++ hornerBits K.bits K.w ++ magnitudeH K.H

/-- `ecx` all ones if digit `esi` is negative, that is if the top bit of its
window is clear: `ecx = b_{w-1} - 1`, through `eax` and `edx`. -/
def signMask : List Instr :=
  winIndex K.w ++ [.movzx8 .eax (winByte (K.bits + K.w - 1)), .alu .sub .eax (.imm 1),
    .mov .ecx (.reg .eax)]

/-- `[y] = -[y]` (through `[neg]`, with zero at `zero`) if digit `esi` is
negative. -/
def negY : Prog isa := .seq (Mont.subCall K.F K.neg K.zero K.E.y) (.block (K.signMask ++ sel (2 * K.M.n) K.E.y K.E.y K.neg))

/-- The words of the table of bits the comb clears, past the scalar's
`kbytes`, up to `w J`. -/
def zw : Nat := (K.w * K.J - K.kbytes + 3) / 4

/-! ## The comb by complete additions

`comb`, as the header has it: the accumulator `A` starts at `[c]G`, and the
iterations `j = J - 1` down to `0` (`esi`, counting down from `J`) add the
entry of table `j` for `|d_j|`, negated if `d_j < 0`, by the complete addition
for any `a` (`rcb`, with `a` and `3b` in `S`), into `D`, which is then copied
to `A`. The table of bits holds only the scalar's `kbytes` bits, so the top
window, whose bits past them are zero, reads only its `topBits`
(`kbytes - w (J - 1) < w`; the test of the counter is public), and its digit
is always negative. -/

/-- The bits of the top window that are the scalar's. -/
def topBits : Nat := K.kbytes - K.w * (K.J - 1)

/-- `ZF` for the top window: `esi = J - 1`. -/
def topTest : List Instr := [.alu .cmp .esi (.imm (BitVec.ofNat 32 (K.J - 1)))]

/-- The magnitude of digit `esi` into `eax` and `ebx`: its window (of
`topBits` bits for the top one) and `|k - H|`. -/
def digitT : Prog isa :=
  .seq (.block K.topTest) <|
  .ite .e (.block (winIndex K.w ++ hornerBits K.bits K.topBits ++ magnitudeH K.H)) (.block K.digit)

/-- `ecx` all ones if digit `esi` is negative: for the top window, whose top
bit is past the scalar's, always; else if its window's top bit is clear. -/
def signMaskT : Prog isa :=
  .seq (.block K.topTest) <|
  .ite .e (.block [.mov .ecx (.imm (BitVec.allOnes 32))]) (.block K.signMask)

/-- The signed entry of digit `esi` into `E`: selected for its magnitude,
and `y` negated (through `[neg]`, with zero at `zero`) for a negative digit. -/
def entry : Prog isa :=
  .seq K.digitT <| .seq (.block K.select) <|
  .seq (Mont.subCall K.F K.neg K.zero K.E.y) <|
  .seq K.signMaskT (.block (sel (2 * K.M.n) K.E.y K.E.y K.neg))

/-- An iteration: `esi -= 1`, the entry of digit `esi`, `D = A + E`, `A = D`,
and `ZF` for `esi = 0`. -/
def step : Prog isa :=
  .seq (.block [decCounter]) <| .seq K.entry <|
  .seq (fprog K.F (rcb K.S K.A K.E K.D)) (.block (copyPt K.M.n K.A K.D ++ [testCounter]))

/-- `[k]G` into `A`, in projective coordinates: `A = [c]G`, then the `J`
iterations. -/
def comb : Prog isa :=
  .seq (.block (setConst K.M.n K.A.x K.start.1 ++ setConst K.M.n K.A.y K.start.2 ++
    setConst K.M.n K.A.z K.one ++ [.mov .esi (.imm (BitVec.ofNat 32 K.J))]))
    (.loop K.step .ne)

end TCombCfg

end VG.Impl.Weierstrass.X86
