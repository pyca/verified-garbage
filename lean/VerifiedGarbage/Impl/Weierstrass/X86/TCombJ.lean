import VerifiedGarbage.Impl.Weierstrass.X86.TComb

/-!
# The fixed-base comb with Booth's digits and Jacobian mixed additions

The comb of `Impl/Weierstrass/X86/TComb.lean`, with the same tables, but
cheaper additions: the digits are Booth's (`d_j = W_j + c_j - 2^w c_{j+1}`,
`W_j` window `j` and `c_j` bit `wj - 1` of `k`, so `|d_j| ≤ 2^(w-1)` and no
constant is added), and they are added from the bottom (`j = 0` up), with the
mixed Jacobian addition (`maddJ`: 8 products and 3 squares, against
Algorithm 5's 11 products and 2 by `b`). That formula fails for equal points;
the sum of the digits below `j` is smaller than any nonzero digit's term,
modulo the order of `G`, so they never are (the proof's `booth_ne`).

The accumulator `A` holds a Jacobian triple. Window `0` puts its entry in `A`
(`first`), the accumulator being `O`. Each later window `j = esi` selects its
entry (the magnitude `bdigit`, `select`), negates it for a negative digit
(`bnegY`), adds it into `D`, takes the entry instead where `A` is `O`
(`Z = 0`, `nzMask`), and `A = D` unless the digit is zero (computed again).
At the end, `A = (XZ : Y : Z³)` in projective coordinates, with `Y = 1` where
`Z = 0` (`outFix`, `outOps`). Every selection is by a mask, and the windows'
order is public: the timing depends on `edi` and the tables' address only.
-/

namespace VG.Impl.Weierstrass.X86

open VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass

/-- `ecx` all ones if the `2 n` 32-bit words at `z` are not all zero, through `eax`. -/
def nzMask (n z : Nat) : List Instr :=
  .mov .eax (.mem (sc z)) :: (List.range (2 * n - 1)).map (fun i => .alu .or .eax (.mem (sc (z + 4 * (i + 1))))) ++
  [.mov .ecx (.imm 0), .alu .sub .ecx (.reg .eax), .alu .sbb .ecx (.reg .ecx)]

namespace TCombCfg

variable (K : TCombCfg)

/-- Booth's digit `esi`'s magnitude into `eax` and `ebx`: `m = W + c` (the
window, through `ecx = edi + w esi`, and, for `c`, bit `w esi - 1`), the window's top
bit `s`, and `s ? 2^w - m : m`, through `edx`. -/
def bdigit (c : Bool) : List Instr :=
  winIndex K.w ++ hornerBits K.bits K.w ++
  ((if c then [.movzx8 .edx (winByte (K.bits - 1)), .alu .add .eax (.reg .edx)] else []) : List Instr) ++
  ([.movzx8 .edx (winByte (K.bits + K.w - 1)), .mov .ebx (.imm 0), .alu .sub .ebx (.reg .edx),
    .alu .xor .eax (.reg .ebx), .alu .sub .eax (.reg .ebx),
    .alu .and .ebx (.imm (BitVec.ofNat 32 (2 ^ K.w))), .alu .add .eax (.reg .ebx), .mov .ebx (.reg .eax)] : List Instr)

/-- `ecx` all ones if Booth's digit `esi` is negative: minus its window's top
bit, through `eax`. -/
def bsignMask : List Instr :=
  winIndex K.w ++ [.movzx8 .eax (winByte (K.bits + K.w - 1)), .mov .ecx (.imm 0),
    .alu .sub .ecx (.reg .eax)]

/-- `[y] = -[y]` (through `[neg]`, with zero at `zero`) if Booth's digit
`esi` is negative. -/
def bnegY : Prog isa :=
  .seq (Mont.subCall K.F K.neg K.zero K.E.y) (.block (K.bsignMask ++ sel (2 * K.M.n) K.E.y K.E.y K.neg))

/-- The bytes of the table of bits past the scalar cleared (to `w J`, in
words). -/
def clearBits : List Instr :=
  .mov .eax (.imm 0) :: (List.range K.zw).map (fun i => .store (sc (K.bits + K.kbytes + 4 * i)) .eax)

/-- Window `0`: its signed entry into `A` (the accumulator being `O`), and
`esi = 1`. -/
def first : Prog isa :=
  .seq (.block (K.clearBits ++ [.mov .esi (.imm 0)] ++ K.bdigit false ++ K.select)) <|
  .seq K.bnegY <|
  .block (copyPt K.M.n K.A K.E ++ [.mov .esi (.imm 1)])

/-- Window `j = esi` (`1 ≤ j < J`), then `esi = j + 1` and `ZF` for `j + 1 = J`. -/
def stepJ : Prog isa :=
  .seq (.block (K.bdigit true ++ K.select)) <|
  .seq K.bnegY <|
  .seq (fprog K.F (maddJ K.S K.A K.E K.D)) <|
  .seq (.block (nzMask K.M.n K.A.z ++ selPt K.M.n K.D K.E K.D)) <|
  .block (K.bdigit true ++ eqMask 0 ++ selPt K.M.n K.A K.D K.A ++
    [.alu .add .esi (.imm 1), .alu .cmp .esi (.imm (BitVec.ofNat 32 K.J))])

/-- `Y = R mod p` where `Z = 0`: `Y` cleared there (from `zero`), then `R`'s
words or-ed in under the complemented mask, through `eax`, `ecx` and `edx`. -/
def outFix : List Instr :=
  nzMask K.M.n K.A.z ++ sel (2 * K.M.n) K.A.y K.zero K.A.y ++ .alu .xor .ecx (.imm (-1)) ::
  (List.range (2 * K.M.n)).flatMap fun i =>
    [.mov .eax (.imm (BitVec.ofNat 32 (K.one / 2 ^ (32 * i)))), .alu .and .eax (.reg .ecx), .alu .or .eax (.mem (sc (K.A.y + 4 * i))),
      .store (sc (K.A.y + 4 * i)) .eax]

/-- `A = (XZ : Y : Z³)`. -/
def outOps : List FOp := [.mul K.A.x K.A.x K.A.z, .mul K.S.t0 K.A.z K.A.z, .mul K.A.z K.S.t0 K.A.z]

/-- `[k]G` into `A`, in projective coordinates. -/
def combJ : Prog isa :=
  .seq K.first <| .seq (.loop K.stepJ .ne) <| .seq (.block K.outFix) (fprog K.F K.outOps)

end TCombCfg

end VG.Impl.Weierstrass.X86
