import VerifiedGarbage.Impl.Weierstrass.X86_64.TComb

/-!
# The fixed-base comb with Booth's digits and Jacobian mixed additions

The comb of `Impl/Weierstrass/X86_64/TComb.lean`, with the same tables, but
cheaper additions: the digits are Booth's (`d_j = W_j + c_j - 2^w c_{j+1}`,
`W_j` window `j` and `c_j` bit `wj - 1` of `k`, so `|d_j| ≤ 2^(w-1)` and no
constant is added), and they are added from the bottom (`j = 0` up), with the
mixed Jacobian addition (`maddJ`: 8 products and 3 squares, against
Algorithm 5's 11 products and 2 by `b`). That formula fails for equal points;
the sum of the digits below `j` is smaller than any nonzero digit's term,
modulo the order of `G`, so they never are (the proof's `booth_ne`).

The accumulator `A` holds a Jacobian triple. Window `0` puts its entry in `A`
(`first`), the accumulator being `O`. Each later window `j = rbx` selects its
entry (the magnitude `bdigit`, `select`), negates it for a negative digit
(`bnegY`), adds it into `D`, takes the entry instead where `A` is `O`
(`Z = 0`, `nzMask`), and `A = D` unless the digit is zero (computed again).
At the end, `A = (XZ : Y : Z³)` in projective coordinates, with `Y = 1` where
`Z = 0` (`outFix`, `outOps`). Every selection is by a mask, and the windows'
order is public: the timing depends on `rdi` and the tables' address only.
-/

namespace VG.Impl.Weierstrass.X86_64

open VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

/-- `rcx` all ones if the `n` words at `z` are not all zero, through `rax`. -/
def nzMask (n z : Nat) : List Instr :=
  .mov .rax (.mem (sc z)) :: (List.range (n - 1)).map (fun i => .alu .or .rax (.mem (sc (z + 8 * (i + 1))))) ++
  [.mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rax), .alu .sbb .rcx (.reg .rcx)]

namespace TCombCfg

variable (K : TCombCfg)

/-- Booth's digit `rbx`'s magnitude into `rax` and `r8`: `m = W + c` (the
window, from `rcx = w rbx`, and, for `c`, bit `w rbx - 1`), the window's top
bit `s`, and `s ? 2^w - m : m`, through `rdx`. -/
def bdigit (c : Bool) : List Instr :=
  winIndex K.w ++ hornerBits K.bits K.w ++
  (if c then [.movzx8 .rdx (winByte (K.bits - 1)), .alu .add .rax (.reg .rdx)] else []) ++
  [.movzx8 .rdx (winByte (K.bits + K.w - 1)), .mov32 .r8 (.imm 0), .alu .sub .r8 (.reg .rdx),
    .alu .xor .rax (.reg .r8), .alu .sub .rax (.reg .r8),
    .alu .and .r8 (.imm (BitVec.ofNat 32 (2 ^ K.w))), .alu .add .rax (.reg .r8), .mov .r8 (.reg .rax)]

/-- `rcx` all ones if Booth's digit `rbx` is negative: minus its window's top
bit, through `rax`. -/
def bsignMask : List Instr :=
  winIndex K.w ++ [.movzx8 .rax (winByte (K.bits + K.w - 1)), .mov32 .rcx (.imm 0),
    .alu .sub .rcx (.reg .rax)]

/-- `[y] = -[y]` (through `[neg]`, with zero at `zero`) if Booth's digit
`rbx` is negative. -/
def bnegY : List Instr :=
  Mont.X86_64.sub K.M K.neg K.zero K.E.y ++ K.bsignMask ++ sel K.M.n K.E.y K.E.y K.neg

/-- The bytes of the table of bits past the scalar cleared (to `w J`, in
words). -/
def clearBits : List Instr :=
  .mov32 .rax (.imm 0) :: (List.range K.zw).map (fun i => .store (sc (K.bits + K.kbytes + 8 * i)) .rax)

/-- Window `0`: its signed entry into `A` (the accumulator being `O`), and
`rbx = 1`. -/
def first : Prog isa :=
  .seq (.block (K.clearBits ++ [.mov32 .rbx (.imm 0)] ++ K.bdigit false ++ K.select)) <|
  .seq (.block K.bnegY) <|
  .block (copyPt K.M.n K.A K.E ++ [.mov32 .rbx (.imm 1)])

/-- Window `j = rbx` (`1 ≤ j < J`), then `rbx = j + 1` and `ZF` for `j + 1 = J`. -/
def stepJ : Prog isa :=
  .seq (.block (K.bdigit true ++ K.select)) <|
  .seq (.block K.bnegY) <|
  .seq (fprogB K.M (maddJ K.S K.A K.E K.D)) <|
  .seq (.block (nzMask K.M.n K.A.z ++ selPt K.M.n K.D K.E K.D)) <|
  .block (K.bdigit true ++ eqMask 0 ++ selPt K.M.n K.A K.D K.A ++
    [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm (BitVec.ofNat 32 K.J))])

/-- `Y = R mod p` where `Z = 0`: `Y` cleared there (from `zero`), then `R`'s
words or-ed in under the complemented mask, through `rax`, `rcx` and `rdx`. -/
def outFix : List Instr :=
  nzMask K.M.n K.A.z ++ sel K.M.n K.A.y K.zero K.A.y ++ .alu .xor .rcx (.imm (-1)) ::
  (List.range K.M.n).flatMap fun i =>
    [.movImm64 .rax (wordOf K.one i), .alu .and .rax (.reg .rcx), .alu .or .rax (.mem (sc (K.A.y + 8 * i))),
      .store (sc (K.A.y + 8 * i)) .rax]

/-- `A = (XZ : Y : Z³)`. -/
def outOps : List FOp := [.mul K.A.x K.A.x K.A.z, .mul K.S.t0 K.A.z K.A.z, .mul K.A.z K.S.t0 K.A.z]

/-- `[k]G` into `A`, in projective coordinates. -/
def combJ : Prog isa :=
  .seq K.first <| .seq (.loop K.stepJ .ne) <| .seq (.block K.outFix) (fprogB K.M K.outOps)

end TCombCfg

end VG.Impl.Weierstrass.X86_64
