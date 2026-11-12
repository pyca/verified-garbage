module

public import VerifiedGarbage.Impl.P256.X86_64.Ifma.Code
public import VerifiedGarbage.Impl.P256.X86_64.Joint

/-!
# P-256 on x86-64 with AVX512_IFMA: the joint multiplication's loop

`vwindow` is `Joint.window` with the loop over the digits of both scalars
in vectors (`vloop`), from the same tables: the accumulator in
`ymm0`–`ymm19` (`Point.lean`), doubled once for each digit (`dblPieces`),
and for each digit that is not zero the entry of the digit's point made of
its words (`convQPieces` for a multiple of `Q`, `convGPieces` for one of the
generator) and added (`addPieces`), or taken as the accumulator if it is the
first (`setPieces`). The accumulator's triple is then put back in the words
of `R` (`outPieces`, `packLane`).

The additions are those of distinct points: where a digit's point is the
accumulator's or its negative, `Z` becomes zero and stays zero, and then
the loop of `Joint.run` is run instead, from the start.

`vpmadd52luq` and `vpmadd52huq` have MXCSR-configuration-dependent timing
on some processors, so the loop runs between Intel's prologue and epilogue
(`region`; see "MCDT" in `TCB/X86_64/Isa.lean`).
-/

@[expose] public section

namespace VG.Impl.P256.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Impl.Rsa.X86_64.CrtIfma (vreg)

/-- The vectors' slots, in the working space. -/
def SL : Nat := 4512

/-- MXCSR, saved, and `0x1FBF` (`region`). -/
def MX : Nat := 5472

/-- The blocks' constants, in the working space. -/
def KB : Nat := 6016

/-- The words of the blocks' constants. -/
def kwords : List (BitVec 64) := poolLit.flatMap fun k => [k.w0, k.w1, k.w2, k.w3].map (BitVec.ofNat 64)

/-- The words `ws` to `o` of the working space. -/
def fill : List (BitVec 64) → Nat → List Instr
  | [], _ => []
  | w :: ws, o => .movImm64 .rax w :: .store (sc o) .rax :: fill ws (o + 8)

/-- `r9` at the mask of an entry's sign among the constants. -/
def signPtr (neg : Bool) : List Instr :=
  [.mov .r9 (.reg .r10), .alu .add .r9 (.imm (BitVec.ofNat 32 (32 * poolLit.idxOf (K4.lanes (if neg then 3 else 0)))))]

/-- `rcx` at the words of the odd multiple of `Q` whose magnitude is in `r8`, and `rdx` at those of its
`Z²` and `Z³`: the addresses of `Naf.publicEntry` and `Naf.cacheRead` (the first kept in `rbp`
while the second is made). -/
def entryQ (c : Joint.Cfg) : List Instr :=
  [.mov .rax (.reg .r8), .alu .sub .rax (.imm 1), .shift .shr .rax 1] ++ Naf.tableAddress c.K.M.n c.K.tbl ++
  [.mov .rbp (.reg .rdx)] ++ Naf.cacheAddress c.K.M.n c.cache ++ [.mov .rcx (.reg .rbp)]

/-- `rdx` at the words of the multiple of the generator whose magnitude is in `r8`: the address of
`Joint.fixedLoad`. -/
def entryG (c : Joint.Cfg) : List Instr := Joint.fixedAddress c.K.M.n c.tsym

/-- The entry in `ymm20`–`ymm29` added to the accumulator, or the accumulator set to it if it is the
first (`r11` zero). -/
def addOrSet : Prog isa :=
  .seq (.block [.alu .test .r11 (.reg .r11)])
    (.ite .e (.block (setPieces.flatten ++ [.mov32 .r11 (.imm 1)])) (.block addPieces.flatten))

/-- The multiple of `Q` of the digit in `r8`, which is not zero, added. -/
def qBody (c : Joint.Cfg) : Prog isa :=
  .seq (.block [.alu .cmp .r8 (.imm 128)]) <|
  .seq (.ite .b (.block (signPtr false))
    (.block ([.mov32 .rax (.imm 256), .alu .sub .rax (.reg .r8), .mov .r8 (.reg .rax)] ++ signPtr true))) <|
  .seq (.block (entryQ c ++ convQPieces.flatten)) addOrSet

/-- A digit of `Q`'s scalar: one byte, a signed odd magnitude below 16 or zero. -/
def qPass (c : Joint.Cfg) : Prog isa :=
  .seq (.block (Naf.digitRead c.K)) (.ite .e (.block []) (qBody c))

/-- The multiple of the generator of the digit in `r8`, which is not zero, added. -/
def gBody (c : Joint.Cfg) : Prog isa :=
  .seq (.block [.alu .cmp .r8 (.imm 256)]) <|
  .seq (.ite .b (.block (signPtr false))
    (.block ([.mov32 .rax (.imm 65536), .alu .sub .rax (.reg .r8), .mov .r8 (.reg .rax)] ++ signPtr true))) <|
  .seq (.block (entryG c ++ convGPieces.flatten)) addOrSet

/-- A digit of the generator's scalar: sixteen bits, a signed magnitude below 256 or zero. -/
def gPass (c : Joint.Cfg) : Prog isa :=
  .seq (.block (Joint.fixedRead c)) (.ite .e (.block []) (gBody c))

/-- A digit of each scalar: the accumulator doubled, unless it is not set yet, and their points added. -/
def vstep (c : Joint.Cfg) : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1), .alu .test .r11 (.reg .r11)]) <|
  .seq (.ite .e (.block []) (.block dblPieces.flatten)) <|
  .seq (qPass c) <| .seq (gPass c) (.block [.alu .test .rbx (.reg .rbx)])

/-- `ymm0`–`ymm19` zero. -/
def zeroAcc : List Instr := (List.range 20).map fun r => .eop (.bin .vpxorq (vreg r) (vreg r) (vreg r))

/-- `ymm0`–`ymm4` into the first five slots. -/
def storeOut : List Instr := (List.range 5).map fun i => .evStore (cfg.smem i) (vreg i)

/-- The registers the loop starts with: `r10` at the constants, as are those the blocks read through
(`rcx`, `rdx`, `r9`) until a digit sets them; the accumulator not set (`r11`); the counter. -/
def vregs (n : Nat) : List Instr :=
  [.mov .r10 (.reg .rdi), .alu .add .r10 (.imm (BitVec.ofNat 32 KB)), .mov32 .r11 (.imm 0),
    .mov32 .rbx (.imm (BitVec.ofNat 32 n)), .mov .rcx (.reg .r10), .mov .rdx (.reg .r10), .mov .r9 (.reg .r10)]

/-- The loop over the digits, after the blocks' constants are written to the working space: the
accumulator's rows of `(Y, Z, _, X)` are left in the first five slots, if it was set (`r11`). -/
def vloop (c : Joint.Cfg) : Prog isa :=
  .seq (.block (fill kwords KB ++ (vregs (64 * c.K.M.n + 1) ++ zeroAcc))) <|
  .seq (.loop (vstep c) .ne) <|
  .seq (.block [.alu .test .r11 (.reg .r11)]) (.ite .e (.block []) (.block (outPieces.flatten ++ storeOut)))

/-- `c` with MXCSR `0x1FBF`, through `[rdi + MX]`: MXCSR saved in `r12`, and loaded back after `c`,
which must not write `r12` (as ML-KEM's `withMxcsr`). -/
def region (c : Prog isa) : Prog isa :=
  .seq (.block [.stmxcsr (sc MX), .mov32 .r12 (.mem (sc MX)), .alu32 .and .r12 (.imm 0xFFFF)])
    (.seq (.seq (.block [.mov32 .rax (.imm 0x1FBF), .store32 (sc (MX + 4)) .rax, .ldmxcsr (sc (MX + 4)), .lfence])
        (.seq c (.block [.lfence])))
      (.block [.store32 (sc MX) .r12, .ldmxcsr (sc MX)]))

/-- The number in lane `l` of five slots at `sl`, below `2 p`, reduced modulo `p` into the words at `dst`. -/
def packLaneAt (sl : Nat) (M : Mod) (l dst : Nat) : List Instr :=
  let L (i : Nat) : MemOp := sc (sl + 32 * i + 8 * l)
  [.mov .r8 (.mem (L 0)), .mov .rax (.mem (L 1)), .mov .r9 (.reg .rax), .shift .shl .rax 52, .alu .or .r8 (.reg .rax),
    .shift .shr .r9 12, .mov .rax (.mem (L 2)), .mov .r10 (.reg .rax), .shift .shl .rax 40, .alu .or .r9 (.reg .rax),
    .shift .shr .r10 24, .mov .rax (.mem (L 3)), .mov .r11 (.reg .rax), .shift .shl .rax 28, .alu .or .r10 (.reg .rax),
    .shift .shr .r11 36, .mov .rax (.mem (L 4)), .mov .r12 (.reg .rax), .shift .shl .rax 16, .alu .or .r11 (.reg .rax),
    .shift .shr .r12 48] ++
  csub M [.r8, .r9, .r10, .r11] .r12 ++ stores [.r8, .r9, .r10, .r11] dst

/-- `packLaneAt`, of the first five slots. -/
def packLane (M : Mod) (l dst : Nat) : List Instr := packLaneAt SL M l dst

/-- `R` from the slots, if the accumulator was set (`rbx`, which keeps `r11`). -/
def packR (c : Joint.Cfg) : Prog isa :=
  .seq (.block [.alu .test .rbx (.reg .rbx)]) <|
  .ite .e (.block []) (.block (packLane c.K.M 3 c.K.R.x ++ packLane c.K.M 0 c.K.R.y ++ packLane c.K.M 1 c.K.R.z))

/-- The digits' loop in vectors, from `R = O`: `R` is the sum, or its `Z` is zero. -/
def vmain (c : Joint.Cfg) : Prog isa :=
  .seq (region (.seq (vloop c) (.block [.mov .rbx (.reg .r11), .vop .vzeroupper]))) (packR c)

/-- `Joint.window` with the loop in vectors, and `Joint.run` where that leaves `Z` zero. -/
def vwindow (c : Joint.Cfg) (double : Prog isa) : Prog isa :=
  .seq (Joint.tableCode c) <| .seq (Joint.cacheCode c) <|
  .seq (.block (Jacobian.infinity c.K c.K.R ++ [.mov32 .rbx (.imm (BitVec.ofNat 32 (Joint.top c)))])) <|
  .seq (vmain c) <|
  .seq (.block (Jacobian.zeroTest c.K.M.n c.K.R.z)) <|
  .ite .e (.seq (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 (Joint.top c)))]) (Joint.run c double))
    (.block [.mov32 .rbx (.imm 0)])

/-- `publicJointAdx` with the generator's digits at `5480`, which leaves the working space from `6000`
for the blocks' constants (`KB`). -/
def publicJointIfma : Joint.Cfg := {VG.Impl.P256.X86_64.publicJointAdx with gBits := 5480}

end VG.Impl.P256.X86_64.Ifma
