module

public import VerifiedGarbage.Spec.Sha256
public import VerifiedGarbage.TCB.X86_64.Isa

/-!
# SHA-256 compression function: x86-64 implementation with the SHA extensions

`vg_sha256_compress_shani(state = rdi, blocks = rsi, n = rdx, scratch = rcx)`,
with the contract of `vg_sha256_compress`, for CPUs with the SHA extensions
and SSSE3.

* The working variables are kept as `ABEF` in `xmm1` and `CDGH` in `xmm2`
  (`A` in bits 127:96, as `sha256rnds2` reads them), converted from and to the
  hash value's `[u32; 8]` layout once per call. Each `sha256rnds2` does two
  rounds and swaps the roles of the two registers.
* Four rounds at a time, `Wₜ + Kₜ` for them is formed in `xmm0` (the implicit
  operand of `sha256rnds2`). The four constants are built from immediates
  through `rax` and `xmm11`. With more than one block, the first block also
  stores them in `scratch` (sixteen bytes per group, at `16i`), and later
  blocks load them from there, one load instead of five instructions.
* The message schedule is kept four words to a register, `W₄ᵢ … W₄ᵢ₊₃` in
  `xmm(3 + i mod 4)`, computed with `sha256msg1`, `palignr` and `sha256msg2`.
* `xmm8` holds the `pshufb` mask that makes the message words big-endian;
  `xmm9` and `xmm10` hold the working variables at the start of the block.
* `scratch` holds only the round constants, and no callee-saved register is
  written. `rdi, rsi, rdx, rcx` (the pointers and the block count) are
  public; no address and no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Sha256.X86_64.ShaNi

open VG.X86_64
open VG.Spec.Sha256 (K)

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- The register holding `W₄ᵢ … W₄ᵢ₊₃`. -/
def msg (i : Nat) : XReg := [.xmm3, .xmm4, .xmm5, .xmm6].getD (i % 4) .xmm3

/-- The 128-bit constant `c` into `x`, through `rax` and `xmm11`. -/
def const (x : XReg) (c : BitVec 128) : List Instr :=
  [.movImm64 .rax (c.extractLsb' 0 64), .xop (.movq x .rax),
   .movImm64 .rax (c.extractLsb' 64 64), .xop (.movq .xmm11 .rax),
   .xop (.bin .punpcklqdq x .xmm11)]

/-- `Kᵢ … Kᵢ₊₃`, `Kᵢ` in bits 31:0. -/
def kQuad (i : Nat) : BitVec 128 := ofDwords (K i) (K (i + 1)) (K (i + 2)) (K (i + 3))

/-- The `pshufb` mask that reverses the bytes of each doubleword. -/
def bswapMask : BitVec 128 := 0x0c0d0e0f08090a0b0405060700010203#128

/-- `W₄ᵢ … W₄ᵢ₊₃` into `msg i`: loaded from the block for `i < 4`, otherwise
from the previous sixteen words (whose register `msg i` held the oldest four). -/
def schedule (i : Nat) : List Instr :=
  if i < 4 then
    [.movdquLoad (msg i) (at_ .rsi (16 * i)), .xop (.bin .pshufb (msg i) .xmm8)]
  else
    [.xop (.bin .sha256msg1 (msg i) (msg (i + 1))),
     .xop (.bin .movdqa .xmm7 (msg (i + 3))),
     .xop (.palignr .xmm7 (msg (i + 2)) 4),
     .xop (.bin .paddd (msg i) .xmm7),
     .xop (.bin .sha256msg2 (msg i) (msg (i + 3)))]

/-- How a block gets its round constants: built from immediates (`build`, the
only block of a call), built and stored at `scratch + 16i` (`store`, the
first of several), or loaded from there (`load`, the others). -/
inductive KMode | build | store | load
  deriving DecidableEq

/-- `K₄ᵢ … K₄ᵢ₊₃` into `xmm0`. -/
def kload : KMode → Nat → List Instr
  | .build, i => const .xmm0 (kQuad (4 * i))
  | .store, i => const .xmm0 (kQuad (4 * i)) ++ [.movdquStore (at_ .rcx (16 * i)) .xmm0]
  | .load, i => [.movdquLoad .xmm0 (at_ .rcx (16 * i))]

/-- Rounds `4i … 4i+3`, with `W₄ᵢ … W₄ᵢ₊₃` in `msg i`. -/
def rounds4 (c : KMode) (i : Nat) : List Instr :=
  kload c i ++
  ([.xop (.bin .paddd .xmm0 (msg i)),
   .xop (.sha256rnds2 .xmm2 .xmm1),
   .xop (.pshufd .xmm0 .xmm0 0x0e),
   .xop (.sha256rnds2 .xmm1 .xmm2)] : List Instr)

/-- Rounds `0 … 4n-1`. -/
def rounds (c : KMode) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds c n) (.block (schedule n ++ rounds4 c n))

/-- One block, with its round constants as `c` says. -/
def body (c : KMode) : Prog isa :=
  .seq (.block [.xop (.bin .movdqa .xmm9 .xmm1), .xop (.bin .movdqa .xmm10 .xmm2)])
    (.seq (rounds c 16)
      (.block [.xop (.bin .paddd .xmm1 .xmm9), .xop (.bin .paddd .xmm2 .xmm10),
        .alu .add .rsi (.imm 64), .alu .sub .rdx (.imm 1)]))

/-- Load the hash value `H₀ … H₇` as `ABEF` into `xmm1` and `CDGH` into `xmm2`. -/
def load : List Instr :=
  const .xmm8 bswapMask ++
  ([.movdquLoad .xmm1 (at_ .rdi 0), .movdquLoad .xmm2 (at_ .rdi 16),
   .xop (.pshufd .xmm1 .xmm1 0xb1), .xop (.pshufd .xmm2 .xmm2 0xb1),
   .xop (.bin .movdqa .xmm7 .xmm2),
   .xop (.bin .punpcklqdq .xmm7 .xmm1),
   .xop (.bin .punpckhqdq .xmm2 .xmm1),
   .xop (.bin .movdqa .xmm1 .xmm7)] : List Instr)

/-- Store `ABEF` and `CDGH` back as the hash value. -/
def store : List Instr :=
  [.xop (.bin .movdqa .xmm7 .xmm1),
   .xop (.bin .punpckhqdq .xmm7 .xmm2),
   .xop (.bin .punpcklqdq .xmm1 .xmm2),
   .xop (.pshufd .xmm7 .xmm7 0xb1), .xop (.pshufd .xmm1 .xmm1 0xb1),
   .movdquStore (at_ .rdi 0) .xmm7, .movdquStore (at_ .rdi 16) .xmm1]

/-- One block takes the branch laid out last, which falls through to `store`;
none, or several, the other. -/
def compress : Prog isa :=
  .seq (.block (load ++ ([.alu .cmp .rdx (.imm 1)] : List Instr)))
    (.seq (.ite .e (body .build)
      (.seq (.block [.alu .test .rdx (.reg .rdx)])
        (.ite .e (.block []) (.seq (body .store) (.loop (body .load) .ne))))) (.block store))

end VG.Impl.Sha256.X86_64.ShaNi
