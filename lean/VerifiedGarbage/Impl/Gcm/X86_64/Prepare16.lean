module

public import VerifiedGarbage.Impl.Gcm.X86_64.Stitch

/-!
# Preparing a key context's first sixteen powers in place, on 256-bit registers

`vg_aes_gcm_prepare16`: `H'` from the hash subkey at `ctx + 240`, as the
stitched loops compute it, then `H'²`–`H'¹⁶`, prepared and paired as the
context holds them, stored as pairs 0–7 as they are computed (`plan`). The
powers each round multiplies by, `H'²`, `H'⁴` and `H'⁸` in both lanes, are
squares of the one before, which need two carry-less products rather than
four (the middle term of a square is zero in characteristic 2), and are
ready no later than the pairs they multiply; the products of the pairs go
straight to the registers that sum them (`mulD`), and are reduced the low
half first. No calls, no stack.
-/

@[expose] public section

namespace VG.Impl.Gcm.X86_64.Prepare16

open VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_ revMask poly hInv const)
open VG.Impl.Gcm.X86_64.Stitch (storesK)

/-- One step of the reduction of `r`, in each lane:
`r ← swap(r) ⊕ clmul(r₀, c)`. -/
def fold (r : XReg) : List Instr :=
  [.vop (.vpclmulqdq .l256 .xmm11 r .xmm1 0x10), .vop (.vpshufd .l256 r r 0x4e),
   .vop (.vbin .vpxor .l256 r r .xmm11)]

/-- `d ← a²` in each lane, prepared: the low and high products only, the low
one folded twice into the high one. -/
def sq (d a : XReg) : List Instr :=
  ([.vop (.vpclmulqdq .l256 .xmm8 a a 0x00), .vop (.vpclmulqdq .l256 .xmm10 a a 0x11)] : List Instr) ++
  fold .xmm8 ++ fold .xmm8 ++ ([.vop (.vbin .vpxor .l256 d .xmm10 .xmm8)] : List Instr)

/-- `d ← a · b` in each lane, prepared: the four products straight into
`ymm8`–`ymm10`, the low half folded into the middle, the middle into the high
half. -/
def mulD (d a b : XReg) : List Instr :=
  ([.vop (.vpclmulqdq .l256 .xmm8 a b 0x00), .vop (.vpclmulqdq .l256 .xmm10 a b 0x11),
    .vop (.vpclmulqdq .l256 .xmm9 a b 0x01), .vop (.vpclmulqdq .l256 .xmm11 a b 0x10),
    .vop (.vbin .vpxor .l256 .xmm9 .xmm9 .xmm11)] : List Instr) ++
  fold .xmm8 ++ ([.vop (.vbin .vpxor .l256 .xmm9 .xmm9 .xmm8)] : List Instr) ++ fold .xmm9 ++
  ([.vop (.vbin .vpxor .l256 d .xmm10 .xmm9)] : List Instr)

/-- A step of `plan`. -/
inductive Op where
  /-- `d ← a²` in each lane. -/
  | sq (d a : XReg)
  /-- `d ← a · b` in each lane. -/
  | mul (d a b : XReg)
  /-- `d ← [a₀, b₀]`: the lower lanes of `a` and `b`. -/
  | ins (d a b : XReg)
  /-- `r` to pair `k` of the context at `rdi`. -/
  | st (r : XReg) (k : Nat)
  deriving DecidableEq

/-- The code of a step. -/
def Op.code : Op → List Instr
  | .sq d a => Prepare16.sq d a
  | .mul d a b => Prepare16.mulD d a b
  | .ins d a b => [.vop (.vinserti128 d a b 1)]
  | .st r k => storesK .rdi [r] (8 + k)

/-- `H'²`–`H'¹⁶`, paired, from `H'` in `xmm3`, each pair stored as it is
computed: `H'²`; `[H'², H']` and `[H'², H'²]`; `[H'⁴, H'³]` and `[H'⁴, H'⁴]`;
`[H'⁶, H'⁵]`, `[H'⁸, H'⁷]` and `[H'⁸, H'⁸]`; then the four pairs times
`H'⁸`. -/
def plan : List Op :=
  [.sq .xmm4 .xmm3, .ins .xmm12 .xmm4 .xmm3, .ins .xmm7 .xmm4 .xmm4, .st .xmm12 0,
   .mul .xmm13 .xmm12 .xmm7, .sq .xmm2 .xmm7, .st .xmm13 1,
   .mul .xmm14 .xmm12 .xmm2, .mul .xmm15 .xmm13 .xmm2, .sq .xmm7 .xmm2, .st .xmm14 2, .st .xmm15 3,
   .mul .xmm6 .xmm12 .xmm7, .st .xmm6 4, .mul .xmm5 .xmm13 .xmm7, .st .xmm5 5,
   .mul .xmm4 .xmm14 .xmm7, .st .xmm4 6, .mul .xmm3 .xmm15 .xmm7, .st .xmm3 7]

/-- The constants, `H'` from the hash subkey at `rdi + 240` into `xmm3`, as
`Stitch.setupG` computes it, and the reduction constant in both lanes. -/
def setup : List Instr :=
  const .xmm0 revMask ++ const .xmm1 poly ++
  ([.movdquLoad .xmm7 (at_ .rdi 240), .xop (.bin .pshufb .xmm7 .xmm0)] : List Instr) ++ hInv ++
  ([.vop (.vinserti128 .xmm1 .xmm1 .xmm1 1)] : List Instr)

/-- The 16 prepared powers into pairs 0–7 of the context at `rdi`, from its
hash subkey. -/
def prepare16 : Prog isa :=
  .block (setup ++ plan.flatMap Op.code ++ ([.vop .vzeroupper] : List Instr))

end VG.Impl.Gcm.X86_64.Prepare16
