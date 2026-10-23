module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx8

/-!
# Preparing a key context's first sixteen powers in place, on 128-bit registers

`vg_aes_gcm_prepare16` for the backends without VPCLMULQDQ, whose eight-block
loops read no other powers: `H'` from the hash subkey at `ctx + 240`, as
those loops compute it (`StitchAvx8.hInv`), then `H'²`–`H'¹⁶` in four rounds
of independent products (`plan`), each stored as it is computed. Half of
them are squares, which need two carry-less products rather than four, since
the middle term of a square is zero in characteristic 2 (`sq`); the products
go straight to the registers that sum them (`mulD`), and are reduced the
low half first. No calls, no stack.
-/

@[expose] public section

namespace VG.Impl.Gcm.X86_64.PrepareAvx

open VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Impl.Gcm.X86_64.Pclmul (revMask poly)
open VG.Impl.Gcm.X86_64.StitchAvx8 (const hInv fold prepOff)

/-- `xmm9`'s half of a reduction: `xmm9 ← swap(xmm9) ⊕ clmul(xmm9₀, c)`. -/
def foldMid : List Instr :=
  [.vop (.vpclmulqdq .l128 .xmm11 .xmm9 .xmm1 0x10), .vop (.vpshufd .l128 .xmm9 .xmm9 0x4e),
   .vop (.vbin .vpxor .l128 .xmm9 .xmm9 .xmm11)]

/-- `d ← a²`, prepared: the low and high products only, the low one folded
twice into the high one. -/
def sq (d a : XReg) : List Instr :=
  ([.vop (.vpclmulqdq .l128 .xmm8 a a 0x00), .vop (.vpclmulqdq .l128 .xmm10 a a 0x11)] : List Instr) ++
  fold ++ fold ++ ([.vop (.vbin .vpxor .l128 d .xmm10 .xmm8)] : List Instr)

/-- `d ← a · b`, prepared: the four products straight into `xmm8`–`xmm10`,
the low half folded into the middle, the middle into the high half. -/
def mulD (d a b : XReg) : List Instr :=
  ([.vop (.vpclmulqdq .l128 .xmm8 a b 0x00), .vop (.vpclmulqdq .l128 .xmm10 a b 0x11),
    .vop (.vpclmulqdq .l128 .xmm9 a b 0x01), .vop (.vpclmulqdq .l128 .xmm11 a b 0x10),
    .vop (.vbin .vpxor .l128 .xmm9 .xmm9 .xmm11)] : List Instr) ++
  fold ++ ([.vop (.vbin .vpxor .l128 .xmm9 .xmm9 .xmm8)] : List Instr) ++ foldMid ++
  ([.vop (.vbin .vpxor .l128 d .xmm10 .xmm9)] : List Instr)

/-- A step `(d, a, b, n)`: `H'ⁿ ← a · b` (a square if `a` is `b`) into `d`,
then stored at its place in the context at `rdi`. -/
def step (p : XReg × XReg × XReg × Nat) : List Instr :=
  (if p.2.1 = p.2.2.1 then sq p.1 p.2.1 else mulD p.1 p.2.1 p.2.2.1) ++
  ([.vmovdquStore .l128 (at_ .rdi (prepOff p.2.2.2)) p.1] : List Instr)

/-- `H'²`–`H'¹⁶` from `H'` in `xmm3`, in four rounds: `H'²`; `H'³`, `H'⁴`;
`H'⁵`–`H'⁸`; and `H'⁹`–`H'¹⁶`, the even powers squares of the halves. -/
def plan : List (XReg × XReg × XReg × Nat) :=
  [(.xmm4, .xmm3, .xmm3, 2),
   (.xmm5, .xmm4, .xmm3, 3), (.xmm6, .xmm4, .xmm4, 4),
   (.xmm12, .xmm6, .xmm3, 5), (.xmm13, .xmm5, .xmm5, 6), (.xmm14, .xmm6, .xmm5, 7), (.xmm15, .xmm6, .xmm6, 8),
   (.xmm2, .xmm15, .xmm3, 9), (.xmm4, .xmm12, .xmm12, 10), (.xmm6, .xmm15, .xmm5, 11),
   (.xmm7, .xmm13, .xmm13, 12), (.xmm0, .xmm15, .xmm12, 13), (.xmm2, .xmm14, .xmm14, 14),
   (.xmm4, .xmm15, .xmm14, 15), (.xmm6, .xmm15, .xmm15, 16)]

/-- The constants, `H'` from the hash subkey at `rdi + 240` into `xmm3`, and
stored. -/
def setup : List Instr :=
  const .xmm0 revMask ++ const .xmm1 poly ++
  ([.vmovdquLoad .l128 .xmm7 (at_ .rdi 240), .vop (.vbin .vpshufb .l128 .xmm7 .xmm7 .xmm0)] : List Instr) ++ hInv ++
  ([.vmovdquStore .l128 (at_ .rdi (prepOff 1)) .xmm3] : List Instr)

/-- `vg_aes_gcm_prepare16`: the first 16 prepared powers into pairs 0–7 of the
context at `rdi`, from its hash subkey, for the eight-block loops, which read
no other. -/
def prepare16 : Prog isa :=
  .block (setup ++ plan.flatMap step)

end VG.Impl.Gcm.X86_64.PrepareAvx
