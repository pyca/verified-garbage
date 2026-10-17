module

public import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledProduct

/-!
# The lazy final subtraction, eight words at a time

For `w` a multiple of 8 and the reduction's result `T < R + m` in `aTmp`
(`R = 2^(64 w)`, so its word `w` is 0 or 1): `lazy8 o` writes
`T - (m ∧ mask)` to `o`, for `mask = -T_w`, in one pass, so that `o < R` and
`o ≡ T (mod m)`, without `finish8`'s pass selecting between `T` and `T - m`.
Each iteration masks four words of `m` into `rcx`, `rdx`, `r9` and `r11`
(an `and`, which clears the carry flag), then subtracts them with the borrow
moved from `rbp` to the carry flag and back, twice.
-/

@[expose] public section

namespace VG.Impl.Bignum.X86_64.Adx

open VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public

/-- `w`, and `T` and `o`'s bases. -/
def lazyLoads (o : Nat) : List Instr :=
  [.mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aTmp))), .mov .rbx (.mem (hdr (sArr o)))]

/-- The mask `-T_w` in `r13`; no borrow; `r14 = 0`. -/
def lazyMask : List Instr :=
  [.mov32 .r13 (.imm 0), .alu .sub .r13 (.mem (ix .r8 .r12)), .mov32 .rbp (.imm 0), .mov .r14 (.imm 0), .align 5]

/-- The registers holding the masked words of a group. -/
def lazyReg : Nat → Reg
  | 0 => .rcx
  | 1 => .rdx
  | 2 => .r9
  | _ => .r11

/-- Word `h + j` of `m`, masked, into `lazyReg j`. -/
def maskWord (h j : Nat) : List Instr :=
  [.mov (lazyReg j) (.reg .r13), .alu .and (lazyReg j) (.mem (ix .r10 .r14 (8 * ((h + j : Nat) : Int))))]

/-- Word `h + j` of `T - (m ∧ mask)`. -/
def lazyWord (h j : Nat) : List Instr :=
  [.mov .rax (.mem (ix .r8 .r14 (8 * ((h + j : Nat) : Int)))), .alu .sbb .rax (.reg (lazyReg j)),
    .store (ix .rbx .r14 (8 * ((h + j : Nat) : Int))) .rax]

/-- Words `h`–`h + 3` of an iteration. -/
def lazyGroup (h : Nat) : List Instr :=
  (List.range 4).flatMap (maskWord h) ++ [cfFromRbp] ++ (List.range 4).flatMap (lazyWord h) ++ [cfToRbp]

/-- `T - (m ∧ mask)` into `o`, for `w` a multiple of 8. -/
def lazy8 (o : Nat) : Prog isa :=
  .seq (.block (lazyLoads o)) (.seq (.block lazyMask)
    (.loop (.block (lazyGroup 0 ++ lazyGroup 4 ++ [.alu .add .r14 (.imm 8), .alu .cmp .r14 (.reg .r12)])) .ne))

end VG.Impl.Bignum.X86_64.Adx

namespace VG.Impl.Bignum.X86_64.AdxTiledProduct
open VG.X86_64

/-- `redcFinish` with the lazy final subtraction. -/
def redcLazy (o : Nat) : Prog isa :=
  .seq AdxRotate8.redc (.seq (.block [.mov .r10 (.mem (hdr (sArr Public.aN)))]) (Adx.lazy8 o))

end VG.Impl.Bignum.X86_64.AdxTiledProduct
