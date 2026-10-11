module

public import VerifiedGarbage.Impl.Bignum.X86_64

/-!
# Montgomery multiplication as a function (x86-64)

`vg_rsa_mont_mul(ws, ws_len, o, a, b)` (`Spec/Rsa/Mont.lean`): the arrays
are given by their indices, in `edx`, `ecx` and `r8d`, and the working space
by `rdi`, as the code that calls it has them. It uses no stack, so that
calls of it run as their code inlined would (`Proof/Framework/X86_64/CallInline.lean`):
it keeps `rbx`, `rbp` and `r12`–`r15` in `xmm0`–`xmm2` (caller-saved) while
it runs, and restores them through its own arrays, `aAcc` and `aTmp`, once
it no longer needs them, which then hold them on return. It never writes
`rdi`.

`call o a b` is the call, with the indices in the argument registers.
-/

@[expose] public section

namespace VG.Impl.Bignum.X86_64.MontFn

open VG.X86_64 VG.Impl.Bignum.X86_64.Public

/-- `[rdi + 8 i + 64]`: the header word holding the base of array `i`, for
`i` in a register. -/
def arrAt (i : Reg) : MemOp := { base := .rdi, index := some i, scale := 8, disp := 8 * sArr 0 }

/-- `[b + d]`. -/
def at_ (b : Reg) (d : Int) : MemOp := { base := b, disp := d }

/-- The indices zero-extended (only their low 32 bits are arguments). -/
def zext : List Instr := [.mov32 .rdx (.reg .rdx), .mov32 .rcx (.reg .rcx), .mov32 .r8 (.reg .r8)]

/-- The callee-saved registers into `xmm0`–`xmm2`, two to a register. -/
def saves : List Instr :=
  [.xop (.movq .xmm0 .rbx), .xop (.movq .xmm1 .rbp), .xop (.bin .punpcklqdq .xmm0 .xmm1),
    .xop (.movq .xmm1 .r12), .xop (.movq .xmm2 .r13), .xop (.bin .punpcklqdq .xmm1 .xmm2),
    .xop (.movq .xmm2 .r14), .xop (.movq .xmm3 .r15), .xop (.bin .punpcklqdq .xmm2 .xmm3)]

/-- `zext`, then `saves`. -/
def enter : List Instr := zext ++ saves

/-- `bases` for the arrays in `edx`, `ecx` and `r8`: `rbx`, `r11`, `r9` the
bases of `o`, `a`, `b`; `r10`, `r8`, `rsi` those of `m`, the accumulator and
the temporary; `r12` `w` and `r15` `-m⁻¹`. -/
def basesR : List Instr :=
  [.mov .rbx (.mem (arrAt .rdx)), .mov .r11 (.mem (arrAt .rcx)), .mov .r9 (.mem (arrAt .r8)),
    .mov .r10 (.mem (hdr (sArr aN))), .mov .r8 (.mem (hdr (sArr aAcc))), .mov .r12 (.mem (hdr sW)),
    .mov .r15 (.mem (hdr sMinv)), .mov .rsi (.mem (hdr (sArr aTmp)))]

/-- The callee-saved registers back, through the first words of the
accumulator (`r8`) and the temporary (`rsi`). -/
def leave : List Instr :=
  [.movdquStore (at_ .r8 0) .xmm0, .movdquStore (at_ .r8 16) .xmm1, .movdquStore (at_ .rsi 0) .xmm2,
    .mov .rbx (.mem (at_ .r8 0)), .mov .rbp (.mem (at_ .r8 8)), .mov .r12 (.mem (at_ .r8 16)),
    .mov .r13 (.mem (at_ .r8 24)), .mov .r14 (.mem (at_ .rsi 0)), .mov .r15 (.mem (at_ .rsi 8))]

/-- `vg_rsa_mont_mul`: `montMul` (`aN`, `aAcc`, `aTmp`) for the arrays in
`edx`, `ecx` and `r8d`. -/
def mulBase : Prog isa :=
  .seq (.block (enter ++ basesR)) (.seq (.seq zeroAccLoop (.seq rounds (.seq subMod selectAcc))) (.block leave))

/-- The indices `o`, `a`, `b` into the argument registers. -/
def args (o a b : Nat) : List Instr :=
  [.mov32 .rdx (.imm (BitVec.ofNat 32 o)), .mov32 .rcx (.imm (BitVec.ofNat 32 a)),
    .mov32 .r8 (.imm (BitVec.ofNat 32 b))]

/-- `[o] = [a] [b] R⁻¹ mod m` by a call of the function `name`, whose code
is `body`. -/
def call (name : String) (body : Prog isa) (o a b : Nat) : Prog isa :=
  .seq (.block (args o a b)) (.call name body)

end VG.Impl.Bignum.X86_64.MontFn
