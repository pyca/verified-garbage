import VerifiedGarbage.Impl.Bignum.X86_64

/-!
# Montgomery multiplication as a function (x86-64)

`vg_rsa_mont_mul(ws, ws_len, o, a, b)` (`Spec/Rsa/Mont.lean`): the arrays
are given by their indices, in `edx`, `ecx` and `r8d`, and the working space
by `rdi`, as the code that calls it has them. It uses no stack, so that
calls of it run as their code inlined would (`Proof/Framework/X86_64/CallInline.lean`):
it keeps `rbx`, `rbp` and `r12`–`r15` in the low quadwords of `xmm8`–`xmm13`
(caller-saved) while it runs, and moves them back from there, without
writing them to memory and loading them back, which costs a stalled
store-to-load forwarding on some cores. It never writes `rdi`.

`call o a b` is the call, with the indices in the argument registers.
-/

namespace VG.Impl.Bignum.X86_64.MontFn

open VG.X86_64 VG.Impl.Bignum.X86_64.Public

/-- `[rdi + 8 i + 64]`: the header word holding the base of array `i`, for
`i` in a register. -/
def arrAt (i : Reg) : MemOp := { base := .rdi, index := some i, scale := 8, disp := 8 * sArr 0 }

/-- `[b + d]`. -/
def at_ (b : Reg) (d : Int) : MemOp := { base := b, disp := d }

/-- The indices zero-extended (only their low 32 bits are arguments). -/
def zext : List Instr := [.mov32 .rdx (.reg .rdx), .mov32 .rcx (.reg .rcx), .mov32 .r8 (.reg .r8)]

/-- The callee-saved registers into `xmm8`–`xmm13`, one to a register. -/
def saves : List Instr :=
  [.xop (.movq .xmm8 .rbx), .xop (.movq .xmm9 .rbp), .xop (.movq .xmm10 .r12),
    .xop (.movq .xmm11 .r13), .xop (.movq .xmm12 .r14), .xop (.movq .xmm13 .r15)]

/-- The callee-saved registers back from `xmm8`–`xmm13`. -/
def unsaves : List Instr :=
  [.movqR .rbx .xmm8, .movqR .rbp .xmm9, .movqR .r12 .xmm10, .movqR .r13 .xmm11,
    .movqR .r14 .xmm12, .movqR .r15 .xmm13]

/-- `zext`, then `saves`. -/
def enter : List Instr := zext ++ saves

/-- `bases` for the arrays in `edx`, `ecx` and `r8`: `rbx`, `r11`, `r9` the
bases of `o`, `a`, `b`; `r10`, `r8`, `rsi` those of `m`, the accumulator and
the temporary; `r12` `w` and `r15` `-m⁻¹`. -/
def basesR : List Instr :=
  [.mov .rbx (.mem (arrAt .rdx)), .mov .r11 (.mem (arrAt .rcx)), .mov .r9 (.mem (arrAt .r8)),
    .mov .r10 (.mem (hdr (sArr aN))), .mov .r8 (.mem (hdr (sArr aAcc))), .mov .r12 (.mem (hdr sW)),
    .mov .r15 (.mem (hdr sMinv)), .mov .rsi (.mem (hdr (sArr aTmp)))]

/-- The callee-saved registers back. -/
def leave : List Instr := unsaves

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
