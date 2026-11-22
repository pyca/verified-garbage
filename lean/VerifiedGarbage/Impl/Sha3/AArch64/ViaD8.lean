module

public import VerifiedGarbage.Impl.Sha3.AArch64.Callee
public import VerifiedGarbage.Impl.ICall

/-!
# Calling a Keccak permutation by the address in `d8`

A function that is the same code for every Keccak permutation it calls
calls the permutation by its address, which its caller leaves in the low 64
bits of `v8` (`d8`, which the calling convention preserves across calls):
`umov x16, v8.d[0]`, then `blr x16`, an indirect call of `c`
(`Code.icalls`), whose printed code does not name `c`. `entryD8 n name body`
is the function that calls such a function, `name`, whose code is `body`,
with the address of `n` in `d8`, in a frame of 16 bytes: its return address
at `sp`, and its caller's `d8` at `sp + 8`, which it restores.
-/

@[expose] public section

namespace VG.Impl.Sha3.AArch64

open VG.AArch64

/-- The call of `c` by the address in `v8`'s low 64 bits. -/
def Callee.viaD8 (c : Callee) : Prog isa :=
  .seq (.block [.umov .x .x16 .v8 0]) (Code.icalls (.blr .x16) [(c.name, c.code)])

/-- `umov x16, v8.d[0]; str x30, [sp]; str x16, [sp, #8]; adrp/add x16, n;
ins v8.d[0], x16`: save the return address and `d8`, and put `n`'s address
in `d8`. -/
def enterD8 (n : String) : List Instr :=
  [.umov .x .x16 .v8 0, .strSp .x30 0, .strSp .x16 8, .adrSym .x16 n, .vop (.ins .d2 .v8 0 .x16)]

/-- `ldr x16, [sp, #8]; ins v8.d[0], x16; ldr x30, [sp]`: restore `d8` and
the return address. -/
def leaveD8 : List Instr := [.ldrSp .x16 8, .vop (.ins .d2 .v8 0 .x16), .ldrSp .x30 0]

/-- A call of `name`, whose code is `body`, with `n`'s address in `d8`. -/
def entryD8 (n name : String) (body : Prog isa) : Prog isa :=
  .frame (.alloc 16) (.seq (.block (enterD8 n)) (.seq (.call name body) (.block leaveD8))) (.free 16)

end VG.Impl.Sha3.AArch64
