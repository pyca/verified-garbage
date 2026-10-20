module

public import VerifiedGarbage.Impl.Bignum.X86.PublicFn

/-! # The entry and return of private CRT RSA with the i686 cdecl ABI

The callee-saved registers saved in the working space's header (argument 16),
and restored from it.
-/

@[expose] public section
namespace VG.Impl.Bignum.X86.Crt
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

def savedRegisters : List (Reg × Nat) := [(.ebx, 32), (.ebp, 36), (.esi, 40), (.edi, 44)]
def save : List Instr := savedRegisters.map fun (r, d) => .store (at_ .eax d) r
def restore : List Instr := savedRegisters.map fun (r, d) => .mov r (.mem (sc d))

def entry : List Instr :=
  [.mov .eax (.mem (PublicFn.argument 16))] ++ save ++ [.mov .edi (.reg .eax)]

end VG.Impl.Bignum.X86.Crt
