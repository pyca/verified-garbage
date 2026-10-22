module

public import VerifiedGarbage.TCB.X86.Isa

/-!
# The frames of the x86 RSA padding functions

The x86 functions of RSAES-PKCS1-v1_5 (`vg_rsa_pkcs1_encrypt_precomputed`,
`vg_rsa_pkcs1_decrypt`) run their body in two frames, as
`vg_rsa_pkcs1_sign` does (`Impl/RsaPkcs1Sig/X86/Sign.lean`): a push of the
callee-saved registers `ebx`, `ebp`, `esi` and `edi` (16 bytes), and in it a
frame of `F` bytes; then they restore `edi`, `esi` and `ebp` from the push
and pop it into `ebx`. So the body may use every register but `esp`, and
argument `j` (from 0) is at `esp + argOff F j` in the inner frame: above the
frame, the push and the return address.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.X86

open VG VG.X86

/-- The registers pushed on entry. -/
def savedRegs : List Reg := [.ebx, .ebp, .esi, .edi]

/-- `edi`, `esi` and `ebp` back from the push, which `esp` points to. -/
def restoreRegs : List Instr :=
  [.mov .edi (.mem ⟨.esp, 0⟩), .mov .esi (.mem ⟨.esp, 4⟩), .mov .ebp (.mem ⟨.esp, 8⟩)]

/-- `body` in a frame of `F` bytes, inside the push of the callee-saved
registers. -/
def wrap (F : Nat) (body : Prog isa) : Prog isa :=
  .frame (.push savedRegs) (.seq (.frame (.alloc F) body (.free F)) (.block restoreRegs)) (.pop .ebx 4)

/-- The offset from `esp` in the inner frame of argument `j` (from 0): the
frame, the push and the return address are below it. -/
def argOff (F j : Nat) : Nat := F + 20 + 4 * j

/-- `[esp + d]`. -/
def stk (d : Nat) : MemOp := ⟨.esp, d⟩

/-- `[r + d]`. -/
def at_ (r : Reg) (d : Nat) : MemOp := ⟨r, d⟩

end VG.Impl.RsaPkcs1Sig.X86
