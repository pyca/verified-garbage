module

public import VerifiedGarbage.Impl.Rsa.X86.KeyRt

/-! Parent-frame metadata for the reused run-time-width RSA arithmetic. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

/-- A small read-only argument frame lets every reused RSA operation read
only the public workspace pointer and byte width. -/
def arithmeticLay : Rsa.X86.KeyRt.Lay := { len := 2, ws := 1, shape := .base }

def arithmeticArgs : List Instr :=
  [.mov .eax (.imm 0), .store (at_ .esp 4) .eax,
   .store (at_ .esp 8) .edi, .store (at_ .esp 12) .esi]

/-- Edi is the workspace and esi its public number width in bytes. -/
def withArithmetic (body : Prog isa) : Prog isa :=
  .frame (.alloc 16) (.seq (.block arithmeticArgs) body) (.free 16)

def frameBytes : Nat := 128

end VG.Impl.Dsa.X86.Generation
