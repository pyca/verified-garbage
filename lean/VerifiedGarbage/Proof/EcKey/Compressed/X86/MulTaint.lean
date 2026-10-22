module

public import VerifiedGarbage.Proof.Framework.X86.TaintMono

/-! # Entry taint for the field-multiplication calls of the x86 point codecs -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86

/-- The codec's three public arguments remain above the multiplication's
return address and four-word argument frame. Only the frame's argument words
need public slots; the output and working space are otherwise secret.
The output length differs between compression and decompression. -/
def codecMulT (outputLen : Nat) : VG.X86.Taint.T :=
  { regs := .ofList [.eax, .ecx, .edx, .esp, .esi, .edi], flags := false,
    lens := [16, outputLen, 8192], bases := [(.edi, 2, 0), (.esp, 0, 4)],
    slots := [(0, 12, 4), (0, 8, 4), (0, 4, 4), (0, 0, 4)], wbases := [(0, 0, 2)],
    argLen := 16, argBases := [(4, 1), (12, 2)], stk := [none, some 16], room := 28 }

end VG.Proof.EcKey.Compressed.X86
