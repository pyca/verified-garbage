module
public import VerifiedGarbage.Impl.Mont.X86

/-! # Shape a byte-aligned candidate in place

Hash finalization can write directly to the candidate buffer, avoiding an
extra digest copy. Set its high and low bits; all supported widths are
whole bytes and at least two bytes.
-/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def shape (len : Nat) : Prog isa := .block [
  .movzx8 .eax (at_ .edi 0), .alu .or .eax (.imm 128), .store8 (at_ .edi 0) .al,
  .movzx8 .eax (at_ .edi (len - 1)), .alu .or .eax (.imm 1), .store8 (at_ .edi (len - 1)) .al]
end VG.Impl.Dsa.X86.Generation
