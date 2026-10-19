module
public import VerifiedGarbage.Impl.MillerRabin.X86_64.Layout
import VerifiedGarbage.Impl.MillerRabin.X86_64.Round


/-! # Keep the RSA workspace around a shared Miller–Rabin call -/

@[expose] public section

namespace VG.Impl.MillerRabin.X86_64.Caller

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate

/-- Padding word w of Montgomery one (array 25), kept by the shared round. -/
def padAddress : List Instr := [
  .mov .rax (.mem (hdr sW)), .mov .rcx (.imm 208), .imul .rcx .rax,
  .alu .add .rcx (.imm 656), .alu .add .rcx (.reg .rdi)]

/-- Save rbx, use it for the workspace, and narrow the callee's capacity. -/
def save : List Instr := padAddress ++ [
  .store (at0 .rcx) .rbx, .mov .rbx (.reg .rdi),
  .mov .rsi (.reg .rax), .mov .rdx (.imm 28), .imul .rsi .rdx,
  .alu .add .rsi (.imm 88)]

/-- Restore the workspace, translate the low 32-bit result to RSA's mask,
and restore rbx. The result never controls a branch here. -/
def restore : List Instr := [
  .mov .rdi (.reg .rbx), .mov32 .rax (.reg .rax), .mov .rcx (.imm 0),
  .alu .sub .rcx (.reg .rax), .store (hdr kFlag) .rcx] ++
  padAddress ++ [.mov .rbx (.mem (at0 .rcx))]

def call (name : String) (callee : Prog isa) : Prog isa :=
  .seq (.block save) (.seq (.call name callee) (.block restore))

end VG.Impl.MillerRabin.X86_64.Caller
