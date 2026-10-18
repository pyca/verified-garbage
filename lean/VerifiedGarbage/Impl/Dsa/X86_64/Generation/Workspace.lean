module

public import VerifiedGarbage.Impl.Rsa.X86_64.Keys

/-! # Initialize the shared candidate/primality workspace from arbitrary bytes -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys

def workspaceHead (w : Nat) : List Instr :=
  [.mov32 .r12 (.imm (BitVec.ofNat 32 w)), .store (hdr sW) .r12,
   .mov32 .rax (.imm 0), .store (hdr sMinv) .rax]

def workspaceStride (w : Nat) : List Instr :=
  [.mov32 .rax (.imm (BitVec.ofNat 32 (8 * (w + 2)))), .store (hdr sStride) .rax]

def workspace (w : Nat) : Prog isa := seqs [
  .block (workspaceHead w), .block setBases, .block (workspaceStride w)]

end VG.Impl.Dsa.X86_64.Generation
