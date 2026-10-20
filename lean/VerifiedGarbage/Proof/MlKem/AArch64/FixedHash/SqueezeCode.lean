module
public import VerifiedGarbage.Impl.MlKem.AArch64.Top


/-! # A compositional view of the fixed generator's output instructions -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64

def squeezePieceCode (sc : Reg) (st pos : Nat) (p : Piece) : List Instr :=
 (List.range (p.len/8)).flatMap fun i=>
  [.ldr .x .x9 sc (st+pos+8*i)] ++ ptrTo .x2 p.base (p.off+8*i) ++ [.str .x .x9 .x2 0]

def squeezeCode (sc : Reg) (st : Nat) : Nat→List Piece→List Instr
 | _,[]=>[]
 | pos,p::ps=>squeezePieceCode sc st pos p ++ squeezeCode sc st (pos+p.len) ps

end VG.Proof.MlKem.AArch64.FixedHash
