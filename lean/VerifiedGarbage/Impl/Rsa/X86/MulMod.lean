module

public import VerifiedGarbage.Impl.Rsa.X86.KeyWs

/-! # Constant-schedule binary modular multiplication on i686

EDI holds the workspace; ESI is the public iteration count. Secret bits
select arrays through masks without affecting branches or addresses.
-/

@[expose] public section
namespace VG.Impl.Rsa.X86.Keys
open VG VG.X86 VG.Impl.Mont.X86

def addMod (w o a b m z t : Nat) : List (Prog isa) :=
  [sub3 w t z b, sub3 w (t + 1) a t, sub3 w (t + 2) (t + 1) m,
   .block [.store (sc sC) .ebx], sel w o (t + 2) (t + 1) sC]

def mulHead (w z y x t : Nat) : Prog isa :=
  .seq (.block (bitOf w sB y)) (sel w t z x sB)

def mulTail (w y : Nat) : Prog isa :=
  seqs [.block [.mov .ebx (.imm 0)], half w y,
    .block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)]]

def mulModStep (w z y x a m t : Nat) : Prog isa :=
  seqs [mulHead w z y x t, seqs (addMod w a a t m z (t + 1)),
    seqs (addMod w x x x m z (t + 1)), mulTail w y]

def mulMod (w z y x a m t : Nat) : Prog isa := .loop (mulModStep w z y x a m t) .ne

end VG.Impl.Rsa.X86.Keys
