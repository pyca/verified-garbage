module

public import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyPrologue
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyRecurrence
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86
open VG.Proof.Aes.X86 (keyP ekSchP ekSchR)

/-- A complete schedule, with the unchanged body-entry GPRs and declared frame. -/
structure KeyDone (s₀ entry : State) (nk : Nat) (s : State) : Prop where
  words : Good s.mem ((ekSchP s₀).setWidth 64)
    (W s₀.mem ((keyP s₀).setWidth 64) nk) (4 * (nk + 7))
  gpr : s.gpr = entry.gpr
  rd : s.rd = entry.rd
  wr : s.wr = entry.wr
  frame : Frame [ekSchR s₀] s₀.mem s.mem

end VG.Proof.Aes.X86.AesNi
