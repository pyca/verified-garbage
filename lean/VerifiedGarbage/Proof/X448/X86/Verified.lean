module

import VerifiedGarbage.Proof.X448.X86.CT
public import VerifiedGarbage.Proof.X448.X86.Lit
public import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.X448.X86.Contract
import Mathlib.Tactic.SplitIfs

/-!
# X448 on x86 (32-bit): correct, with a state satisfying its contract

Correctness (`x448_ok`, from `Main.lean`) against the target's contract
`x448X86`, which `vg_x448_exchange`'s proof (`Exchange.lean`) composes with
constant time (`CT.lean`), and a state satisfying it (`satState`).
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000, 0x4000` at `0x8004`. -/
def satMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x30 else
  if a = 0x8011 then 0x40 else 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 56⟩, ⟨0x3000, 56⟩, ⟨0x8004, 16⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]

theorem x448_ok (s : State) (hs : Proof.X448.x448X86.pre s) :
    ∃ t s', Exec isa Impl.X448.X86.x448 s t s' ∧ abiPreserved s s' ∧ Proof.X448.x448X86.post s s' :=
  correct (Pre.of s hs)

end VG.Proof.X448.X86
