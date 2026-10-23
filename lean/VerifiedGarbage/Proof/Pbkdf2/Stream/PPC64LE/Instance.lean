module

public import VerifiedGarbage.Proof.Pbkdf2.Stream.PPC64LE.Shared

/-!
# PBKDF2 over any streaming hash function on PPC64LE: an instance

A state satisfying `iterate`'s shared precondition, at each instance's sizes.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Stream.PPC64LE

open VG.PPC64LE

/-- A state satisfying `iterate`'s precondition, with states of `S` bytes, a
digest of `D` bytes, and `sc` bytes of scratch space. -/
def iterSat (S D sc : Nat) : State where
  gpr r := match r with
    | .r3 => 0x10000 | .r4 => 0x20000 | .r5 => 1 | .r6 => 0x30000 | .r7 => 0x40000
    | _ => 0
  lr := 0
  sp := 0x90000
  mem _ := 0
  rd := [⟨0x10000, 2 * S⟩, ⟨0x20000, D⟩]
  wr := [⟨0x30000, D⟩, ⟨0x40000, sc⟩]

end VG.Proof.Pbkdf2.Stream.PPC64LE
