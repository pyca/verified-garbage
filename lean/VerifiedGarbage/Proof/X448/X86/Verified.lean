import VerifiedGarbage.Proof.X448.X86.CT
import VerifiedGarbage.Proof.X448.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.Contract

/-!
# X448 on x86 (32-bit): `Verified`

Correctness (`Main.lean`), constant time (`CT.lean`), satisfiability, and
the shared contract of `Spec/`, with the 20 bytes of stack below the return
address that the calls of the field functions use.
-/

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

theorem x448_verified :
    Verified X86.target Impl.X448.X86.x448 (Spec.X448.x448Contract X86.abi 20) :=
  Verified.of_correct x448_ok x448_ct (by
    have a0 : arg satState 0 = 0x1000 := by decide
    have a1 : arg satState 1 = 0x2000 := by decide
    have a2 : arg satState 2 = 0x3000 := by decide
    have a3 : arg satState 3 = 0x4000 := by decide
    have e : argAddr satState 0 = 0x8004 := by decide
    have esp : satState.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.X448.x448Contract, Spec.X448.x448Sig, Proof.X448.x448X86, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, e, esp] using Proof.X448.X86.satState)

end VG.Proof.X448.X86
