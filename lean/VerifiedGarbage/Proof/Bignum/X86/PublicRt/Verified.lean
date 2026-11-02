module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeTop
public import VerifiedGarbage.Proof.Rsa.Contract

/-! # Public RSA at a run-time width on i686 against its contract

Correctness (`correct`), constant time (`constantTime`), and a state meeting
the precondition, with 40 bytes of stack below `esp` for the calls.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.Impl.Bignum.X86

/-- Disjoint 512-bit buffers; the zero-valued modulus is rejected at runtime. -/
def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 16 else if a = 0x20008 then 64 else if a = 0x2000d then 32
    else if a = 0x20010 then 64 else if a = 0x20015 then 48 else if a = 0x20018 then 1
    else if a = 0x2001d then 64 else if a = 0x20020 then 64 else if a = 0x20025 then 128
    else if a = 0x20028 then 128 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 64⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 1024⟩, ⟨0x20004, 40⟩]

theorem satisfiable : ∃ s, (Proof.Rsa.publicCheckedContract abi 96).pre s := by
  have a0 : arg satState 0 = 4096 := by decide
  have a1 : arg satState 1 = 64 := by decide
  have a2 : arg satState 2 = 8192 := by decide
  have a3 : arg satState 3 = 64 := by decide
  have a4 : arg satState 4 = 12288 := by decide
  have a5 : arg satState 5 = 1 := by decide
  have a6 : arg satState 6 = 16384 := by decide
  have a7 : arg satState 7 = 64 := by decide
  have a8 : arg satState 8 = 32768 := by decide
  have a9 : arg satState 9 = 128 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Proof.Rsa.publicCheckedContract, Proof.Rsa.publicSig, abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, e, esp, satState, Spec.Rsa.lenValid,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords] using satState

theorem verified : Verified target PublicRt.code (Proof.Rsa.publicCheckedContract abi 96) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Bignum.X86.PublicRt
