module

public import VerifiedGarbage.Proof.Dsa.X86.SharedCorrect
public import VerifiedGarbage.Proof.Dsa.X86.SharedTiming

/-! # Complete x86 DSA certificates against the shared contracts -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.X86

/-- A disjoint 1024/160 call; its zero-valued key is rejected at runtime. -/
def signingSatState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 16 else if a = 0x20008 then 40 else if a = 0x2000d then 32 else if a = 0x20010 then 168 else if a = 0x20011 then 1 else if a = 0x20014 then 128 else if a = 0x20019 then 64 else if a = 0x2001c then 20 else if a = 0x20021 then 80 else if a = 0x20029 then 128 else if a = 0x2002d then 8 else 0
  rd := [⟨0x2000, 424⟩, ⟨0x4000, 20⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x1000, 40⟩, ⟨0x8000, 16384⟩, ⟨0x20004, 44⟩]

theorem signingSatisfiable : ∃ s, (Spec.Dsa.signContract abi 32).pre s := by
  have a0 : arg signingSatState 0 = 4096 := by decide
  have a1 : arg signingSatState 1 = 40 := by decide
  have a2 : arg signingSatState 2 = 8192 := by decide
  have a3 : arg signingSatState 3 = 424 := by decide
  have a4 : arg signingSatState 4 = 128 := by decide
  have a5 : arg signingSatState 5 = 16384 := by decide
  have a6 : arg signingSatState 6 = 20 := by decide
  have a7 : arg signingSatState 7 = 20480 := by decide
  have a8 : arg signingSatState 8 = 0 := by decide
  have a9 : arg signingSatState 9 = 32768 := by decide
  have a10 : arg signingSatState 10 = 2048 := by decide
  have e : argAddr signingSatState 0 = 0x20004 := by decide
  have esp : signingSatState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e, esp, signingSatState] using signingSatState

theorem signing_verified : Verified target (Entry.operation true) (Spec.Dsa.signContract abi 32) :=
  ⟨signingCorrect, signingConstantTime, signingSatisfiable⟩

/-- A disjoint 1024/160 call; its zero-valued key is rejected at runtime. -/
def verifyingSatState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 32 else if a = 0x20008 then 148 else if a = 0x20009 then 1 else if a = 0x2000c then 128 else if a = 0x20010 then 20 else if a = 0x20015 then 64 else if a = 0x20018 then 40 else if a = 0x2001d then 80 else if a = 0x20025 then 128 else if a = 0x20029 then 8 else 0
  rd := [⟨0x2000, 404⟩, ⟨0x4000, 40⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x8000, 16384⟩, ⟨0x20004, 40⟩]

theorem verifyingSatisfiable : ∃ s, (Spec.Dsa.verifyContract abi 32).pre s := by
  have a0 : arg verifyingSatState 0 = 8192 := by decide
  have a1 : arg verifyingSatState 1 = 404 := by decide
  have a2 : arg verifyingSatState 2 = 128 := by decide
  have a3 : arg verifyingSatState 3 = 20 := by decide
  have a4 : arg verifyingSatState 4 = 16384 := by decide
  have a5 : arg verifyingSatState 5 = 40 := by decide
  have a6 : arg verifyingSatState 6 = 20480 := by decide
  have a7 : arg verifyingSatState 7 = 0 := by decide
  have a8 : arg verifyingSatState 8 = 32768 := by decide
  have a9 : arg verifyingSatState 9 = 2048 := by decide
  have e : argAddr verifyingSatState 0 = 0x20004 := by decide
  have esp : verifyingSatState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, e, esp, verifyingSatState] using verifyingSatState

theorem verifying_verified : Verified target (Entry.operation false) (Spec.Dsa.verifyContract abi 32) :=
  ⟨verifyingCorrect, verifyingConstantTime, verifyingSatisfiable⟩

end VG.Proof.Dsa.X86
