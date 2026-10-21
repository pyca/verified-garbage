module
public import VerifiedGarbage.Impl.Dsa.X86.GenerateKey
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.InvokeTiming
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.ConstantTime
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Correct

/-! # The x86 key generator meets the existing bounded-tape contract -/
@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.Impl.Dsa.X86.GenerateKey

def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 16 else if a = 0x20008 then 168 else if a = 0x20009 then 1 else if a = 0x2000d then 112 else if a = 0x20011 then 32 else if a = 0x20014 then 20 else if a = 0x20015 then 1 else if a = 0x20018 then 128 else if a = 0x2001c then 20 else if a = 0x20021 then 80 else if a = 0x20029 then 128 else if a = 0x2002d then 36 else 0
  rd := [⟨0x2000, 276⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x1000, 424⟩, ⟨0x7000, 8⟩, ⟨0x8000, 73728⟩, ⟨0x20004, 44⟩]

theorem satisfiable : ∃ s, (Spec.Dsa.generateKeyContract abi 156).pre s := by
  have a0 : arg satState 0 = 4096 := by decide
  have a1 : arg satState 1 = 424 := by decide
  have a2 : arg satState 2 = 28672 := by decide
  have a3 : arg satState 3 = 8192 := by decide
  have a4 : arg satState 4 = 276 := by decide
  have a5 : arg satState 5 = 128 := by decide
  have a6 : arg satState 6 = 20 := by decide
  have a7 : arg satState 7 = 20480 := by decide
  have a8 : arg satState 8 = 0 := by decide
  have a9 : arg satState 9 = 32768 := by decide
  have a10 : arg satState 10 = 9216 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argSlots, argVal, argBytes,
    stackBelow] [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e, esp, satState] using satState

/-- An internal checker may establish an invariant for an inlined derivation. -/
theorem verifiedWith {I : State → Mem → Prop} (C : CheckInvoke I) (D : DeriveInvoke I)
    (stable : StableScratch I) (nc : NoSp C.code) (nd : NoSp D.code)
    (ctC : CheckInvokeCT C) (ctD : DeriveInvokeCT D) :
    Verified target (codeWith C.code D.code) (Spec.Dsa.generateKeyContract abi 156) :=
  ⟨generateKeyWith_correct C D stable nc nd,
    generateKeyWith_constantTime C D stable ctC ctD, satisfiable⟩

theorem verified (C : CheckCall.CheckFn) (D : DeriveFn) :
    Verified target (code C.name D.name C.code D.code) (Spec.Dsa.generateKeyContract abi 156) :=
  ⟨generateKey_correct C D, generateKey_constantTime C D, satisfiable⟩
end VG.Proof.Dsa.X86.KeyRandom
