module

public import VerifiedGarbage.Proof.Bignum.X86.CrtOperationTiming
public import VerifiedGarbage.Proof.Bignum.X86.CrtObservations

/-! # Complete i686 certificate for the private CRT RSA operation -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Impl.Bignum.X86

theorem constantTime : ConstantTime isa (Spec.Rsa.privateCrtContract abi 20).pre
    (Spec.Rsa.privateCrtContract abi 20).pub Crt.code := by
  intro s t tr ur sf tf S T H E F
  have Args := arguments H
  exact operation_trace (crtABI_of S) (crtABI_of T) Args.2 Args.1 (modulusBytes H) E F

/-- Disjoint minimum-length buffers with a runtime-rejected zero modulus. -/
def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 16
    else if a = 0x20008 then 64
    else if a = 0x2000d then 32
    else if a = 0x20010 then 64
    else if a = 0x20015 then 48
    else if a = 0x20018 then 64
    else if a = 0x2001d then 64
    else if a = 0x20020 then 1
    else if a = 0x20025 then 80
    else if a = 0x20028 then 1
    else if a = 0x2002d then 96
    else if a = 0x20030 then 1
    else if a = 0x20035 then 112
    else if a = 0x20038 then 1
    else if a = 0x2003d then 128
    else if a = 0x20040 then 1
    else if a = 0x20045 then 144
    else if a = 0x20048 then 32
    else if a = 0x20049 then 4 else 0
  rd := [⟨8192, 64⟩, ⟨12288, 64⟩, ⟨16384, 1⟩, ⟨20480, 1⟩, ⟨24576, 1⟩, ⟨28672, 1⟩, ⟨32768, 1⟩]
  wr := [⟨4096, 64⟩, ⟨36864, 8448⟩, ⟨0x20004, 72⟩]

theorem satisfiable : ∃ s, (Spec.Rsa.privateCrtContract abi 20).pre s := by
  have a0 : arg satState 0 = 4096 := by decide
  have a1 : arg satState 1 = 64 := by decide
  have a2 : arg satState 2 = 8192 := by decide
  have a3 : arg satState 3 = 64 := by decide
  have a4 : arg satState 4 = 12288 := by decide
  have a5 : arg satState 5 = 64 := by decide
  have a6 : arg satState 6 = 16384 := by decide
  have a7 : arg satState 7 = 1 := by decide
  have a8 : arg satState 8 = 20480 := by decide
  have a9 : arg satState 9 = 1 := by decide
  have a10 : arg satState 10 = 24576 := by decide
  have a11 : arg satState 11 = 1 := by decide
  have a12 : arg satState 12 = 28672 := by decide
  have a13 : arg satState 13 = 1 := by decide
  have a14 : arg satState 14 = 32768 := by decide
  have a15 : arg satState 15 = 1 := by decide
  have a16 : arg satState 16 = 36864 := by decide
  have a17 : arg satState 17 = 1056 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, e, esp, satState, Spec.Rsa.lenValid,
      Spec.Rsa.scratchWords] using satState

theorem verified : Verified target Crt.code (Spec.Rsa.privateCrtContract abi 20) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Bignum.X86.Crt
