module
public import VerifiedGarbage.Proof.Rsa.X86.KcABI

import VerifiedGarbage.Proof.Rsa.X86.KcOperationTiming
import VerifiedGarbage.Proof.Rsa.X86.KcCorrect

/-! # Complete i686 certificates for RSA key validation -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86
open VG.Impl.Rsa.X86.KeyCheck

def crtState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 16
    else if a = 0x20008 then 64
    else if a = 0x2000d then 32
    else if a = 0x20010 then 3
    else if a = 0x20015 then 48
    else if a = 0x20018 then 32
    else if a = 0x2001d then 64
    else if a = 0x20020 then 32
    else if a = 0x20025 then 80
    else if a = 0x20028 then 32
    else if a = 0x2002d then 96
    else if a = 0x20030 then 32
    else if a = 0x20035 then 112
    else if a = 0x20038 then 32
    else if a = 0x2003e then 1
    else if a = 0x20040 then 32
    else if a = 0x20041 then 4 else 0
  rd := [⟨4096, 64⟩, ⟨8192, 3⟩, ⟨12288, 32⟩, ⟨16384, 32⟩, ⟨20480, 32⟩, ⟨24576, 32⟩, ⟨28672, 32⟩]
  wr := [⟨0x10000, 8448⟩, ⟨0x20004, 64⟩]

theorem crt_satisfiable : ∃ s, (Spec.Rsa.checkCrtKeyContract abi 20).pre s := by
  have a0 : arg crtState 0 = 4096 := by decide
  have a1 : arg crtState 1 = 64 := by decide
  have a2 : arg crtState 2 = 8192 := by decide
  have a3 : arg crtState 3 = 3 := by decide
  have a4 : arg crtState 4 = 12288 := by decide
  have a5 : arg crtState 5 = 32 := by decide
  have a6 : arg crtState 6 = 16384 := by decide
  have a7 : arg crtState 7 = 32 := by decide
  have a8 : arg crtState 8 = 20480 := by decide
  have a9 : arg crtState 9 = 32 := by decide
  have a10 : arg crtState 10 = 24576 := by decide
  have a11 : arg crtState 11 = 32 := by decide
  have a12 : arg crtState 12 = 28672 := by decide
  have a13 : arg crtState 13 = 32 := by decide
  have a14 : arg crtState 14 = 65536 := by decide
  have a15 : arg crtState 15 = 1056 := by decide
  have e : argAddr crtState 0 = 0x20004 := by decide
  have esp : crtState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, e, esp, crtState, Spec.Rsa.lenValid, Spec.Rsa.scratchWords] using crtState

def keyState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 16
    else if a = 0x20008 then 64
    else if a = 0x2000d then 32
    else if a = 0x20010 then 3
    else if a = 0x20015 then 48
    else if a = 0x20018 then 64
    else if a = 0x2001d then 64
    else if a = 0x20020 then 32
    else if a = 0x20025 then 80
    else if a = 0x20028 then 32
    else if a = 0x2002d then 96
    else if a = 0x20030 then 32
    else if a = 0x20035 then 112
    else if a = 0x20038 then 32
    else if a = 0x2003d then 128
    else if a = 0x20040 then 32
    else if a = 0x20046 then 1
    else if a = 0x20048 then 32
    else if a = 0x20049 then 4 else 0
  rd := [⟨4096, 64⟩, ⟨8192, 3⟩, ⟨12288, 64⟩, ⟨16384, 32⟩, ⟨20480, 32⟩, ⟨24576, 32⟩, ⟨28672, 32⟩, ⟨32768, 32⟩]
  wr := [⟨0x10000, 8448⟩, ⟨0x20004, 72⟩]

theorem key_satisfiable : ∃ s, (Spec.Rsa.checkKeyContract abi 20).pre s := by
  have a0 : arg keyState 0 = 4096 := by decide
  have a1 : arg keyState 1 = 64 := by decide
  have a2 : arg keyState 2 = 8192 := by decide
  have a3 : arg keyState 3 = 3 := by decide
  have a4 : arg keyState 4 = 12288 := by decide
  have a5 : arg keyState 5 = 64 := by decide
  have a6 : arg keyState 6 = 16384 := by decide
  have a7 : arg keyState 7 = 32 := by decide
  have a8 : arg keyState 8 = 20480 := by decide
  have a9 : arg keyState 9 = 32 := by decide
  have a10 : arg keyState 10 = 24576 := by decide
  have a11 : arg keyState 11 = 32 := by decide
  have a12 : arg keyState 12 = 28672 := by decide
  have a13 : arg keyState 13 = 32 := by decide
  have a14 : arg keyState 14 = 32768 := by decide
  have a15 : arg keyState 15 = 32 := by decide
  have a16 : arg keyState 16 = 65536 := by decide
  have a17 : arg keyState 17 = 1056 := by decide
  have e : argAddr keyState 0 = 0x20004 := by decide
  have esp : keyState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, e, esp, keyState, Spec.Rsa.lenValid, Spec.Rsa.scratchWords] using keyState

theorem satisfiable (full : Bool) : ∃ s, (contract full).pre s := by
  cases full
  · exact crt_satisfiable
  · exact key_satisfiable

theorem verified (full : Bool) : Verified target (code full) (contract full) :=
  ⟨correct full, constantTime full, satisfiable full⟩

end VG.Proof.Rsa.X86.KeyCheck
