module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64

/-! # A fixed sequence reduces a whole candidate word without a bit-loop branch -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Mod64
open VG.X86

def steps (exponent count : Nat) : List Instr := (List.range count).flatMap fun _ => bit exponent

def word (exponent : Nat) : List Instr := steps exponent 32

end VG.Impl.RsaKeyGen.X86.Mod64
