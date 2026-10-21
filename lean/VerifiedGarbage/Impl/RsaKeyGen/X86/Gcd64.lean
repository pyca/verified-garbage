module

public import VerifiedGarbage.Impl.Rsa.X86.Inverse

/-! # Fixed-step 64-bit binary GCD using the native RSA key workspace

Only the u/v part of the existing binary inverse step is needed. Two banks
avoid copying the operands between steps. ESI counts 64 pairs of steps,
enough to terminate from two 64-bit values with an odd second operand.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.Keys

def bankStep (a b : Nat) : Prog isa := seqs [
  .block (bitOf 2 sOdd a), sub3 2 aT1 a (a + 1),
  .block ([.store (sc sB) .ebx] ++ andS sC sOdd sB), sub3 2 aT2 (a + 1) a,
  sel 2 (b + 1) (a + 1) a sC, sel 2 aT3 aT1 aT2 sC,
  sel 2 b a aT3 sOdd, .block [.mov .ebx (.imm 0)], half 2 b]

def body : Prog isa := .seq (bankStep 0 4) (.seq (bankStep 4 0)
  (.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)]))

def code : Prog isa :=
  .seq (.block [.mov .esi (.imm 64)]) (.loop body .ne)

end VG.Impl.RsaKeyGen.X86.Gcd64
