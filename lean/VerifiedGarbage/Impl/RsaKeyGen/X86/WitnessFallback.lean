module

public import VerifiedGarbage.Impl.Mont.X86

/-! # Masked witness fallback sets bit one and clears the most significant bit -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.WitnessFallback
open VG VG.X86 VG.Impl.Mont.X86

/-- EAX is the uniform-witness mask and remains unchanged. -/
def low (src : Nat) : List Instr :=
  [.mov .ecx (.reg .eax), .alu .xor .ecx (.imm (BitVec.allOnes 32)), .alu .and .ecx (.imm 2),
    .alu .or .ecx (.mem (sc src)), .store (sc src) .ecx]

def high (offset : Nat) : List Instr :=
  [.mov .ecx (.reg .eax), .alu .xor .ecx (.imm (BitVec.allOnes 32)), .alu .and .ecx (.imm 0x80000000),
    .alu .xor .ecx (.imm (BitVec.allOnes 32)), .alu .and .ecx (.mem (sc offset)), .store (sc offset) .ecx]

/-- For a witness of `k` native words: bit one set, and the most significant
bit of word `k − 1` cleared. -/
def codeAt (k src : Nat) : List Instr := low src ++ high (src + 4 * k - 4)

def code (w src : Nat) : List Instr := codeAt (2 * w) src

end VG.Impl.RsaKeyGen.X86.WitnessFallback
