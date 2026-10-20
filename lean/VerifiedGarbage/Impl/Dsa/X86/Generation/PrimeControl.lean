module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.DrawWitness
public import VerifiedGarbage.Impl.Dsa.X86.Generation.SampleWitness
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrepareExponent

/-! # Uniform-witness counting and exact tape exhaustion for DSA primality tests -/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def primeMark (status : Nat) : List Instr :=
  [.mov .eax (.imm (BitVec.ofNat 32 status)), .store (sc primeStatus) .eax]

def primeInit : List Instr :=
  [.mov .eax (.imm 0), .store (sc primeUniform) .eax] ++ primeMark 4

def primeTapeCheck (drawBytes : Nat) : List Instr :=
  [.mov .ecx (.mem (sc primeTapeLen)), .alu .sub .ecx (.mem (sc primeUsed)),
   .alu .cmp .ecx (.imm (BitVec.ofNat 32 drawBytes))]

def primeUniformUpdate (checks : Nat) : List Instr :=
  [.mov .eax (.mem (sc primeIsUniform)), .mov .ecx (.imm 0), .alu .sub .ecx (.reg .eax),
   .mov .eax (.mem (sc primeUniform)), .alu .add .eax (.reg .ecx), .store (sc primeUniform) .eax,
   .alu .cmp .eax (.imm (BitVec.ofNat 32 checks))]

def primeRoundResult (checks : Nat) : Prog isa :=
  .seq (.block [.alu .cmp .eax (.imm 0)]) (.ite .e (.block (primeMark 3))
    (.seq (.block (primeUniformUpdate checks)) (.ite .ae (.block (primeMark 1)) (.block (primeMark 4)))))

def primeDrawRound (len drawBytes checks : Nat) : Prog isa :=
  let n := (len + 7) / 8
  .seq (drawWitness len drawBytes) (.seq (sampleWitness len)
    (.seq (.seq (restoreExponent n) (round n (2 * n))) (primeRoundResult checks)))

def primeStep (len drawBytes checks : Nat) : Prog isa :=
  .seq (.block (primeTapeCheck drawBytes))
    (.seq (.ite .b (.block (primeMark 0)) (primeDrawRound len drawBytes checks))
      (.block [.mov .eax (.mem (sc primeStatus)), .alu .cmp .eax (.imm 4)]))

def primeLoop (len drawBytes checks : Nat) : Prog isa :=
  .seq (.block primeInit) (.loop (primeStep len drawBytes checks) .e)
end VG.Impl.Dsa.X86.Generation
