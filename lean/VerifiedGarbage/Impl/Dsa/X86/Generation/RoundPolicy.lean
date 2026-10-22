module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.RoundCall
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Header

/-! RSA's blinded-round minimum and DSA's uniform-witness target. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def roundIndex : Nat := Dsa.Generation.Layout.control + 8
def uniformCount : Nat := Dsa.Generation.Layout.control + 12
def primeStatus : Nat := Dsa.Generation.Layout.control + 20

/-- ECX is the next round index; EDX counts uniform witnesses. -/
def roundDecision (checks : Nat) : Prog isa :=
  .seq (.block [.alu .cmp .ecx (.imm 17)])
    (.ite .b (.block [.mov .eax (.imm 4)])
      (.seq (.block [.alu .cmp .edx (.imm (BitVec.ofNat 32 checks))])
        (.ite .b (.block [.mov .eax (.imm 4)]) (.block [.mov .eax (.imm 1)]))))

def roundCount : List Instr :=
  [.mov .ecx (.mem (sc roundIndex)), .alu .add .ecx (.imm 1), .store (sc roundIndex) .ecx,
    .mov .edx (.mem (sc uniformCount)), .alu .add .edx (.mem (sc witnessUniform)),
    .store (sc uniformCount) .edx]

def roundFinish : List Instr :=
  [.store (sc primeStatus) .eax, .alu .cmp .eax (.imm 4)]

def roundOutcome (checks : Nat) : Prog isa :=
  .ite .e (.block [.mov .eax (.imm 3)]) (.seq (.block roundCount) (roundDecision checks))

def roundTail (checks : Nat) : Prog isa :=
  .seq (.block [.alu .cmp .eax (.imm 0)])
    (.seq (roundOutcome checks) (.block roundFinish))

end VG.Impl.Dsa.X86.Generation
