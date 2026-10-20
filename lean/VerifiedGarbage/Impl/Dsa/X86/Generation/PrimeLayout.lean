module

/-! # Persistent state in the parameter generator's arithmetic workspace

These words follow the largest Montgomery context and survive its
multiplications. The odd exponent is saved once for all witness rounds.
The reciprocal trial table lives in the separate parent workspace.
-/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation

def primeTwos : Nat := 8268
def primeIteration : Nat := 8272
def primeUniform : Nat := 8276
def primeUsed : Nat := 8280
def primeTape : Nat := 8284
def primeTapeLen : Nat := 8288
def primeStatus : Nat := 8292
def primeIsUniform : Nat := 8296
def primeWitness : Nat := 8300
def primeExponent : Nat := 8320
end VG.Impl.Dsa.X86.Generation
