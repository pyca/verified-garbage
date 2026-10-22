module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.ImportEntry
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessSample
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext

/-! # Read a fresh entropy block and sample a witness directly in its conversion operand -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.WitnessLoad
open VG VG.X86 VG.Impl.Bignum.X86.PublicContext
open VG.Impl.Mont.X86 (sc)

/-- Native words `k` through `2 w − 1` of the operand at `o` cleared: none
for a full-width candidate. -/
def zeros (o n : Nat) : List Instr :=
  (List.range n).flatMap fun j => [.mov .eax (.imm 0), .store (sc (o + 4 * j)) .eax]

def zeroTail (k w o : Nat) : List Instr := zeros (o + 4 * k) (2 * w - k)

/-- A witness of `D` octets, cut to its `k` low native words (the
candidate's bit length is `32 k`), for a candidate in a `w`-word geometry. -/
def codeAt (D k w : Nat) : Prog isa :=
  .seq (Import.load (D / 4) (slot w 6))
    (.seq (.block (zeroTail k w (slot w 6))) (WitnessSample.codeAt k w (slot w 6) (slot w 0)))

def code (w : Nat) : Prog isa := codeAt (8 * w) (2 * w) w

end VG.Impl.RsaKeyGen.X86.WitnessLoad
