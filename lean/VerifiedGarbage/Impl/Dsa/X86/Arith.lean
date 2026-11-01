module

public import VerifiedGarbage.Impl.Dsa.X86.Pow
public import VerifiedGarbage.Impl.Dsa.X86.Arithmetic
public import VerifiedGarbage.Impl.Dsa.X86.Stream
public import VerifiedGarbage.Impl.Dsa.HelperLayout

/-! # DSA's reductions and products as functions on IA-32

`vg_dsa_reduce_{n}` and `vg_dsa_mulmod_{n}` (`Proof/Dsa/ModArithContract.lean`)
reduce the `data_len` bytes at `data` (`reduceStream`) or multiply the
ordinary integers in slots 5 and 8 (`ordinaryMul`), modulo the one in
slot 0, into slot 6, with the register saves of `Pow.lean`. The product sets
up the complete context (`contextSetup`); the reduction needs only the
modulus and its inverse (`contextStart`), and keeps the bytes' length in the
header of `ws`, at byte 24. The caller loads the modulus (and operands) and
passes the working space as `vg_dsa_pow_{n}_{e}`'s callers do (`Pow.call`),
so each width has one reduction and one product shared by every DSA
function.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86.Arith
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Pow

/-- The header's words that keep the bytes' length and address. -/
def lenAt : Nat := 24
def dataAt : Nat := 28

/-- `data` and `data_len`, arguments 2 and 3, into the header. -/
def stash : List Instr :=
  [.mov .eax (.mem (at_ .esp 16)), .mov .ecx (.mem (at_ .esp 12)),
    .store (sc lenAt) .eax, .store (sc dataAt) .ecx]

/-- The saves, the arguments into the header, the context's start, and the
bytes' address into `esi`. -/
def reducePrefix (n : Nat) : Prog isa :=
  .seq (.block Pow.save) <| .seq (.block stash) <| .seq (contextStart n) <|
  .block [.mov .esi (.mem (sc dataAt))]

def reduceBody (n : Nat) : Prog isa :=
  .seq (reducePrefix n) (.seq (reduceStream n (.mem (sc lenAt))) (.block Pow.restore))

def reduceLayout (n : Nat) : Impl.Dsa.ModArith.ReduceLayout where
  n := n
  modulus := slot n 0
  result := slot n 6
  scratch := Pow.scratch n
  size := contextBytes n

def reduceName (n : Nat) : String := s!"vg_dsa_reduce_{(reduceLayout n).n}"

/-- Reduce the `ebx` bytes at `esi`: cdecl's four stack arguments, the
workspace, its length, and the bytes. -/
def reduceCall (n : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.imm (BitVec.ofNat 32 (contextBytes n / 8)))])
    (.frame (.push [.ebx, .esi, .eax, .edi]) (.call (reduceName n) (reduceBody n)) (.pop .eax 4))

def mulBody (n : Nat) : Prog isa :=
  .seq (.block Pow.save) (.seq (contextSetup n) (.seq (ordinaryMul n) (.block Pow.restore)))

def mulLayout (n : Nat) : Impl.Dsa.ModArith.MulLayout where
  n := n
  modulus := slot n 0
  a := slot n 5
  b := slot n 8
  result := slot n 6
  scratch := Pow.scratch n
  size := contextBytes n

def mulName (n : Nat) : String := s!"vg_dsa_mulmod_{(mulLayout n).n}"

/-- Pass the workspace and its length using cdecl's two stack arguments. -/
def mulCall (n : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.imm (BitVec.ofNat 32 (contextBytes n / 8)))])
    (.frame (.push [.eax, .edi]) (.call (mulName n) (mulBody n)) (.pop .eax 2))

end VG.Impl.Dsa.X86.Arith
