module

public import VerifiedGarbage.Impl.Bignum.AArch64.ProductDispatch
public import VerifiedGarbage.Impl.Rsa.AArch64

/-! Canonical FFDH comb context over the existing eight-array Montgomery workspace.
All header controls are public; secret scalars and selected residues live in arrays. -/
@[expose] public section
namespace VG.Impl.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

def sCtx : Nat := 16
def sDom : Nat := 17
def sLen : Nat := 18
def sDL : Nat := 19
def sBits : Nat := 20
def sBytes : Nat := 21
def sRows : Nat := 22
def sX : Nat := 23
def sY : Nat := 24
def sRand : Nat := 25
def sI : Nat := 26
def sD : Nat := 27
def sTmp : Nat := 28
def sJ : Nat := 29
def sTab : Nat := 30
def sMask : Nat := 31

def load (a : Nat) : Prog isa := .seq (.block [ldh .x8 (sArr a),ldh .x12 sW]) loadBE

def copy (a b : Nat) : Prog isa :=
 .seq (.block [ldh .x12 sW,ldh .x16 (sArr b),ldh .x17 (sArr a)]) copyWords

def const (a n : Nat) : Prog isa :=
 .seq (.block [ldh .x12 sW,movi .x9 n,movi .x13 0]) (setWord a)

/-- Context table entry at the public digit x3; its w words at x17. -/
def entryPtr : List Instr :=
 [ldh .x17 sCtx,ldh .x12 sW,.addImm .x .x3 .x3 2,
  .mul .x .x3 .x3 .x12,.lsl .x .x3 .x3 3,.add .x .x17 .x17 .x3,.addImm .x .x17 .x17 24]

def storeEntry (a : Nat) : Prog isa :=
 .seq (.block (entryPtr ++ [ldh .x16 (sArr a)])) copyWords

/-- Load a public context entry into an arithmetic operand array. -/
def loadEntry (a : Nat) : Prog isa :=
 .seq (.block (entryPtr ++ [mov .x16 .x17,ldh .x17 (sArr a)])) copyWords

/-- Import the canonical p/R² prefix and reconstruct the inverse word. -/
def importPrefix : Prog isa := seqs [
 .block VG.Impl.Rsa.AArch64.head,
 .block [ldh .x16 sCtx,.addImm .x .x16 .x16 24,ldh .x17 (sArr 0),ldh .x12 sW],copyWords,
 .block [ldh .x17 (sArr 4),ldh .x12 sW],copyWords,
 .block ([ldh .x8 (sArr 0),ld .x3 .x8] ++ minv ++ [sth .x15 sMinv])]

end VG.Impl.Ffdh.AArch64.Cached
