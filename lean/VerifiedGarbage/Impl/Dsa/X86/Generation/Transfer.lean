module

public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Impl.Mont.X86.Context
public import VerifiedGarbage.Impl.Weierstrass.X86
public import VerifiedGarbage.Spec.Rsa.Mont

/-! Transfer prepared numbers using the existing native word-copy implementation. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86.Dynamic

structure WordTransfer where
  words : Nat
  destination : Nat
  source : Nat

def WordTransfer.code (t : WordTransfer) : Prog isa :=
  .block (Weierstrass.X86.copy t.words t.destination t.source)

def candidateTransfer (n : Nat) : WordTransfer :=
  { words := 2 * n, destination := Dsa.Generation.Layout.arithmetic + 160, source := slot n 0 }

/-- Save the exponent and its full 64-bit one-hot tail before the compact
header replaces the arithmetic workspace's original header and arrays. -/
def saveExponentTransfers (n : Nat) : List WordTransfer :=
  [{ words := 2 * n, destination := slot n 8, source := Dsa.Generation.Layout.arithmetic + 160 },
   { words := 2, destination := slot n 8 + 8 * n, source := Dsa.Generation.Layout.arithmetic + 64 }]

def compactNumberTransfer (n destination source : Nat) : WordTransfer :=
  { words := 2 * n,
    destination := Dsa.Generation.Layout.arithmetic + Spec.Rsa.Mont.arrAt n destination,
    source := slot n source }

/-- R-squared lives outside the round's borrowed scratch. Ordinary one
initializes the witness to a reduced value before sampled witnesses replace it. -/
def compactTransfers (n : Nat) : List WordTransfer :=
  [compactNumberTransfer n 0 0, compactNumberTransfer n 5 3, compactNumberTransfer n 7 4,
   compactNumberTransfer n 9 6, compactNumberTransfer n 10 7,
   { words := 2 * n + 2,
     destination := Dsa.Generation.Layout.arithmetic + Spec.Rsa.Mont.arrAt n 27,
     source := slot n 8 }]

def transferWords (ts : List WordTransfer) : Prog isa :=
  ts.foldr (fun t rest => .seq t.code rest) (.block [])

end VG.Impl.Dsa.X86.Generation
