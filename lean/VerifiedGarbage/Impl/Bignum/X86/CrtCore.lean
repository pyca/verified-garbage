module

public import VerifiedGarbage.Impl.Bignum.X86.CrtLayout
public import VerifiedGarbage.Impl.Bignum.X86.CopyPadded
public import VerifiedGarbage.Impl.Bignum.X86.CheckedPrimePower
public import VerifiedGarbage.Impl.Bignum.X86.CheckedPreparePrime
public import VerifiedGarbage.Impl.Bignum.X86.CrtCoefficient
public import VerifiedGarbage.Impl.Bignum.X86.CrtRecombine
public import VerifiedGarbage.Impl.Bignum.X86.CheckFactorProduct
public import VerifiedGarbage.Impl.Bignum.X86.PublicFn

/-! # The i686 private CRT arithmetic pipeline in one reusable workspace -/

@[expose] public section
namespace VG.Impl.Bignum.X86.Crt
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

def importComponent (n argumentIndex destination : Nat) : Prog isa :=
  .seq (.block [.mov .esi (.mem (PublicFn.argument argumentIndex)),
    .mov .ecx (.mem (PublicFn.argument (argumentIndex + 1)))]) (loadBE n destination)

def importComponents (n : Nat) : Prog isa :=
  .seq (importComponent (2 * n) 2 (slot n modulusSlot)) <|
  .seq (importComponent n 4 (slot n inputSlot)) <|
  .seq (importComponent n 6 (slot n pSlot)) <|
  .seq (importComponent n 8 (slot n qSlot)) <|
  .seq (importComponent n 10 (slot n dpSlot)) <|
  .seq (importComponent n 12 (slot n dqSlot)) (importComponent n 14 (slot n inverseSlot))

def mergeAcceptance : List Instr :=
  [.mov .edx (.mem (sc acceptanceOffset)), .alu .and .edx (.reg .eax), .store (sc acceptanceOffset) .edx]

def validate (n : Nat) : Prog isa :=
  .seq (checkFactorProduct n (slot n productSlot) (slot n pSlot) (slot n qSlot)
    (slot n modulusSlot) multiplierOffset)
    (.seq (.block [.store (sc acceptanceOffset) .edx])
      (.seq (VG.Impl.Dsa.X86.lessThan n (slot n inputSlot) (slot n modulusSlot))
        (.seq (.block mergeAcceptance)
          (.seq (VG.Impl.Dsa.X86.lessThan n (slot n inverseSlot) (slot n pSlot)) (.block mergeAcceptance)))))

def loadPower (n prime exponent : Nat) : Prog isa :=
  .seq (copyArray n (slot n prime) (slot n 0))
    (.seq (copyArray n (slot n inputSlot) (slot n 5)) (copyArray n (slot n exponent) (slot n 8)))

def factorPower (n prime exponent output : Nat) : Prog isa :=
  .seq (loadPower n prime exponent)
    (.seq (checkedPrimePower n) (copyPadded n (slot n 6) (slot n output)))

def loadCoefficient (n : Nat) : Prog isa :=
  .seq (copyArray n (slot n pSlot) (slot n 0)) <|
  .seq (copyArray n (slot n mqSlot) (slot n 5)) <|
  .seq (copyArray n (slot n mpSlot) (slot n 6)) (copyArray n (slot n inverseSlot) (slot n 8))

def coefficient (n : Nat) : Prog isa :=
  .seq (loadCoefficient n) (.seq (checkedPreparePrime n) (crtCoefficient n))

def powers (n : Nat) : Prog isa :=
  .seq (factorPower n pSlot dpSlot mpSlot) (factorPower n qSlot dqSlot mqSlot)

def compute (n : Nat) : Prog isa :=
  .seq (powers n) (.seq (coefficient n)
    (crtRecombine n (slot n productSlot) (slot n qSlot) (slot n 7)
      (slot n mqSlot) (slot n resultSlot) multiplierOffset))

end VG.Impl.Bignum.X86.Crt
