module

public import VerifiedGarbage.Impl.Bignum.X86.CrtLayout
public import VerifiedGarbage.Impl.Bignum.X86.CopyPadded
public import VerifiedGarbage.Impl.Bignum.X86.CheckedPrimePower
public import VerifiedGarbage.Impl.Bignum.X86.CheckedPreparePrime
public import VerifiedGarbage.Impl.Bignum.X86.CrtCoefficient
public import VerifiedGarbage.Impl.Bignum.X86.CrtRecombine
public import VerifiedGarbage.Impl.Bignum.X86.CheckFactorProduct
public import VerifiedGarbage.Impl.Bignum.X86.PublicFn
public import VerifiedGarbage.Impl.Bignum.X86.CrtNarrow

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

/-- The exponentiation of the factor at `prime` at `half n` words when CF
says its length fits them, at the modulus's width otherwise. -/
def fitPower (n prime exponent output : Nat) : Prog isa :=
  .ite .b (narrowPower n prime exponent output) (factorPower n prime exponent output)

/-- The number of factors `powers` has raised, in the multiplier's word, which
is dead between the factor-product check and the recombination. -/
def counterOffset : Nat := multiplierOffset

/-- The `k` words at slots `a` and `b` exchanged, through slot 20 (the narrow
exponentiation's table, dead between exponentiations). -/
def swapSlots (n k a b : Nat) : Prog isa :=
  .seq (copyArray k (slot n a) (slot n 20)) <|
  .seq (copyArray k (slot n b) (slot n a)) (copyArray k (slot n 20) (slot n b))

/-- `q`, `dq` and `mq` exchanged with `p`, `dp` and `mp`. -/
def swapFactors (n : Nat) : Prog isa :=
  .seq (swapSlots n n pSlot qSlot) <|
  .seq (swapSlots n n dpSlot dqSlot) (swapSlots n (2 * n) mpSlot mqSlot)

/-- CF set when the length of the factor in `p`'s slot (`p_len` first, then
`q_len`) fits `half n` words. -/
def selectLength (n : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.mem (sc counterOffset)), .alu .cmp .eax (.imm 0)])
    (.ite .e (.block (lengthFits n 7)) (.block (lengthFits n 9)))

/-- The power of the factor in `p`'s slot into `mp`'s, then the factors
exchanged, so that the second iteration raises `q` and the first's result
ends in `mp`. -/
def factorStep (n : Nat) : Prog isa :=
  .seq (selectLength n) <|
  .seq (fitPower n pSlot dpSlot mpSlot) <|
  .seq (swapFactors n)
    (.block [.mov .eax (.mem (sc counterOffset)), .alu .add .eax (.imm 1),
      .store (sc counterOffset) .eax, .alu .cmp .eax (.imm 2)])

/-- Both factors' powers, by one copy of the exponentiation's code. -/
def powers (n : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.imm 0), .store (sc counterOffset) .eax]) (.loop (factorStep n) .ne)

def compute (n : Nat) : Prog isa :=
  .seq (powers n) (.seq (coefficient n)
    (crtRecombine n (slot n productSlot) (slot n qSlot) (slot n 7)
      (slot n mqSlot) (slot n resultSlot) multiplierOffset))

end VG.Impl.Bignum.X86.Crt
