module

public import VerifiedGarbage.Impl.Mont.X86.Exponent
public import VerifiedGarbage.Impl.Mont.X86.Inverse

/-! # Runtime Montgomery workspace and exponentiation on 32-bit x86 -/

@[expose] public section
namespace VG.Impl.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86

/-- Each slot accommodates even the double-width accumulator. -/
def stride (n : Nat) : Nat := 16 * n + 8

def slot (n i : Nat) : Nat := 64 + i * stride n

def contextBytes (n : Nat) : Nat := slot n 9

def contextMod (n : Nat) : Mod := { n, mo := slot n 0, tmp := slot n 1, minv := 0 }

/-- Slots: modulus, subtraction temporary, accumulator, one, R², base,
result, conditional product, mutable exponent. The header stores the inverse
and selection mask. All offsets depend only on public widths. -/
def contextSetup (n : Nat) : Prog isa :=
  .seq (.block (setupInverse (slot n 0) 0)) (.seq (one n (slot n 3))
    (powerTwo (contextMod n) (slot n 2) (slot n 4) (128 * n)))

def exponentProduct (n : Nat) : Prog isa :=
  .seq (.block (exponentMask (slot n 8) 4))
  (.seq (mul (contextMod n) 0 (slot n 2) (slot n 7) (slot n 6) (slot n 5))
    (selectProduct (contextMod n) (slot n 6) (slot n 7) 4))

def exponentBody (n expWords : Nat) : Prog isa :=
  .seq (exponentProduct n)
  (.seq (mul (contextMod n) 0 (slot n 2) (slot n 5) (slot n 5) (slot n 5))
    (shiftDown expWords (slot n 8)))

def exponentStep (n expWords : Nat) : Prog isa :=
  .seq (exponentBody n expWords)
    (.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)])

/-- Input base and exponent occupy slots five and eight. The result replaces
slot six. The exponent is consumed using a fixed public number of iterations. -/
def exponentiate (n expWords : Nat) : Prog isa :=
  .seq (mul (contextMod n) 0 (slot n 2) (slot n 6) (slot n 4) (slot n 3))
  (.seq (mul (contextMod n) 0 (slot n 2) (slot n 5) (slot n 5) (slot n 4))
  (.seq (.block [.mov .esi (.imm (BitVec.ofNat 32 (32 * expWords)))])
  (.seq (.loop (exponentStep n expWords) .ne)
    (mul (contextMod n) 0 (slot n 2) (slot n 6) (slot n 6) (slot n 3)))))

end VG.Impl.Mont.X86.Dynamic
