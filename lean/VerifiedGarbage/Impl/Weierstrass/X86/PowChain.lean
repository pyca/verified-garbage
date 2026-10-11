module

public import VerifiedGarbage.Impl.Weierstrass.X86

/-! # Fixed addition chains using the existing exponentiation slots -/

@[expose] public section

namespace VG.Impl.Weierstrass.X86
open VG.X86 VG.Impl.Mont.X86 VG.Impl.Weierstrass

inductive PowerOp where
  | save
  | squares (n : Nat)
  | mulBase
  | mulSaved
  deriving Repr

/-- Repeat squaring with a public counter, retaining the saved power. -/
def squareRun (P : PowCfg) (F : Spec.Weierstrass.Mont.Modulus) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (.block [.mov .esi (.imm (BitVec.ofNat 32 (n + 1)))])
      (.loop (.seq (.block [decCounter])
        (.seq (Mont.mulCall F P.acc P.acc P.acc) (.block [testCounter]))) .ne)

def powerOp (P : PowCfg) (F : Spec.Weierstrass.Mont.Modulus) : PowerOp → Prog isa
  | .save => .block (copy (2 * P.M.n) P.tmp P.acc)
  | .squares n => squareRun P F n
  | .mulBase => Mont.mulCall F P.acc P.acc P.base
  | .mulSaved => Mont.mulCall F P.acc P.acc P.tmp

def powerChain (P : PowCfg) (F : Spec.Weierstrass.Mont.Modulus) : List PowerOp → Prog isa
  | [] => .block []
  | op :: ops => .seq (powerOp P F op) (powerChain P F ops)

/-- Build `x^(2^30-1)` in the saved slot, then append the runs of bits in
`p-2`. This uses 255 squares and 18 other multiplications. -/
def p256PowerOps : List PowerOp :=
  [.save, .squares 1, .mulSaved, .squares 1, .mulBase,
   .save, .squares 3, .mulSaved, .squares 1, .mulBase,
   .save, .squares 7, .mulSaved, .squares 1, .mulBase,
   .save, .squares 15, .mulSaved, .save,
   .squares 1, .mulBase, .squares 1, .mulBase,
   .squares 32, .mulBase,
   .squares 126, .mulSaved, .squares 30, .mulSaved, .squares 30, .mulSaved,
   .squares 1, .mulBase, .squares 1, .mulBase, .squares 1, .mulBase, .squares 1, .mulBase,
   .squares 2, .mulBase]

def p256Power (P : PowCfg) (F : Spec.Weierstrass.Mont.Modulus) : Prog isa :=
  .seq (.block (copy (2 * P.M.n) P.acc P.base ++ copy (2 * P.M.n) P.tmp P.base))
    (powerChain P F p256PowerOps)

/-- Fixed field exponent for P-256, with the generic exponentiation fallback. -/
def powField (P : PowCfg) (F : Spec.Weierstrass.Mont.Modulus) (m : Nat) : Prog isa :=
  if m = p256Prime then p256Power P F else pow P F

end VG.Impl.Weierstrass.X86
