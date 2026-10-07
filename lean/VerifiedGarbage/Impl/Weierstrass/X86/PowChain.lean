import VerifiedGarbage.Impl.Weierstrass.X86

/-! # Fixed addition chains using the existing exponentiation slots -/
namespace VG.Impl.Weierstrass.X86
open VG.X86 VG.Impl.Mont.X86 VG.Impl.Weierstrass

inductive PowerOp where
  | save
  | squares (n : Nat)
  | mulBase
  | mulSaved
  deriving Repr

/-- Repeat squaring with a public counter, retaining the saved power. -/
def squareRun (P : PowCfg) (wk : Nat) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (.block [.mov .esi (.imm (BitVec.ofNat 32 (n + 1)))])
      (.loop (.seq (.block [decCounter])
        (.seq (VG.Impl.Mont.X86.mul P.M wk P.acc P.acc P.acc) (.block [testCounter]))) .ne)

def powerOp (P : PowCfg) (wk : Nat) : PowerOp → Prog isa
  | .save => .block (copy (2 * P.M.n) P.tmp P.acc)
  | .squares n => squareRun P wk n
  | .mulBase => VG.Impl.Mont.X86.mul P.M wk P.acc P.acc P.base
  | .mulSaved => VG.Impl.Mont.X86.mul P.M wk P.acc P.acc P.tmp

def powerChain (P : PowCfg) (wk : Nat) : List PowerOp → Prog isa
  | [] => .block []
  | op :: ops => .seq (powerOp P wk op) (powerChain P wk ops)

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

def p256Power (P : PowCfg) (wk : Nat) : Prog isa :=
  .seq (.block (copy (2 * P.M.n) P.acc P.base ++ copy (2 * P.M.n) P.tmp P.base))
    (powerChain P wk p256PowerOps)

/-- Fixed field exponent for P-256, with the generic exponentiation fallback. -/
def powField (P : PowCfg) (wk m : Nat) : Prog isa :=
  if m = p256Prime then p256Power P wk else pow P wk

end VG.Impl.Weierstrass.X86
