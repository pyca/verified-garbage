module

public import VerifiedGarbage.Impl.Ecdsa.AArch64

/-!
# The parts of the signing code, read from a literal

A curve's fixed-base signing code (`signComb`) is its signing code
(`Cfg.signWith`) with another comb, for a configuration that differs only in
the comb's table: its inversions, the steps between them and its last steps
are the same code. The literal of the signing code has them already, so the
literal of the fixed-base code reads them there (`pPowOf sign.lit`, …, each
stated as the literal of that part: `materialize_code` then stops at it),
rather than have the kernel build them again.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.SignParts
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64

/-- The second of a sequence. -/
def right : Prog isa → Prog isa
  | .seq _ b => b
  | c => c

/-- The first of a sequence. -/
def left : Prog isa → Prog isa
  | .seq a _ => a
  | c => c

/-- `Cfg.pPow`, of the code of `Cfg.signWith`. -/
def pPowOf (p : Prog isa) : Prog isa := left (right (right (right p)))
/-- `Cfg.middle`, of the code of `Cfg.signWith`. -/
def middleOf (p : Prog isa) : Prog isa := left (right (right (right (right p))))
/-- `Cfg.nPow`, of the code of `Cfg.signWith`. -/
def nPowOf (p : Prog isa) : Prog isa := left (right (right (right (right (right p)))))
/-- `Cfg.scalar`, of the code of `Cfg.signWith`. -/
def scalarOf (p : Prog isa) : Prog isa := right (right (right (right (right (right p)))))

theorem pPowOf_signWith (c : Cfg) (comb : Prog isa) : pPowOf (c.signWith comb) = c.pPow := rfl
theorem middleOf_signWith (c : Cfg) (comb : Prog isa) : middleOf (c.signWith comb) = c.middle := rfl
theorem nPowOf_signWith (c : Cfg) (comb : Prog isa) : nPowOf (c.signWith comb) = c.nPow := rfl
theorem scalarOf_signWith (c : Cfg) (comb : Prog isa) : scalarOf (c.signWith comb) = c.scalar := rfl

end VG.Proof.Ecdsa.AArch64.SignParts
