module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.ForwardField

/-! Precompute Z² and Z³ once for each public odd-multiple table entry. -/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64.Naf
open VG VG.X86_64 VG.Impl.Mont

def cachePairOps (n ptbl tbl i : Nat) : List FOp :=
  [.mul (tbl+16*n*i) (ptbl+24*n*i+16*n) (ptbl+24*n*i+16*n),
   .mul (tbl+16*n*i+8*n) (tbl+16*n*i) (ptbl+24*n*i+16*n)]

def cachePair (M : Mod) (ptbl tbl i : Nat) : Prog isa :=
  if M.adx ∧ M.n = 4 then ForwardField.program M [] (cachePairOps M.n ptbl tbl i)
  else fprogB M (cachePairOps M.n ptbl tbl i)

/-- Unroll the fixed number of entries; no secret-dependent loop or address. -/
def cacheTable (M : Mod) (ptbl tbl : Nat) : Nat → Prog isa
  | 0 => .block []
  | k+1 => .seq (cacheTable M ptbl tbl k) (cachePair M ptbl tbl k)

end VG.Impl.Weierstrass.X86_64.Naf
