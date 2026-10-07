import VerifiedGarbage.Impl.Weierstrass.X86_64.ForwardField

/-! Precompute Z² and Z³ once for each public odd-multiple table entry. -/
namespace VG.Impl.Weierstrass.X86_64.Naf
open VG VG.X86_64 VG.Impl.Mont

def cachePairOps (ptbl tbl i : Nat) : List FOp :=
  [.mul (tbl+64*i) (ptbl+96*i+64) (ptbl+96*i+64),
   .mul (tbl+64*i+32) (tbl+64*i) (ptbl+96*i+64)]

def cachePair (M : Mod) (ptbl tbl i : Nat) : Prog isa :=
  if M.adx then ForwardField.program M [] (cachePairOps ptbl tbl i)
  else fprogB M (cachePairOps ptbl tbl i)

/-- Unroll the fixed number of entries; no secret-dependent loop or address. -/
def cacheTable (M : Mod) (ptbl tbl : Nat) : Nat → Prog isa
  | 0 => .block []
  | k+1 => .seq (cacheTable M ptbl tbl k) (cachePair M ptbl tbl k)

end VG.Impl.Weierstrass.X86_64.Naf
