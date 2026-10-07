import VerifiedGarbage.Impl.Weierstrass.X86_64.CachedJac
import VerifiedGarbage.Impl.Weierstrass.X86_64.TCombJ

/-! Secret Jacobian addition with cached Z powers and branchless infinity handling. -/
namespace VG.Impl.Weierstrass.X86_64.CachedJac
open VG VG.X86_64 VG.Impl.Weierstrass

def infinityMasks (K : WinCfg) (p q o : Pt) : List Instr :=
  (nzMask K.M.n p.z ++ selPt K.M.n o q o) ++
  (nzMask K.M.n q.z ++ selPt K.M.n o p o)

/-- Equal nonzero inputs are excluded by the secret-window scalar bounds. -/
def maskedAdd (K : WinCfg) (p q o : Pt) (dst : Nat) : Prog isa :=
  .seq (ForwardField.programB K.M (head K.S p q dst)) <|
  .seq (ForwardField.programB K.M (jacTail K.S p q o)) <|
  .block (infinityMasks K p q o)

end VG.Impl.Weierstrass.X86_64.CachedJac
