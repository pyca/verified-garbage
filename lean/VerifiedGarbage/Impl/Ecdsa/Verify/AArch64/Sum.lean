module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64

/-! General complete addition for the public joint verification loops. The
five-word curve shares this large kernel across table setup and both doublings. -/

@[expose] public section
namespace VG.Impl.Ecdsa.Verify.AArch64.GeneralSum
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

/-- General complete addition uses `a` and `3b`. -/
def slots (c : Ecdsa.AArch64.Cfg) : RcbSlots := { c.rcbSlots with b3 := c.sl EXPP }

/-- `R = U + R`, through `D`. The field operations preserve the link. -/
def inlineSum (c : Ecdsa.AArch64.Cfg) : Prog isa :=
  .seq (fprogB c.MP' (rcb (slots c) (c.pt UX UY UZ) (c.pt RX RY RZ) (c.pt DX DY DZ)))
    (.block (copy c.n (c.sl RX) (c.sl DX) ++
      (copy c.n (c.sl RY) (c.sl DY) ++ copy c.n (c.sl RZ) (c.sl DZ))))

/-- Share the five-word kernel; the other measured layouts remain inline. -/
def sum (c : Ecdsa.AArch64.Cfg) : Prog isa :=
  if c.n = 5 then .call "vg_brainpoolp320r1_verify_add" (inlineSum c) else inlineSum c

end VG.Impl.Ecdsa.Verify.AArch64.GeneralSum
