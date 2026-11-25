module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64
public import VerifiedGarbage.Spec.Secp256k1
public import VerifiedGarbage.Spec.BrainpoolP256r1

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

/-- The measured kernels large enough to share across the public loop. -/
def sharedName (c : Ecdsa.AArch64.Cfg) : Option String :=
  if c.n = 5 then some "vg_brainpoolp320r1_verify_add"
  else if c.C.p = Spec.Secp256k1.p then some "vg_secp256k1_verify_add"
  else if c.C.p = Spec.BrainpoolP256r1.p then some "vg_brainpoolp256r1_verify_add"
  else none

/-- Share the selected kernels across table setup and the joint loop. -/
def sum (c : Ecdsa.AArch64.Cfg) : Prog isa :=
  match sharedName c with
  | some name => .call name (inlineSum c)
  | none => inlineSum c

end VG.Impl.Ecdsa.Verify.AArch64.GeneralSum
