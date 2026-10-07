import VerifiedGarbage.Impl.P256.VerifyDouble
import VerifiedGarbage.Impl.Weierstrass.CachedJac
import VerifiedGarbage.Impl.Weierstrass.JacAdd

/-! Register-forwarded field programs for public P-256 verification. -/
namespace VG.Impl.P256.VerifyArithmetic
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.P256.VerifyDouble

deriving instance DecidableEq for FOp

inductive Kind where
  | doubleRR | mixedHead | mixedTail | jacHead | jacTail | tableHead | tableTail | cachedHead
  deriving DecidableEq

def twice : Pt := ⟨VG.Impl.Ecdsa.AArch64.p256.winTbl+768,
  VG.Impl.Ecdsa.AArch64.p256.winTbl+800,VG.Impl.Ecdsa.AArch64.p256.winTbl+832⟩

def operations : Kind → List FOp
  | .doubleRR => dblJMul S R R
  | .mixedHead => VG.Impl.Weierstrass.jacMixedHead S R E
  | .mixedTail => VG.Impl.Weierstrass.jacMixedTail S R E D
  | .jacHead => VG.Impl.Weierstrass.jacHead S R E
  | .jacTail => VG.Impl.Weierstrass.jacTail S R E D
  | .tableHead => VG.Impl.Weierstrass.jacHead S R twice
  | .tableTail => VG.Impl.Weierstrass.jacTail S R twice D
  | .cachedHead => CachedJac.head S R E

def kinds : List Kind := [.doubleRR,.mixedHead,.mixedTail,.jacHead,.jacTail,.tableHead,.tableTail,.cachedHead]

def selected (m : Mod) (ops : List FOp) : Prop := m=M ∧ ops∈kinds.map operations
instance (m : Mod) (ops : List FOp) : Decidable (selected m ops) := by
  unfold selected; infer_instance

/-- Other layouts retain the generic field compiler. -/
def program (m : Mod) (ops : List FOp) : Prog isa :=
  if selected m ops then .block (Forward.optimize (fprog m ops)) else fprogB m ops

/-- In-place doubling consumes each input before overwriting its slot. -/
def double (m : Mod) (slots : RcbSlots) (p : Pt) : Prog isa :=
  program m (dblJMul slots p p)

end VG.Impl.P256.VerifyArithmetic
