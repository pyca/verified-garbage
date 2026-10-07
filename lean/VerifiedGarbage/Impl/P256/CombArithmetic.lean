import VerifiedGarbage.Impl.P256.VerifyArithmetic
import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombJ

/-! Forwarded field schedules for the secret P-256 Booth comb. -/
namespace VG.Impl.P256.CombArithmetic
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

abbrev K := VG.Impl.Ecdsa.AArch64.p256.combCfg

inductive Kind where
  | mixed | out
  deriving DecidableEq

def operations : Kind → List FOp
  | .mixed => maddJ K.S K.A K.E K.D
  | .out => K.outOps

def kinds : List Kind := [.mixed,.out]
def selected (M : Mod) (ops : List FOp) : Prop := M=K.M ∧ ops∈kinds.map operations
instance (M : Mod) (ops : List FOp) : Decidable (selected M ops) := by
  unfold selected; infer_instance

def program (M : Mod) (ops : List FOp) : Prog isa :=
  if selected M ops then .block (Forward.optimize (fprog M ops)) else fprogB M ops

end VG.Impl.P256.CombArithmetic
