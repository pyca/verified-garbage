import VerifiedGarbage.Impl.Ecdsa.P256.AArch64
import VerifiedGarbage.Impl.Weierstrass.AArch64.Forward

namespace VG.Impl.P256.VerifyDouble
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64

deriving instance DecidableEq for VG.Impl.Mont.Mod, RcbSlots, Pt

def M := p256.MP'
def S := p256.rcbSlots
def R := p256.pt RX RY RZ
def D := p256.pt DX DY DZ
def E := p256.pt TX TY TZ

/-- Restrict forwarding to the three measured verification layouts. -/
def selected (m : Mod) (slots : RcbSlots) (p o : Pt) : Prop :=
  m=M ∧ slots=S ∧ ((p=R ∧ o=D) ∨ (p=D ∧ o=R) ∨ (p=E ∧ o=D))

instance (m : Mod) (slots : RcbSlots) (p o : Pt) : Decidable (selected m slots p o) := by
  unfold selected; infer_instance

def double (m : Mod) (slots : RcbSlots) (p o : Pt) : Prog isa :=
  if selected m slots p o then Forward.double m slots p o
  else fprogB m (dblJMul slots p o)

end VG.Impl.P256.VerifyDouble
