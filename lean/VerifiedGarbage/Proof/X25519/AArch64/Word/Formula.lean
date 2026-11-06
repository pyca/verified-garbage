module

public import VerifiedGarbage.Proof.X25519.AArch64.Word.Slots
public import VerifiedGarbage.Proof.X25519.Ladder

/-! The shared field operations implement precisely the RFC 7748 ladder formulas. -/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Word
open VG VG.Spec.X25519 VG.Proof.X25519
open VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519.AArch64

def Good (e : Env) (x1 : Fe) (st : Ladder) : Prop :=
  e 0 = x1 ∧ e 1 = st.x2 ∧ e 2 = st.z2 ∧ e 3 = st.x3 ∧ e 4 = st.z3 ∧ e 18 = a24

end VG.Proof.X25519.AArch64.Word
