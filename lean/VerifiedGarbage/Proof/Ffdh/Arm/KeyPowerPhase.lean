module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpPhase
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Block

/-! # Public generator dispatch with a full-width secret exponent

The fallback is supplied with its verified arithmetic and timing behavior.
Both paths use the original imported exponent bytes without shortening.
-/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeyPower
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand)
open VG.Proof.X25519.Arm (Rest)

structure PhaseInput (base ep : BitVec 32) (len w M x : Nat) (P : State → Prop)
    (regions : List Region) (eb : List Byte) (s : State) : Prop where
  phase : ExpPhaseInput base ep len w M x eb s
  persistent : P s
  separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb.length⟩ r

end VG.Proof.Ffdh.Arm.KeyPower
