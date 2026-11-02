module

public import VerifiedGarbage.Proof.Rsa.Arm.Stage.MM
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.KS
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.Taint2
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
public import VerifiedGarbage.Proof.Rsa.RecoverExp
import VerifiedGarbage.Proof.Rsa.RecoverSubtract
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Tools
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops2
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Loads

/-! # The ARMv7 key stages: the steps of the factors as pieces

`Sk`: a stage of the working space with `v` words, without Montgomery
multiplication (which the factors no longer use).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa (b2n)

/-- A stage without Montgomery multiplication. -/
abbrev Sk (P : RP) (E : State → Prop) (A : State → Nat → Nat) (L : List Nat) (AW : State → Nat → Nat)
    (LW : List Nat) (V : State → Nat → Nat) (LS : List Nat) (v N : Nat) (σ s : State) : Prop :=
  E σ ∧ KS P σ (A σ) L (AW σ) LW (V σ) LS s ∧ Ws s P.B P.Z v N

/-- `a - b` modulo `2^(32 w)`. -/
def sub32 (w a b : Nat) : Nat := (a + 2 ^ (32 * w) - b) % 2 ^ (32 * w)

theorem sub32_of {X a b w c : Nat} (hX : X < 2 ^ (32 * w)) (hb : b < 2 ^ (32 * w))
    (h : X + b = a + 2 ^ (32 * w) * c) (hc : c ≤ 1) : X = sub32 w a b ∧ c = b2n (decide (a < b)) :=
  VG.Proof.Rsa.sub32_of hX hb h hc

section
variable {P : RP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {AW : State → Nat → Nat}
  {LW : List Nat} {V : State → Nat → Nat} {LS : List Nat}

end

end VG.Proof.Rsa.Arm.Recover
