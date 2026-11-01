module

public import VerifiedGarbage.Proof.Bignum.Arm.CombExpState
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Proof.Rsa.FixedBaseComb
public import VerifiedGarbage.Impl.Bignum.Arm.CombExp

/-! The real masked gather/scan fragment supplies one selected comb entry. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure Kernel (base source table : BitVec 32) (len w bytes N M g x : Nat)
    (P : State → Prop) (regions : List Region) where
  arithmetic : TwoExp.Montgomery base len w P regions
  choose_ok : ∀ (s : State) (i E : Nat), i < Spec.Rsa.FixedBaseComb.rows N →
    Power base len w M g E s → P s → Controls base source table bytes N s → Counter base (i+1) s →
    WP isa VG.Impl.Bignum.Arm.CombExp.choose s fun t =>
      Power base len w M g E t ∧ P t ∧ Controls base source table bytes N t ∧ Counter base (i+1) t ∧
      numAt t.mem (State.addr base) w 1 < M ∧
      numAt t.mem (State.addr base) w 1 % M =
        g ^ (Spec.Rsa.FixedBaseComb.exponent N (VG.Proof.Rsa.FixedBaseComb.digit N x i)) * 2^(64*w) % M ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t

end VG.Proof.Bignum.Arm.CombExp
