module

import VerifiedGarbage.Impl.RsaKeyGen.X86.FastR2
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.State
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Impl.Rsa.X86.KeyWs

/-! # The six squarings in fast R² setup, generic over a verified multiplier -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.FastR2
open VG VG.X86 VG.Impl.Rsa.X86.Keys

theorem squares_ok (square : Prog isa) (P : State → Prop) (value : State → Nat) {m R : Nat}
    (coprime : Nat.Coprime R m)
    (step : ∀ s, P s → value s < m → WP isa square s fun t =>
      P t ∧ value t < m ∧ value t * R % m = value s * value s % m)
    (count : Nat) {s : State} {E : Nat} (S : P s) (lt : value s < m)
    (congruent : value s % m = 2 ^ E * R % m) :
    WP isa (seqs (List.replicate (count + 1) square)) s fun t =>
      P t ∧ value t < m ∧ value t % m = 2 ^ (2 ^ (count + 1) * E) * R % m := by
  induction count generalizing s E with
  | zero =>
    exact WP.mono (step s S lt) fun t ⟨T, bound, mul⟩ =>
      ⟨T, bound, VG.Proof.Bignum.mont_sq coprime congruent mul⟩
  | succ count ih =>
    change WP isa (.seq square (seqs (List.replicate (count + 1) square))) s _
    refine WP.seq (WP.mono (step s S lt) fun a ⟨A, bound, mul⟩ => ?_)
    refine WP.mono (ih A bound (VG.Proof.Bignum.mont_sq coprime congruent mul))
      fun t ⟨T, bound, V⟩ => ⟨T, bound, ?_⟩
    rw [V, show 2 ^ (count + 1 + 1) = 2 ^ (count + 1) * 2 from rfl, Nat.mul_assoc]

end VG.Proof.RsaKeyGen.X86.FastR2
