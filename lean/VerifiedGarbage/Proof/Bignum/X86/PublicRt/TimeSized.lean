module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeExp
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Seed
meta import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeExp
public import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Omega

/-! # The trace of the exponentiation of public RSA at a run-time width

What the exponentiation needs of a run and leaves (`ExpIn`, `ExpOut`); runs
from the same exponent leak the same traces (`seed_relCT`,
`exponentiate_relCT`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

section
variable {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- What the exponentiation needs of a run: `Env`, the arguments apart, `esp`, one and `R² mod M` below `M`,
and the exponent `k` at 128. -/
def ExpIn (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (M k : Nat) (s : State) : Prop :=
  Env base bytes len args M s ∧ ArgsOk s ∧ s.gpr .esp = sp ∧
    val32 s.mem base (numAt len 3) (nw len) < M ∧ val32 s.mem base (numAt len 4) (nw len) < M ∧
    val32 s.mem base 128 2 = k

/-- After the exponentiation. -/
def ExpOut (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (s : State) : Prop :=
  ∃ M, Env base bytes len args M s ∧ ArgsOk s ∧ s.gpr .esp = sp

/-- Seeding branches only on the public exponent; copying reads no secret addresses. -/
theorem seed_relCT (hbytes : bytes = (args 9).toNat * 8) (sp : BitVec 32) (k : Nat) :
    RelCT isa (Both fun s => ∃ M, St base bytes len args sp M k s) seed
      (Both fun s => ∃ M, St base bytes len args sp M (k - k % 2) s) := by
  apply relCT_both
  · unfold seed
    refine VG.RelCT.seq (taint_both (F := fun s => (∃ M, St base bytes len args sp M k s) ∧
        s.zf = some (decide (k % 2 = 0))) (fun _ _ ⟨_, S₁⟩ ⟨_, S₂⟩ => S₁.agree S₂) (.block [])
      (by taint_decide) fun _ ⟨M, S⟩ => WP.mono (bit_st sp S) fun _ ⟨h, z⟩ => ⟨⟨M, h⟩, z⟩) ?_
    refine VG.RelCT.ite (M := isa) (c := .e) (fun _ _ h => h.1.2.trans h.2.2.symm) ?_ ?_
    · exact ((mul_relCT hbytes sp (o := 2) (a := 4) (b := 3) (by decide) (by decide) (by decide) (by decide)
        (by taint_decide)).mono (by
          rintro s t ⟨⟨⟨⟨M₁, S₁⟩, _⟩, ⟨⟨M₂, S₂⟩, _⟩⟩, _⟩
          exact ⟨S₁.2.2.1, S₂.2.2.1, ⟨⟨M₁, S₁.1, S₁.2.2.2.2.1⟩, S₁.2.1⟩,
            ⟨⟨M₂, S₂.1, S₂.2.2.2.2.1⟩, S₂.2.1⟩⟩) fun _ _ h => h)
    · exact RelCT.taint (A := taint) τA (by
        rintro s t ⟨⟨⟨⟨_, S₁⟩, _⟩, ⟨⟨_, S₂⟩, _⟩⟩, _⟩
        exact S₁.agree S₂) (hc := VG.Taint.hintOf taint τA (.seq seedCopy (.block seedConsume)))
        (by taint_decide)
  · rintro s ⟨M, E, A, sp₀, X, O, W⟩
    exact WP.mono (seed_ok E hbytes X O) fun t ⟨Et, _, K, _, V, Wt, _⟩ =>
      ⟨M, Et, A.keep K (by decide), (K.1 _ (by decide)).trans sp₀,
        by rw [V 1 (by decide) (by decide)]; exact X,
        by rw [V 3 (by decide) (by decide)]; exact O, by rw [Wt, W]⟩

/-- Runs from the same exponent `k` leak the same traces. -/
theorem exponentiate_relCT (hbytes : bytes = (args 9).toNat * 8) (sp : BitVec 32) (k : Nat) :
    RelCT isa (Both fun s => ∃ M, ExpIn base bytes len args sp M k s) exponentiate
      (Both (ExpOut base bytes len args sp)) := by
  unfold exponentiate
  refine VG.RelCT.seq (relCT_both (F := fun s => ∃ M, St base bytes len args sp M k s)
    ((mul_relCT hbytes sp (o := 1) (a := 1) (b := 4) (by decide) (by decide) (by decide) (by decide)
      (by taint_decide)).mono (fun _ _ ⟨⟨_, X₁⟩, ⟨_, X₂⟩⟩ =>
        ⟨X₁.2.2.1, X₂.2.2.1, ⟨⟨_, X₁.1, X₁.2.2.2.2.1⟩, X₁.2.1⟩, ⟨⟨_, X₂.1, X₂.2.2.2.2.1⟩, X₂.2.1⟩⟩) fun _ _ h => h)
    fun _ ⟨M, E, A, sp₀, O, T, W⟩ => WP.mono (mulKeep_ok E A hbytes (o := 1) (a := 1) (b := 4) (by decide)
      (by decide) (by decide) (by decide) T) fun _ ⟨Eu, Au, K, L, V, Wu⟩ => ⟨M, Eu, Au, (K.1 _ (by decide)).trans sp₀,
        L, by rw [V 3 (by decide) (by decide)]; exact O, Wu.trans W⟩) ?_
  refine VG.RelCT.seq (seed_relCT hbytes sp k) ?_
  refine VG.RelCT.seq (sparseLoop_relCT sp hbytes (k - k % 2)) ?_
  exact relCT_both ((mul_relCT hbytes sp (o := 2) (a := 2) (b := 3) (by decide) (by decide) (by decide) (by decide)
      (by taint_decide)).mono (fun _ _ ⟨⟨_, S₁⟩, ⟨_, S₂⟩⟩ =>
        ⟨S₁.2.2.1, S₂.2.2.1, ⟨⟨_, S₁.1, S₁.2.2.2.2.1⟩, S₁.2.1⟩, ⟨⟨_, S₂.1, S₂.2.2.2.2.1⟩, S₂.2.1⟩⟩) fun _ _ h => h)
    fun _ ⟨M, E, A, sp₀, _, O, _⟩ => WP.mono (mulKeep_ok E A hbytes (o := 2) (a := 2) (b := 3) (by decide)
      (by decide) (by decide) (by decide) O) fun _ ⟨Eu, Au, K, _⟩ => ⟨M, Eu, Au, (K.1 _ (by decide)).trans sp₀⟩

end

end VG.Proof.Bignum.X86.PublicRt
