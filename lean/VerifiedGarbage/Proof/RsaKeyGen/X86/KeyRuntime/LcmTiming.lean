module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InverseTiming
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Twos
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.OddSecond
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.OddModulus
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyHalveStep
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseBridge
import VerifiedGarbage.Proof.RsaKeyGen.HalveBounds
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
meta import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Public
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint

/-! # The fixed LCM schedule keeps the factors secret

Its pieces before and after the prime-width gcd's inversion are checked by the taint analysis;
the inversion is `inverseFrom_trace`, from the odd modulus each run computes, which fits the
prime width. -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aU aV aDen aOne aPm aQm aPhi aL kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr

theorem lcm_twos_public : Public twos := by
  refine of_any (hint := ?hint) ?check
  case check => taint_decide

theorem lcm_second_public : Public oddSecond := by
  refine of_any (hint := ?hint) ?check
  case check => taint_decide

theorem lcm_modulus_public : Public (oddModulus aV aDen) := by
  refine of_any (hint := ?hint) ?check
  case check => taint_decide

theorem lcm_setup_public : Public (inverseSetup .prime (VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aU)
    (VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aDen)) := by
  refine of_any (hint := ?hint) ?check
  case check => taint_decide

theorem lcm_gcdRest_public : Public (seqs [widen .prime (VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aDen)
    (.array .prime 1), sel aDen aOne aDen kFlag]) := by
  refine of_any (hint := ?hint) ?check
  case check => taint_decide

theorem lcm_divide_public : Public (divFull aPhi aDen aL aT1) := by
  refine of_any (hint := ?hint) ?check
  case check => taint_decide

/-- The LCM's state: the factors' predecessors, at the prime width, and their product. -/
def LcmStart (B : Addr) (Z n k : Nat) (s : State) : Prop :=
  Ws s B Z n 32 ∧ num s.mem B n aPm < 2 ^ (32 * k) ∧ num s.mem B n aQm < 2 ^ (32 * k) ∧
    num s.mem B n aPhi = num s.mem B n aPm * num s.mem B n aQm

theorem lcm_trace (B : Addr) (Z n k : Nat) (width : n = 2 * k) (positive : 0 < k) :
    RelCT isa (Both (LcmStart B Z n k)) lcmPart (VG.X86.Taint.Agree runtimeTaint) := by
  have small : k ≤ n := by omega
  have half : n / 2 = k := by omega
  have three : 3 < 2 ^ (32 * k) := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 32 ≤ 32 * k by omega)
    omega
  intro s₁ s₂ tr₁ tr₂ t₁ t₂ P E₁ E₂
  have layout := VG.Proof.RsaKeyGen.X86.Key.inverse_array_layout P.1.1.old small (a := aU) (b := aDen)
    (by decide) (by decide) (by decide) (by decide)
  have layout' : VG.Proof.RsaKeyGen.X86.Key.InverseLayout Z (Width.prime.words n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aU).offset n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aDen).offset n) := by
    simpa only [VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, Width.words, half] using layout
  refine (?_ : RelCT isa _ lcmPart _) s₁ s₂ tr₁ tr₂ t₁ t₂ P E₁ E₂
  unfold lcmPart gcdPart gcdFrom seqs
  refine RelCT.seq (step_trace (Q := fun u => Ws u B Z n 32 ∧ num u.mem B n aU < 2 ^ (32 * k) ∧
      num u.mem B n aV < 2 ^ (32 * k)) lcm_twos_public
    fun s ⟨h, bP, bQ, product⟩ => WP.mono (twos_ok h) fun u ⟨hu, _, triple, _⟩ => ?_) ?_
  · have phi : num s.mem B n aPhi < 2 ^ (32 * n) := val32_lt _ _ _ _
    have bounds := VG.Proof.RsaKeyGen.halveIter_bounds (32 * n) (st := (num s.mem B n aPm,
      num s.mem B n aQm, num s.mem B n aPhi)) ⟨bP, bQ, phi⟩
    rw [← triple] at bounds
    exact ⟨hu, bounds.1, bounds.2.1⟩
  refine RelCT.seq (RelCT.seq (step_trace (Q := fun u => Ws u B Z n 32 ∧ num u.mem B n aV < 2 ^ (32 * k))
      lcm_second_public fun s ⟨h, bU, bV⟩ => WP.mono (oddSecond_ok h) fun u ⟨hu, _, _, V, _⟩ => ?_) ?_)
    (public_trace lcm_divide_public)
  · refine ⟨hu, ?_⟩
    rw [V]
    split
    · exact bU
    · exact bV
  refine RelCT.seq (step_trace (Q := FromReady B Z n 32 .prime (VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aDen))
      lcm_modulus_public fun s ⟨h, bV⟩ =>
    WP.mono (oddModulus_ok h (by decide) (by decide) (by decide)) fun u ⟨hu, _, _, modulus, _⟩ => ?_)
    (RelCT.seq (inverseFrom_trace (N := 32) (by decide) (by decide) layout' lcm_setup_public)
      (public_trace lcm_gcdRest_public))
  have bound : num u.mem B n aDen < 2 ^ (32 * k) := by
    rw [modulus]
    split
    · exact bV
    · exact three
  have low : val32 u.mem B (arr n aDen) k = num u.mem B n aDen :=
    VG.Proof.RsaKeyGen.WordBounds32.low_eq small bound
  have M := oddAt_of modulus
  refine ⟨hu, ?_, ?_⟩
  · change val32 u.mem B (arr n aDen) (n / 2) % 2 = 1
    rw [half, low]
    exact M.1
  · change 1 < val32 u.mem B (arr n aDen) (n / 2)
    rw [half, low]
    exact M.2

end VG.Proof.RsaKeyGen.X86.KeyRuntime
