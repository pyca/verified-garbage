module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InverseTiming
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.OddModulus
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseBridge
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
meta import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Public
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint

/-! # The arithmetic after the small-exponent check keeps the factors secret

Its pieces before and after the CRT coefficient's inversion are checked by the taint analysis; the
inversion is `inverseFrom_trace`, from the odd modulus each run computes, which fits the prime
width. -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aDen aQi aN kOk kFlag kStatus)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr

theorem qinv_modulus_public : Public (oddModulus aPa aDen) := by
  refine of_any (hint := ?hint) ?check
  case check => taint_decide

theorem qinv_setup_public : Public (inverseSetup .prime (VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aQa)
    (VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aDen)) := by
  refine of_any (hint := ?hint) ?check
  case check => taint_decide

theorem qinv_rest_public : Public (seqs [gcdIsOne .prime, .block (andS kOk kOk kFlag),
    widen .prime (VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aQi) (.array .prime 3)]) := by
  refine of_any (hint := ?hint) ?check
  case check => taint_decide

theorem keyPart_rest_public : Public (seqs [crtPart, primeProduct aN aPa aQa, finalMask,
    .block [.mov .eax (.mem (VG.Impl.Mont.X86.sc kOk)), .store (VG.Impl.Mont.X86.sc kStatus) .eax]]) := by
  refine of_any (hint := ?hint) ?check
  case check => taint_decide

theorem keyPart_trace (B : Addr) (Z n k : Nat) (width : n = 2 * k) (positive : 0 < k) :
    RelCT isa (Both (fun s => Ws s B Z n 32 ∧ num s.mem B n aPa < 2 ^ (32 * k))) keyPart
      (VG.X86.Taint.Agree runtimeTaint) := by
  have small : k ≤ n := by omega
  have half : n / 2 = k := by omega
  have three : 3 < 2 ^ (32 * k) := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 32 ≤ 32 * k by omega)
    omega
  intro s₁ s₂ tr₁ tr₂ t₁ t₂ P E₁ E₂
  have layout := VG.Proof.RsaKeyGen.X86.Key.inverse_array_layout P.1.1.old small (a := aQa) (b := aDen)
    (by decide) (by decide) (by decide) (by decide)
  have layout' : VG.Proof.RsaKeyGen.X86.Key.InverseLayout Z (Width.prime.words n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aQa).offset n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aDen).offset n) := by
    simpa only [VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, Width.words, half] using layout
  refine (?_ : RelCT isa _ keyPart _) s₁ s₂ tr₁ tr₂ t₁ t₂ P E₁ E₂
  unfold keyPart qinvPart seqs
  refine RelCT.seq (RelCT.seq (step_trace
      (Q := FromReady B Z n 32 .prime (VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aDen)) qinv_modulus_public
      fun s ⟨h, bP⟩ => WP.mono (oddModulus_ok h (by decide) (by decide) (by decide))
        fun u ⟨hu, _, _, modulus, _⟩ => ?_)
    (RelCT.seq (inverseFrom_trace (N := 32) (by decide) (by decide) layout' qinv_setup_public)
      (public_trace qinv_rest_public))) (public_trace keyPart_rest_public)
  have bound : num u.mem B n aDen < 2 ^ (32 * k) := by
    rw [modulus]
    split
    · exact bP
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
