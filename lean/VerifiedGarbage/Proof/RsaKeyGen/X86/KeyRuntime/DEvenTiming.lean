module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InverseTiming
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.OddModulus
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ScalarKey
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ArrayDivision
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseBridge
meta import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Public
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint

/-! # The even-exponent path leaks only public data

Its pieces before and after the inversion are checked by the taint analysis; the inversion is
`inverseFrom_trace`, from a modulus each run makes odd. -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aE aL aDen aU aV aD kOk kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr

theorem dEven_modulus_public : Public (oddModulus aL aDen) := by
  refine of_any (hint := ?hint) ?check
  case check => taint_decide

theorem dEven_save_public : Public (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc kFlag)),
    .store (VG.Impl.Mont.X86.sc kOk) .eax]) := by
  refine of_any (hint := ?hint) ?check
  case check => taint_decide

theorem dEven_divide_public : Public (divFull aE aDen aU aV) := by
  refine of_any (hint := ?hint) ?check
  case check => taint_decide

theorem dEven_setup_public : Public (inverseSetup .modulus (VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aV) (VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aDen)) := by
  refine of_any (hint := ?hint) ?check
  case check => taint_decide

theorem dEven_rest_public :
    Public (seqs [gcdIsOne .modulus, .block (andS kOk kOk kFlag), cp aD 3]) := by
  refine of_any (hint := ?hint) ?check
  case check => taint_decide

theorem dEven_trace (B : Addr) (Z n : Nat) :
    RelCT isa (Both (fun s => Ws s B Z n 32)) dEven (VG.X86.Taint.Agree runtimeTaint) := by
  intro s₁ s₂ tr₁ tr₂ t₁ t₂ P E₁ E₂
  have layout := VG.Proof.RsaKeyGen.X86.Key.inverse_array_layout P.1.old (Nat.le_refl n)
    (by decide : aV < 32) (by decide : aDen < 32) (by decide) (by decide)
  refine (?_ : RelCT isa _ dEven _) s₁ s₂ tr₁ tr₂ t₁ t₂ P E₁ E₂
  unfold dEven seqs
  refine RelCT.seq (step_trace (Q := fun u => Ws u B Z n 32 ∧ OddAt B n aDen u) dEven_modulus_public
    fun s h => WP.mono (oddModulus_ok h (by decide) (by decide) (by decide))
      fun u ⟨hu, _, _, modulus, _⟩ => ⟨hu, oddAt_of modulus⟩) ?_
  refine RelCT.seq (step_trace (Q := fun u => Ws u B Z n 32 ∧ OddAt B n aDen u) dEven_save_public
    fun s ⟨h, M⟩ => WP.mono (saveSlot_ok h (by decide) (by decide)) fun v ⟨hv, Ov, _, _⟩ => ⟨hv, ?_⟩) ?_
  · rw [OddAt, Ov.num (by simp) (by decide) (h.fit64 (by decide))]
    exact M
  refine RelCT.seq (step_trace (Q := FromReady B Z n 32 .modulus (VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aDen)) dEven_divide_public
    fun s ⟨h, M⟩ => WP.mono (arrayDivision_ok h (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by have := M.2; omega))
      fun w ⟨hw, Ow, _, _, _⟩ => ?_) ?_
  · have same := arrayDivision_preserves_num (j := aDen) (by decide) (by decide) (by decide)
      (h.fit64 (by decide)) Ow
    refine ⟨hw, ?_, ?_⟩
    · change num w.mem B n aDen % 2 = 1
      rw [same]
      exact M.1
    · change 1 < num w.mem B n aDen
      rw [same]
      exact M.2
  exact RelCT.seq (inverseFrom_trace (N := 32) (by decide) (by decide) layout dEven_setup_public)
    (public_trace dEven_rest_public)

end VG.Proof.RsaKeyGen.X86.KeyRuntime
