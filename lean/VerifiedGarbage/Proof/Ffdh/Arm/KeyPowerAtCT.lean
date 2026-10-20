module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerPhase
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerAt
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT

/-! # Key-generation power pointer setup and shared phase timing -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeyPower
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (arrAt)

theorem powerAt_ct {p : Inputs} {slots : List Nat} {bs es ec M : Nat}
    {P : State → Prop} {regions : List Region} {bb eb1 eb2 : List Byte}
    (A : TwoExp.Montgomery p.base p.len p.w P regions) (ct : TwoExp.MontgomeryTiming A)
    (fallback : Fallback p.base p.len p.w P regions)
    (stable : stableSlots slots = true) (hb : bs ∈ slots) (he : es ∈ slots) (hc : ec ∈ slots) (hk : 32 ∈ slots)
    (baseLength : bb.length = p.k) (positive : 0 < eb1.length) (fits : eb1.length < 2 ^ 32)
    (count : p.slotValue ec = BitVec.ofNat 32 eb1.length) (length : eb1.length = eb2.length)
    (odd : M % 2 = 1) :
    RelCT isa (fun s t => ArgsInput p slots bs es M P regions bb eb1 s ∧
      ArgsInput p slots bs es M P regions bb eb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.KeyPower.powerAt A.phase fallback.code bs es ec) (fun _ _ => True) := by
  have tableFit : arrAt p.w 3 + 32 ≤ 8 * p.len := by
    have f := p.width.2.2.1
    simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at *
    omega
  have positiveW : 0 < 2 * p.w := by have := p.width.1; omega
  unfold VG.Impl.Ffdh.Arm.KeyPower.powerAt
  exact relCT_chain
    ((powerArgs_ct bs es ec).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial))
    (fun s h => WP.mono (args_input s A stable hb he hc hk baseLength positive fits count odd h) fun _ k => k.1)
    (fun s h => WP.mono (args_input s A stable hb he hc hk baseLength
      (by rw [← length]; exact positive) (by rw [← length]; exact fits)
      (by rw [← length]; exact count) odd h) fun _ k => k.1)
    (power_ct A ct fallback tableFit positiveW positive length)

end VG.Proof.Ffdh.Arm.KeyPower
