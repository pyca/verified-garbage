module

public import VerifiedGarbage.Proof.Ffdh.Arm.PowerAtCT
import VerifiedGarbage.Impl.Ffdh.Arm.PublicScan
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.PublicPowerInput
import VerifiedGarbage.Proof.Ffdh.Arm.PublicScanCT
import VerifiedGarbage.Proof.Ffdh.Arm.PowerCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Ffdh.Arm.PowerArgs

/-! Public subgroup exponentiation skips only identical public zero prefixes. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (numAt)

theorem publicPowerAt_ct {p : Inputs} {slots : List Nat} {bs es ec M : Nat} {bb eb : List Byte}
    (stable : stableSlots slots = true) (hb : bs ∈ slots) (he : es ∈ slots) (hc : ec ∈ slots) (hk : 32 ∈ slots)
    (baseLength : bb.length = p.k) (positive : 0 < eb.length) (fits : eb.length < 2 ^ 32)
    (count : p.slotValue ec = BitVec.ofNat 32 eb.length) (odd : M % 2 = 1) :
    RelCT isa (fun s t => PowerAtInput p slots bs es M bb eb s ∧
      PowerAtInput p slots bs es M bb eb t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.publicPowerAt bs es ec) (fun _ _ => True) := by
  have leadLt := VG.Proof.Ffdh.lead_lt (bs := eb) (by intro empty; rw [empty] at positive; simp at positive)
  have trimmedPositive : 0 < (eb.drop (VG.Proof.Ffdh.lead eb)).length := by
    simp only [List.length_drop]; omega
  have tableFit : Spec.Rsa.Mont.arrAt p.w 3 + 32 ≤ 8*p.len := by
    have fit := p.width.2.2.1
    simp only [Spec.Rsa.Mont.arrAt,Spec.Rsa.Mont.hdrBytes] at *
    omega
  have scan := (PublicScan.code_ct positive fits).mono
    (P' := fun (s t : State) => PowerInput p.base (p.slotValue bs) (p.slotValue es) p.len p.w M bb eb s ∧
      PowerInput p.base (p.slotValue bs) (p.slotValue es) p.len p.w M bb eb t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.exponentBytes,h.1.exponent,h.1.exponentCount⟩,
      ⟨h.2.1.exponentBytes,h.2.1.exponent,h.2.1.exponentCount⟩,h.2.2⟩) (fun _ _ h => h)
  have tail := relCT_chain scan
    (fun s h => WP.mono (PublicScan.input_ok s h) fun _ k => k.1)
    (fun s h => WP.mono (PublicScan.input_ok s h) fun _ k => k.1)
    (power_ct tableFit p.width.2.2.1 trimmedPositive rfl rfl)
  unfold VG.Impl.Ffdh.Arm.Domain.publicPowerAt
  exact relCT_chain
    ((powerArgs_ct bs es ec).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial))
    (fun s h => powerArgs_input s stable hb he hc hk baseLength positive fits count odd h)
    (fun s h => powerArgs_input s stable hb he hc hk baseLength positive fits count odd h) tail

end VG.Proof.Ffdh.Arm
