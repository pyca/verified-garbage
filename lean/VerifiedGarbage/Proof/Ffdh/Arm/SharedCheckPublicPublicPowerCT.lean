module

public import VerifiedGarbage.Impl.Ffdh.Arm.SharedCheckPublic
public import VerifiedGarbage.Proof.Ffdh.Arm.PowerAtCT
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
import VerifiedGarbage.Proof.Ffdh.Arm.PublicPowerInput
import VerifiedGarbage.Proof.Ffdh.Arm.PublicScanCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerCT
import VerifiedGarbage.Proof.Ffdh.Arm.PowerArgs
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowPhaseCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT

/-! Shared subgroup exponentiation trims only the public exponent prefix. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

private theorem sharedPublicPower_ct {base src ep : BitVec 32} {len w M : Nat}
    {P : State → Prop} {regions : List Region} {bb eb1 eb2 : List Byte}
    (K : TwoExp.Montgomery base len w P regions) (ct : TwoExp.MontgomeryTiming K)
    (fits : Proof.Rsa.Mont.arrAt w 16 ≤ 8 * len) (positive : 0 < eb1.length)
    (length : eb1.length = eb2.length)
    (separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb1.length⟩ r) :
    RelCT isa (fun s t => KeyPower.Input base src ep len w M P regions bb eb1 s ∧
      KeyPower.Input base src ep len w M P regions bb eb2 t ∧ s.sp = t.sp)
      (.seq VG.Impl.Ffdh.Arm.powerImport (VG.Impl.Bignum.Arm.SharedWindow.phase K.op))
      (fun _ _ => True) := by
  exact relCT_chain
    ((KeyPower.import_ct length).mono
      (fun _ _ h => ⟨h.1.power, h.2.1.power, h.2.2⟩) (fun _ _ h => h))
    (fun s h => WP.mono (KeyPower.import_ok K s h) fun _ k => ⟨k.1.phase, k.1.persistent⟩)
    (fun s h => WP.mono (KeyPower.import_ok K s h) fun _ k => ⟨k.1.phase, k.1.persistent⟩)
    (SharedWindow.phase_ct K ct fits positive length separate)

theorem sharedCheckPublicPublicPower_ct {p : Inputs} {slots : List Nat} {bs es ec M : Nat}
    {bb eb : List Byte} {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery p.base p.len p.w P regions) (ct : TwoExp.MontgomeryTiming K)
    (stable : stableSlots slots = true) (hb : bs ∈ slots) (he : es ∈ slots)
    (hc : ec ∈ slots) (hk : 32 ∈ slots)
    (baseLength : bb.length = p.k) (positive : 0 < eb.length) (fit : eb.length < 2^32)
    (count : p.slotValue ec = BitVec.ofNat 32 eb.length) (odd : M % 2 = 1)
    (separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr (p.slotValue es),eb.length⟩ r) :
    RelCT isa (fun s t => (PowerAtInput p slots bs es M bb eb s ∧ P s) ∧
      (PowerAtInput p slots bs es M bb eb t ∧ P t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedCheckPublic.publicPowerAt K.op bs es ec) (fun _ _ => True) := by
  intro s0 t0 tr1 tr2 u v initial run1 run2
  have leadLt := VG.Proof.Ffdh.lead_lt (bs := eb) (by intro empty; rw [empty] at positive; simp at positive)
  have trimmedPositive : 0 < (eb.drop (VG.Proof.Ffdh.lead eb)).length := by
    simp only [List.length_drop]; omega
  have args (s : State) (h : PowerAtInput p slots bs es M bb eb s ∧ P s) :
      WP isa (.block (VG.Impl.Ffdh.Arm.Domain.powerArgs bs es ec)) s
        (KeyPower.Input p.base (p.slotValue bs) (p.slotValue es) p.len p.w M P regions bb eb) := by
    obtain ⟨tr,u,run,input⟩ := powerArgs_input s stable hb he hc hk baseLength positive fit count odd h.1
    obtain ⟨_,v,run',values,rest⟩ := powerArgs_ok s bs es ec h.1.context stable hb he hc hk
    obtain ⟨_,rfl⟩ := Exec.det run run'
    have frame : Frame [⟨State.addr p.base,8*p.len⟩] s.mem u.mem := by
      rw [values.2.2.2.2]; exact Frame.refl _ _
    exact ⟨tr,u,run,input,K.stable frame (rest.mono (by simp [roundClobbers])) h.2,separate⟩
  have trim (s : State)
      (h : KeyPower.Input p.base (p.slotValue bs) (p.slotValue es) p.len p.w M P regions bb eb s) :
      WP isa VG.Impl.Ffdh.Arm.PublicScan.code s
        (KeyPower.Input p.base (p.slotValue bs)
          (p.slotValue es+BitVec.ofNat 32 (VG.Proof.Ffdh.lead eb)) p.len p.w M P regions bb
            (eb.drop (VG.Proof.Ffdh.lead eb))) := by
    refine WP.mono (PublicScan.input_ok s h.power) ?_
    rintro t ⟨input,mem,rest⟩
    have frame : Frame [⟨State.addr p.base,8*p.len⟩] s.mem t.mem := by
      rw [mem]; exact Frame.refl _ _
    exact ⟨input,K.stable frame (rest.mono (by simp [roundClobbers])) h.persistent,
      fun r hr => PublicScan.suffix_separate h.power.exponentBytes positive (h.separate r hr)⟩
  have scan := (PublicScan.code_ct positive fit).mono
    (P' := fun (s t : State) => KeyPower.Input p.base (p.slotValue bs) (p.slotValue es) p.len p.w M P regions bb eb s ∧
      KeyPower.Input p.base (p.slotValue bs) (p.slotValue es) p.len p.w M P regions bb eb t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.power.exponentBytes,h.1.power.exponent,h.1.power.exponentCount⟩,
      ⟨h.2.1.power.exponentBytes,h.2.1.power.exponent,h.2.1.power.exponentCount⟩,h.2.2⟩)
    (fun _ _ h => h)
  have trimmedSeparate : ∀ r ∈ regions, Region.Disjoint
      ⟨State.addr (p.slotValue es+BitVec.ofNat 32 (VG.Proof.Ffdh.lead eb)),
        (eb.drop (VG.Proof.Ffdh.lead eb)).length⟩ r := by
    intro r hr
    exact PublicScan.suffix_separate initial.1.1.exponent positive (separate r hr)
  have tail := relCT_chain scan trim trim
    (sharedPublicPower_ct K ct p.width.2.2.1 trimmedPositive rfl trimmedSeparate)
  unfold VG.Impl.Ffdh.Arm.SharedCheckPublic.publicPowerAt at run1 run2
  exact (relCT_chain ((powerArgs_ct bs es ec).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial))
    (fun s h => args s h) (fun s h => args s h) tail) s0 t0 tr1 tr2 u v initial run1 run2

end VG.Proof.Ffdh.Arm
