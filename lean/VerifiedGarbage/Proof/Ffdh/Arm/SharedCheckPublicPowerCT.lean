module

public import VerifiedGarbage.Impl.Ffdh.Arm.SharedCheckPublic
public import VerifiedGarbage.Proof.Ffdh.Arm.PowerAtCT
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerCT
import VerifiedGarbage.Proof.Ffdh.Arm.PowerArgs
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowPhaseCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery

/-! Shared public-key exponentiation retains the three-bit window timing policy. -/

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

theorem sharedCheckPublicPowerAt_ct {p : Inputs} {slots : List Nat} {bs es ec M : Nat}
    {bb eb1 eb2 : List Byte} {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery p.base p.len p.w P regions) (ct : TwoExp.MontgomeryTiming K)
    (stable : stableSlots slots = true) (hb : bs ∈ slots) (he : es ∈ slots)
    (hc : ec ∈ slots) (hk : 32 ∈ slots)
    (baseLength : bb.length = p.k) (positive : 0 < eb1.length) (fit : eb1.length < 2 ^ 32)
    (count : p.slotValue ec = BitVec.ofNat 32 eb1.length) (length : eb1.length = eb2.length)
    (odd : M % 2 = 1)
    (separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr (p.slotValue es), eb1.length⟩ r) :
    RelCT isa (fun s t => (PowerAtInput p slots bs es M bb eb1 s ∧ P s) ∧
      (PowerAtInput p slots bs es M bb eb2 t ∧ P t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedCheckPublic.powerAt K.op bs es ec) (fun _ _ => True) := by
  have args (s : State) {eb : List Byte} (h : PowerAtInput p slots bs es M bb eb s ∧ P s)
      (positive : 0 < eb.length) (fit : eb.length < 2 ^ 32)
      (count : p.slotValue ec = BitVec.ofNat 32 eb.length)
      (sep : ∀ r ∈ regions, Region.Disjoint ⟨State.addr (p.slotValue es), eb.length⟩ r) :
      WP isa (.block (VG.Impl.Ffdh.Arm.Domain.powerArgs bs es ec)) s
        (KeyPower.Input p.base (p.slotValue bs) (p.slotValue es) p.len p.w M P regions bb eb) := by
    obtain ⟨tr,u,run,input⟩ := powerArgs_input s stable hb he hc hk baseLength positive fit count odd h.1
    have retained := powerArgs_ok s bs es ec h.1.context stable hb he hc hk
    obtain ⟨_,v,run',values,rest⟩ := retained
    obtain ⟨_,rfl⟩ := Exec.det run run'
    have frame : Frame [⟨State.addr p.base,8*p.len⟩] s.mem u.mem := by
      rw [values.2.2.2.2]
      exact Frame.refl _ _
    exact ⟨tr,u,run, input, K.stable frame (rest.mono (by simp [roundClobbers])) h.2, sep⟩
  unfold VG.Impl.Ffdh.Arm.SharedCheckPublic.powerAt
  exact relCT_chain ((powerArgs_ct bs es ec).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial))
    (fun s h => args s h positive fit count separate)
    (fun s h => args s h (by rw [←length]; exact positive) (by rw [←length]; exact fit)
      (by rw [←length]; exact count) (by rw [←length]; exact separate))
    (sharedPublicPower_ct K ct p.width.2.2.1 positive length separate)

end VG.Proof.Ffdh.Arm
