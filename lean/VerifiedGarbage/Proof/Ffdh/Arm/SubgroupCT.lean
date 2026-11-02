module

public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain

import VerifiedGarbage.Proof.Ffdh.Arm.PublicPowerAt
import VerifiedGarbage.Proof.Ffdh.Arm.Subgroup
import VerifiedGarbage.Proof.Ffdh.Arm.ValueChecksCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Ffdh.Arm.PowerAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.PublicPowerInput
import VerifiedGarbage.Proof.Ffdh.Arm.PublicScanCT
import VerifiedGarbage.Proof.Ffdh.Arm.PowerCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
/-! Subgroup checks have a trace determined by the domain width and pointers. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/PublicPowerAtCT.lean`, which only this module imported.
section

/-! Public subgroup exponentiation skips only identical public zero prefixes. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)

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
  have tableFit : Proof.Rsa.Mont.arrAt p.w 3 + 32 ≤ 8*p.len := by
    have fit := p.width.2.2.1
    simp only [Proof.Rsa.Mont.arrAt,Proof.Rsa.Mont.hdrBytes] at *
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
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (Operand)

structure SubgroupInput (p : Inputs) (slots : List Nat) (slot : Nat) (bb : List Byte) (s : State) : Prop where
  context : Context p slots s
  ready : ArithmeticReady p.base p.len p.w s
  modulus : Proof.Rsa.Mont.numAt s.mem (State.addr p.base) p.w 0 = p.P
  r2 : Proof.Rsa.Mont.numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P
  source : Octets p.base (p.slotValue slot) p.len bb s

theorem SubgroupInput.after_workspace {p : Inputs} {slots : List Nat} {slot : Nat} {bb : List Byte}
    {s t : State} {rs : List Reg} (h : SubgroupInput p slots slot bb s)
    (stable : stableSlots slots = true) (frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem)
    (rest : VG.Proof.X25519.Arm.Rest rs s t) (ready : ArithmeticReady p.base p.len p.w t)
    (modulus : Proof.Rsa.Mont.numAt t.mem (State.addr p.base) p.w 0 = p.P)
    (r2 : Proof.Rsa.Mont.numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P) :
    SubgroupInput p slots slot bb t :=
  ⟨h.context.after_workspace frame rest ready.ptr (fun d hd => (stableSlots_at (d := d) stable hd).1),
    ready, modulus, r2, h.source.after_workspace frame rest⟩

theorem SubgroupInput.after_mem {p : Inputs} {slots : List Nat} {slot : Nat} {bb : List Byte}
    {s t : State} {rs : List Reg} (h : SubgroupInput p slots slot bb s)
    (stable : stableSlots slots = true) (mem : t.mem = s.mem) (rest : VG.Proof.X25519.Arm.Rest rs s t)
    (ptr : t.gpr .r0 = p.base) : SubgroupInput p slots slot bb t := by
  have frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact ⟨h.context.after_workspace frame rest ptr (fun d hd => (stableSlots_at (d := d) stable hd).1),
    h.ready.of_mem mem rest ptr, by rw [mem]; exact h.modulus,
    by rw [mem]; exact h.r2, h.source.after_workspace frame rest⟩

theorem subgroup_ct {p : Inputs} {slots : List Nat} {slot : Nat} {bb : List Byte}
    (stable : stableSlots slots = true) (hb : slot ∈ slots) (h60 : 60 ∈ slots) (h32 : 32 ∈ slots)
    (hasQ : p.hasQ = true) (baseLength : bb.length = p.k) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => SubgroupInput p slots slot bb s ∧ SubgroupInput p slots slot bb t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.subgroup slot) (fun _ _ => True) := by
  have positive : 0 < ((p.dom.drop (2 * p.k)).take p.k).length := by
    rw [p.qLength hasQ]; have := p.minLength; omega
  have fits : ((p.dom.drop (2 * p.k)).take p.k).length < 2 ^ 32 := by
    rw [p.qLength hasQ]; have := p.maxLength; omega
  have count : p.slotValue 32 = BitVec.ofNat 32 ((p.dom.drop (2 * p.k)).take p.k).length := by
    change BitVec.ofNat 32 p.k = _; rw [p.qLength hasQ]
  have powers := (publicPowerAt_ct (p := p) (bs := slot) (es := 60) (ec := 32)
    stable hb h60 h32 h32 baseLength positive fits count odd).mono
    (P' := fun (s t : State) => SubgroupInput p slots slot bb s ∧ SubgroupInput p slots slot bb t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready, h.1.modulus, h.1.r2, h.1.source, h.1.context.qBytes hasQ⟩,
      ⟨h.2.1.context, h.2.1.ready, h.2.1.modulus, h.2.1.r2, h.2.1.source, h.2.1.context.qBytes hasQ⟩, h.2.2⟩)
    (fun _ _ h => h)
  have wp (s : State) (h : SubgroupInput p slots slot bb s) :=
    WP.mono (publicPowerAt_ok s slot 60 32 h.context stable hb h60 h32 h32 h.ready h.modulus odd h.r2
      h.source baseLength (h.context.qBytes hasQ) positive fits count) fun _ j => j.2.1
  unfold VG.Impl.Ffdh.Arm.Domain.subgroup
  exact relCT_chain powers wp wp (isOne_ct (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 6))

end VG.Proof.Ffdh.Arm
