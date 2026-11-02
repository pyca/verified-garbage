module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.PowerArgs
import VerifiedGarbage.Proof.Ffdh.Arm.PowerAt
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.PowerCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
public import VerifiedGarbage.Proof.Ffdh.Arm.Power
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack

/-! Exponentiation through saved FFDH pointers retains RSA's constant-time window. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)

structure PowerAtInput (p : Inputs) (slots : List Nat) (bs es : Nat)
    (M : Nat) (bb eb : List Byte) (s : State) : Prop where
  context : Context p slots s
  ready : ArithmeticReady p.base p.len p.w s
  modulus : numAt s.mem (State.addr p.base) p.w 0 = M
  r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % M
  source : Octets p.base (p.slotValue bs) p.len bb s
  exponent : Octets p.base (p.slotValue es) p.len eb s

theorem powerArgs_input (s : State) {p : Inputs} {slots : List Nat} {bs es ec M : Nat}
    {bb eb : List Byte} (stable : stableSlots slots = true)
    (hb : bs ∈ slots) (he : es ∈ slots) (hc : ec ∈ slots) (hk : 32 ∈ slots)
    (baseLength : bb.length = p.k) (positive : 0 < eb.length) (fits : eb.length < 2 ^ 32)
    (count : p.slotValue ec = BitVec.ofNat 32 eb.length) (odd : M % 2 = 1)
    (h : PowerAtInput p slots bs es M bb eb s) :
    WP isa (.block (VG.Impl.Ffdh.Arm.Domain.powerArgs bs es ec)) s
      (PowerInput p.base (p.slotValue bs) (p.slotValue es) p.len p.w M bb eb) := by
  refine WP.mono (powerArgs_ok s bs es ec h.context stable hb he hc hk) ?_
  rintro u ⟨⟨source, length, exponent, exponentCount, mem⟩, rest⟩
  have frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem u.mem := by rw [mem]; exact Frame.refl _ _
  exact ⟨h.ready.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ready.ptr),
    by rw [mem]; exact h.modulus, odd, by rw [mem]; exact h.r2,
    h.source.after_workspace frame rest, h.exponent.after_workspace frame rest,
    by rw [baseLength]; have := p.minLength; omega,
    by rw [baseLength]; exact p.width.2.2.2.1,
    positive, fits, source, by rw [baseLength]; exact length, exponent, exponentCount.trans count⟩

theorem powerAt_ct {p : Inputs} {slots : List Nat} {bs es ec M : Nat} {bb eb1 eb2 : List Byte}
    (stable : stableSlots slots = true) (hb : bs ∈ slots) (he : es ∈ slots) (hc : ec ∈ slots) (hk : 32 ∈ slots)
    (baseLength : bb.length = p.k) (positive : 0 < eb1.length) (fits : eb1.length < 2 ^ 32)
    (count : p.slotValue ec = BitVec.ofNat 32 eb1.length) (length : eb1.length = eb2.length)
    (odd : M % 2 = 1) :
    RelCT isa (fun s t => PowerAtInput p slots bs es M bb eb1 s ∧
      PowerAtInput p slots bs es M bb eb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.powerAt bs es ec) (fun _ _ => True) := by
  have args := (powerArgs_ct bs es ec).mono
    (P' := fun (s t : State) => PowerAtInput p slots bs es M bb eb1 s ∧
      PowerAtInput p slots bs es M bb eb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have tableFit : Proof.Rsa.Mont.arrAt p.w 3 + 32 ≤ 8 * p.len := by
    have fit := p.width.2.2.1
    simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] at *
    omega
  unfold VG.Impl.Ffdh.Arm.Domain.powerAt
  exact relCT_chain args
    (fun s h => powerArgs_input s stable hb he hc hk baseLength positive fits count odd h)
    (fun s h => powerArgs_input s stable hb he hc hk baseLength (by rw [← length]; exact positive)
      (by rw [← length]; exact fits) (by rw [← length]; exact count) odd h)
    (power_ct tableFit p.width.2.2.1 positive rfl length)

end VG.Proof.Ffdh.Arm
