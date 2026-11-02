module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPower
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyCallMemory
public import VerifiedGarbage.Proof.Ffdh.Arm.PowerAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.PowerArgs
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Block

/-! # Shared arithmetic power through saved key-generation pointers -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeyPower
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure ArgsInput (p : Inputs) (slots : List Nat) (bs es M : Nat) (P : State → Prop)
    (regions : List Region) (bb eb : List Byte) (s : State) : Prop where
  power : PowerAtInput p slots bs es M bb eb s
  persistent : P s
  separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr (p.slotValue es), eb.length⟩ r

theorem args_input (s : State) {p : Inputs} {slots : List Nat} {bs es ec M : Nat}
    {P : State → Prop} {regions : List Region} {bb eb : List Byte}
    (A : TwoExp.Montgomery p.base p.len p.w P regions)
    (stable : stableSlots slots = true) (hb : bs ∈ slots) (he : es ∈ slots) (hc : ec ∈ slots) (hk : 32 ∈ slots)
    (baseLength : bb.length = p.k) (positive : 0 < eb.length) (fits : eb.length < 2 ^ 32)
    (count : p.slotValue ec = BitVec.ofNat 32 eb.length) (odd : M % 2 = 1)
    (h : ArgsInput p slots bs es M P regions bb eb s) :
    WP isa (.block (VG.Impl.Ffdh.Arm.Domain.powerArgs bs es ec)) s
      (fun t => Input p.base (p.slotValue bs) (p.slotValue es) p.len p.w M P regions bb eb t ∧
        t.mem = s.mem ∧ Rest roundClobbers s t) := by
  obtain ⟨tr, t, run, ⟨_, _, _, _, mem⟩, rest⟩ :=
    powerArgs_ok s bs es ec h.power.context stable hb he hc hk
  obtain ⟨_, _, run2, input⟩ := powerArgs_input s stable hb he hc hk baseLength positive fits count odd h.power
  obtain ⟨-, rfl⟩ := Exec.det run run2
  have frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact ⟨tr, t, run, ⟨input, A.stable frame (rest.mono (by simp [roundClobbers])) h.persistent, h.separate⟩,
    mem, rest.mono (by simp [roundClobbers])⟩


theorem powerAt_ok (s : State) {p : Inputs} {slots : List Nat} {bs es ec M : Nat}
    {P : State → Prop} {bb eb : List Byte}
    (A : TwoExp.Montgomery p.base p.len p.w P [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48])
    (fallback : Fallback p.base p.len p.w P [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48])
    (stable : stableSlots slots = true) (hb : bs ∈ slots) (he : es ∈ slots) (hc : ec ∈ slots) (hk : 32 ∈ slots)
    (baseLength : bb.length = p.k) (positive : 0 < eb.length) (fits : eb.length < 2 ^ 32)
    (count : p.slotValue ec = BitVec.ofNat 32 eb.length) (odd : M % 2 = 1)
    (h : ArgsInput p slots bs es M P [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48] bb eb s)
    (calls : KeyCallMemory p s) :
    WP isa (VG.Impl.Ffdh.Arm.KeyPower.powerAt A.phase fallback.code bs es ec) s fun t =>
      Context p slots t ∧ PhaseResult p.base p.len p.w M (Spec.Rsa.os2ip bb) P
        [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48] eb s t := by
  rw [VG.Impl.Ffdh.Arm.KeyPower.powerAt, WP.seq_iff]
  refine WP.mono (args_input s A stable hb he hc hk baseLength positive fits count odd h) ?_
  rintro u ⟨input, memU, restU⟩
  refine WP.mono (power_ok A fallback u input) ?_
  rintro t ⟨ready, value, modulus, r2, one, pt, frameT, restT⟩
  have frame : Frame [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48] s.mem t.mem := by
    rw [memU] at frameT
    exact frameT
  have rest := restU.trans restT
  exact ⟨h.power.context.after_call calls frame rest ready.ptr (fun d hd => (stableSlots_at stable hd).1),
    ready, value, modulus, r2, one, pt, frame, rest⟩

end VG.Proof.Ffdh.Arm.KeyPower
