module

public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.Prepare
/-! Native modulus setup composes the FFDH frame with RSA's fast arithmetic. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

def prepareAtWrites (p : Inputs) (s : State) : List Region :=
  ⟨State.addr p.base, 8 * p.len⟩ :: prepareWrites s

theorem prepareArgs_input (s : State) {p : Inputs} {slots : List Nat} (slot : Nat) {bs : List Byte}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (hs : slot ∈ slots) (hk : 32 ∈ slots) (h0 : 0 ∈ slots)
    (source : Octets p.base (p.slotValue slot) p.len bs s) (length : bs.length = p.k)
    (sourceStack : Region.Disjoint ⟨State.addr (p.slotValue slot), p.k⟩ ⟨State.addr s.sp, 72⟩)
    (large : 1 < Spec.Rsa.os2ip bs) (odd : Spec.Rsa.os2ip bs % 2 = 1) :
    WP isa (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs slot)) s
      (PrepareInput p.base (p.slotValue slot) p.len p.k) := by
  refine WP.mono (prepareArgs_ok s slot h stable hs hk h0) ?_
  rintro u ⟨contextU, stack, _, countU, _, frameU, restU⟩
  have sourceU := source.after_frame frameU restU (by
    intro r hr
    rw [length]
    apply sourceStack.sub_right
    simp only [prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by decide))
  have bytes : Spec.Rsa.bytesAt u.mem (State.addr (p.slotValue slot)) p.k = bs := by
    simpa only [length] using sourceU.bytes
  exact ⟨contextU.workspace, by rw [stack.savedOutput]; exact stack, contextU.ptr, countU,
    p.minLength, p.maxLength, p.publicSpace,
    by rw [← length]; exact sourceU.fits,
    by rw [← length]; exact sourceU.readable,
    by rw [← length]; exact sourceU.separate,
    by rw [bytes]; exact large, by rw [bytes]; exact odd⟩

theorem prepareAt_ok (s : State) {p : Inputs} {slots : List Nat} (slot : Nat) {bs : List Byte}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (hs : slot ∈ slots) (hk : 32 ∈ slots) (h0 : 0 ∈ slots)
    (source : Octets p.base (p.slotValue slot) p.len bs s) (length : bs.length = p.k)
    (sourceStack : Region.Disjoint ⟨State.addr (p.slotValue slot), p.k⟩ ⟨State.addr s.sp, 72⟩)
    (large : 1 < Spec.Rsa.os2ip bs) (odd : Spec.Rsa.os2ip bs % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.prepareAt slot) s fun t => Context p slots t ∧
      ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 0 = Spec.Rsa.os2ip bs ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % Spec.Rsa.os2ip bs ∧
      Frame (prepareAtWrites p s) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.Domain.prepareAt, WP.seq_iff]
  refine WP.mono (prepareArgs_ok s slot h stable hs hk h0) ?_
  rintro u ⟨contextU, stack, srcU, countU, _, frameU, restU⟩
  have sourceU := source.after_frame frameU restU (by
    intro r hr
    rw [length]
    apply sourceStack.sub_right
    simp only [prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by decide))
  have bytes : Spec.Rsa.bytesAt u.mem (State.addr (p.slotValue slot)) p.k = bs := by
    simpa only [length] using sourceU.bytes
  have input : PrepareInput p.base (p.slotValue slot) p.len p.k u :=
    ⟨contextU.workspace, by rw [stack.savedOutput]; exact stack, contextU.ptr, countU,
      p.minLength, p.maxLength, p.publicSpace,
      by rw [← length]; exact sourceU.fits,
      by rw [← length]; exact sourceU.readable,
      by rw [← length]; exact sourceU.separate,
      by rw [bytes]; exact large, by rw [bytes]; exact odd⟩
  refine WP.mono (prepare_ok u input) ?_
  rintro t ⟨ready, modulus, r2, frameT, restT⟩
  rw [bytes] at modulus r2
  have contextT := contextU.after_workspace frameT restT ready.ptr
    (fun d hd => (stableSlots_at stable hd).1)
  have frame : Frame (prepareAtWrites p s) s.mem t.mem :=
    (frameU.mono (by intro r hr; exact List.mem_cons_of_mem _ hr)).trans
      (frameT.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact List.mem_cons_self))
  exact ⟨contextT, ready, modulus, r2, frame,
    (restU.mono (by simp [roundClobbers])).trans restT⟩

end VG.Proof.Ffdh.Arm
