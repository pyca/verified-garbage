module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAt
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack

/-! Preparing a saved modulus has a trace determined by public frame metadata. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

structure PrepareAtInput (p : Inputs) (slots : List Nat) (slot : Nat) (bs : List Byte) (s : State) : Prop where
  context : Context p slots s
  source : Octets p.base (p.slotValue slot) p.len bs s
  separate : Region.Disjoint ⟨State.addr (p.slotValue slot), p.k⟩ ⟨State.addr s.sp, 72⟩

theorem prepareAt_ct {p : Inputs} {slots : List Nat} {slot : Nat} {bs : List Byte}
    (stable : stableSlots slots = true) (hs : slot ∈ slots) (hk : 32 ∈ slots) (h0 : 0 ∈ slots)
    (length : bs.length = p.k) (large : 1 < Spec.Rsa.os2ip bs) (odd : Spec.Rsa.os2ip bs % 2 = 1) :
    RelCT isa (fun s t => PrepareAtInput p slots slot bs s ∧ PrepareAtInput p slots slot bs t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.prepareAt slot) (fun _ _ => True) := by
  have args := (prepareArgs_ct slot).mono
    (P' := fun (s t : State) => PrepareAtInput p slots slot bs s ∧ PrepareAtInput p slots slot bs t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  have wp (s : State) (h : PrepareAtInput p slots slot bs s) :=
    prepareArgs_input s slot h.context stable hs hk h0 h.source length h.separate large odd
  unfold VG.Impl.Ffdh.Arm.Domain.prepareAt
  exact relCT_chain args wp wp (prepare_ct p.width.2.2.2.2)

end VG.Proof.Ffdh.Arm
