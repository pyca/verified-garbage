module

public import VerifiedGarbage.Proof.Ffdh.Arm.DomainCallMemory
public import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeFinish
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! The peer, private scalar and output all avoid the shared arithmetic call area. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedExchange
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

def writes (p : Inputs) (s : State) : List Region :=
  exchangeWrites p s ++ [belowA s.sp 48]

structure CallMemory (p : Inputs) (scalarBytes : Nat) (s : State) : Prop extends DomainCallMemory p s where
  scalarBelow : Region.Disjoint ⟨State.addr p.privateValue, scalarBytes⟩ (belowA s.sp 48)
  outputBelow : Region.Disjoint ⟨State.addr p.output, p.k⟩ (belowA s.sp 48)

theorem CallMemory.of_outer {p : Inputs} {n : Nat} {s : State} {sp : BitVec 32}
    (fit : 176 ≤ sp.toNat) (pointer : s.sp = sp - BitVec.ofNat 32 128)
    (workspace : Region.Disjoint (belowA sp 176) ⟨State.addr p.base, 8 * p.len⟩)
    (domain : Region.Disjoint ⟨State.addr p.domain, p.dom.length⟩ (belowA sp 176))
    (publicValue : Region.Disjoint ⟨State.addr p.publicValue, p.k⟩ (belowA sp 176))
    (scalar : Region.Disjoint ⟨State.addr p.privateValue, n⟩ (belowA sp 176))
    (output : Region.Disjoint ⟨State.addr p.output, p.k⟩ (belowA sp 176)) :
    CallMemory p n s := by
  have inner : Region.Sub (belowA s.sp 48) (belowA sp 176) := by
    rw [pointer]
    exact belowA_inner (a := 48) (k := 128) (by decide) fit
  exact ⟨DomainCallMemory.of_outer fit pointer workspace domain publicValue,
    scalar.sub_right inner, output.sub_right inner⟩

theorem CallMemory.after {p : Inputs} {n : Nat} {s t : State} {rs : List Reg}
    (h : CallMemory p n s) (rest : Rest rs s t) : CallMemory p n t := by
  refine ⟨h.toDomainCallMemory.after rest, ?_, ?_⟩ <;> rw [rest.sp]
  · exact h.scalarBelow
  · exact h.outputBelow

end VG.Proof.Ffdh.Arm.SharedExchange
