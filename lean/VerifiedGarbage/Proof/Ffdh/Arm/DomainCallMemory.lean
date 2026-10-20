module

public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Bignum.Arm.CallStack
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Offset

/-! # Caller-owned FFDH buffers outside the shared arithmetic call stack

The public calling conditions persist through the exponent loop. A shared
Montgomery call may change its workspace and 48 bytes below the current
stack pointer, while the domain and public value remain outside
that stack space.
-/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure DomainCallMemory (p : Inputs) (s : State) : Prop where
  stack : CallStack p.base p.len s
  domain : Region.Disjoint ⟨State.addr p.domain, p.dom.length⟩ (belowA s.sp 48)
  publicValue : Region.Disjoint ⟨State.addr p.publicValue, p.k⟩ (belowA s.sp 48)

theorem DomainCallMemory.of_outer {p : Inputs} {s : State} {sp : BitVec 32}
    (fit : 176 ≤ sp.toNat) (pointer : s.sp = sp - BitVec.ofNat 32 128)
    (workspace : Region.Disjoint (belowA sp 176) ⟨State.addr p.base, 8 * p.len⟩)
    (domain : Region.Disjoint ⟨State.addr p.domain, p.dom.length⟩ (belowA sp 176))
    (publicValue : Region.Disjoint ⟨State.addr p.publicValue, p.k⟩ (belowA sp 176)) :
    DomainCallMemory p s := by
  have inner : Region.Sub (belowA s.sp 48) (belowA sp 176) := by
    rw [pointer]
    exact belowA_inner (a := 48) (k := 128) (by decide) fit
  refine ⟨⟨?_, workspace.sub_left inner⟩, domain.sub_right inner, publicValue.sub_right inner⟩
  rw [pointer, sub_toNat' (by omega : 128 ≤ sp.toNat)]
  omega

theorem DomainCallMemory.after {p : Inputs} {s t : State} {rs : List Reg}
    (h : DomainCallMemory p s) (rest : Rest rs s t) : DomainCallMemory p t := by
  refine ⟨h.stack.of_rest rest, ?_, ?_⟩ <;> rw [rest.sp]
  · exact h.domain
  · exact h.publicValue

theorem Octets.after_arithmetic {base src : BitVec 32} {len : Nat} {bs : List Byte}
    {s t : State} {rs : List Reg} (h : Octets base src len bs s)
    (frame : Frame [⟨State.addr base, 8 * len⟩, belowA s.sp 48] s.mem t.mem)
    (rest : Rest rs s t) (below : Region.Disjoint ⟨State.addr src, bs.length⟩ (belowA s.sp 48)) :
    Octets base src len bs t := by
  refine h.after_frame frame rest ?_
  intro r hr
  rcases List.mem_cons.mp hr with hr | hr
  · subst r; exact h.separate
  · have eq := List.mem_singleton.mp hr; subst r; exact below

theorem Context.after_arithmetic {p : Inputs} {slots : List Nat} {s t : State} {rs : List Reg}
    (h : Context p slots s) (call : DomainCallMemory p s)
    (frame : Frame [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48] s.mem t.mem)
    (rest : Rest rs s t) (ptr : t.gpr .r0 = p.base) (fit : ∀ d ∈ slots, d + 4 ≤ 72) :
    Context p slots t := by
  refine h.after_frame frame rest ptr ?_ ?_
  · intro r hr
    rcases List.mem_cons.mp hr with hr | hr
    · subst r; exact h.domain.separate
    · have eq := List.mem_singleton.mp hr; subst r; exact call.domain
  · intro d hd r hr
    have inside : (⟨off (State.addr s.sp) d, 4⟩ : Region).Sub ⟨State.addr s.sp, 72⟩ :=
      Offset.sub_base _ (fit d hd)
    rcases List.mem_cons.mp hr with hr | hr
    · subst r; exact h.locals.separate.sub_left inside
    · have eq := List.mem_singleton.mp hr; subst r
      have sep : Region.Disjoint ⟨State.addr s.sp, 72⟩ (belowA s.sp 48) := by
        rw [belowA, addr_sub' call.stack.fit]
        exact (Offset.below_disjoint _ (by decide)).symm
      exact sep.sub_left inside

theorem DomainCallMemory.domainSlice {p : Inputs} {slots : List Nat} {s : State}
    (h : DomainCallMemory p s) (context : Context p slots s) {d k : Nat}
    (positive : 0 < k) (fit : d + k ≤ p.dom.length) :
    Region.Disjoint ⟨State.addr (p.domain + BitVec.ofNat 32 d), k⟩ (belowA s.sp 48) := by
  rw [VG.Arm.addr_add (by have := context.domain.fits; omega)]
  exact h.domain.sub_left (Offset.sub_base _ fit)

end VG.Proof.Ffdh.Arm
