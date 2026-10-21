module

public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! Native parameter-generation arguments saved in the common 72-byte
FFDH frame. Only slots a phase needs are kept in its invariant. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

structure SavedFrame (values : Nat → BitVec 32) (slots : List Nat) (s : State) : Prop where
  space : Workspace s s.sp 72
  saved : ∀ d ∈ slots, s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 d)) 32 = values d

theorem SavedFrame.read {values : Nat → BitVec 32} {slots : List Nat} {s : State}
    (h : SavedFrame values slots s) {d : Nat} (fit : d + 4 ≤ 72) :
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 d)) 4 := by
  rw [VG.Arm.addr_add (by have := h.space.nowrap; omega)]
  exact h.space.read fit

theorem SavedFrame.after_frame {values : Nat → BitVec 32} {slots : List Nat} {s t : State}
    {regions : List Region} {rs : List Reg} (h : SavedFrame values slots s)
    (frame : Frame regions s.mem t.mem) (rest : Rest rs s t)
    (separate : ∀ d ∈ slots, ∀ r ∈ regions,
      (⟨State.addr (s.sp + BitVec.ofNat 32 d), 4⟩ : Region).Disjoint r) :
    SavedFrame values slots t := by
  refine ⟨?_, ?_⟩
  · rw [rest.sp]
    exact h.space.congr rest.wr
  · intro d hd
    rw [rest.sp, frame.readW (r := ⟨State.addr (s.sp + BitVec.ofNat 32 d), 4⟩)
      (Region.contains_self _ _) (separate d hd) (by decide)]
    exact h.saved d hd

theorem SavedFrame.after_memory {values : Nat → BitVec 32} {slots : List Nat} {s t : State}
    {rs : List Reg} (h : SavedFrame values slots s) (memory : t.mem = s.mem) (rest : Rest rs s t) :
    SavedFrame values slots t := by
  refine ⟨?_, ?_⟩
  · rw [rest.sp]
    exact h.space.congr rest.wr
  · intro d hd
    rw [memory, rest.sp]
    exact h.saved d hd

theorem SavedFrame.after_output {values : Nat → BitVec 32} {slots : List Nat} {s t : State}
    {dst : BitVec 32} {n : Nat} {rs : List Reg} (h : SavedFrame values slots s)
    (bounds : ∀ d ∈ slots, d + 4 ≤ 72)
    (frame : Frame [⟨State.addr dst, n⟩] s.mem t.mem) (rest : Rest rs s t)
    (separate : (⟨State.addr dst, n⟩ : Region).Disjoint ⟨State.addr s.sp, 72⟩) :
    SavedFrame values slots t := by
  refine h.after_frame frame rest ?_
  intro d hd r hr
  rw [List.mem_singleton] at hr
  subst r
  rw [VG.Arm.addr_add (by have := h.space.nowrap; have := bounds d hd; omega)]
  exact separate.symm.sub_left (Offset.sub_base _ (bounds d hd))

end VG.Proof.Ffdh.Arm.ParameterCandidate
