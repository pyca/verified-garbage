module

public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeState
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow

/-! Public subset and basis counters advance without changing arithmetic arrays. -/
@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Impl.Ffdh.Arm.CombPrecompute
open VG.Proof.X25519.Arm (Rest)

theorem Memory.controlRead {p : Inputs} {sp : BitVec 32} {s t : State}
    (h : Memory p sp s)
    (frame : Frame [⟨State.addr p.base,8*p.len⟩,⟨State.addr p.output,bytes p⟩,
      FrameStack.belowA s.sp 48] s.mem t.mem) (d : Nat) (hd : d+4≤72) :
    t.mem.readW (off (State.addr s.sp) d) 32=s.mem.readW (off (State.addr s.sp) d) 32 := by
  have sub := Offset.sub_base (State.addr s.sp) (d:=d) (n:=4) (k:=72) hd
  apply frame.readW (r:=⟨off (State.addr s.sp) d,4⟩) (Region.contains_self _ _) _ (by decide)
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact h.context.locals.separate.sub_left sub
  · rw [h.fixed] at sub ⊢
    exact h.localSeparate.sub_left sub
  · have sep : (⟨State.addr s.sp,72⟩ : Region).Disjoint (FrameStack.belowA s.sp 48) := by
      rw [FrameStack.belowA,FrameStack.addr_sub' h.calls.stack.fit]
      exact (Offset.below_disjoint _ (by decide)).symm
    exact sep.sub_left sub

theorem productNext_raw (s : State) {base : BitVec 32} {len low high : Nat}
    (locals : Locals base len s) (lowFit : low+1<2^32) (highFit : high<2^32)
    (savedLow : s.mem.readW (off (State.addr s.sp) 40) 32=BitVec.ofNat 32 low)
    (savedHigh : s.mem.readW (off (State.addr s.sp) 36) 32=BitVec.ofNat 32 high) :
    WP isa (.block productNext) s fun t =>
      (t.mem=s.mem.writeW (off (State.addr s.sp) 40) (BitVec.ofNat 32 (low+1)) ∧
        t.z=decide (low+1=high)) ∧ Rest [.r2,.r3,.r12] s t := by
  have a40 : State.addr (s.sp+BitVec.ofNat 32 40)=off (State.addr s.sp) 40 := addr_add (by have := locals.space.nowrap; omega)
  have a36 : State.addr (s.sp+BitVec.ofNat 32 36)=off (State.addr s.sp) 36 := addr_add (by have := locals.space.nowrap; omega)
  have read40 := locals.read (d:=40) (by decide)
  have read36 := locals.read (d:=36) (by decide)
  have write := locals.space.write (off:=40) (by decide)
  have add : BitVec.ofNat 32 low+1=BitVec.ofNat 32 (low+1) := (BitVec.ofNat_add _ _).symm
  have keep36 : (s.mem.writeW (off (State.addr s.sp) 40) (BitVec.ofNat 32 (low+1))).readW
      (off (State.addr s.sp) 36) 32=s.mem.readW (off (State.addr s.sp) 36) 32 := by
    have frame : Frame [⟨off (State.addr s.sp) 40,4⟩] s.mem
        (s.mem.writeW (off (State.addr s.sp) 40) (BitVec.ofNat 32 (low+1))) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    apply frame.readW (r:=⟨off (State.addr s.sp) 36,4⟩) (Region.contains_self _ _) _ (by decide)
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact Offset.disjoint _ (by decide) (by decide) (by decide)
  refine withRest_all (c:=.block productNext) [.r2,.r3,.r12] ?_ (by rfl) rfl
  unfold productNext VG.Impl.Ffdh.Arm.Domain.st
  ffrun [a40,a36,read40,read36,write,savedLow,savedHigh,add,keep36,off,BitVec.add_zero,subFlags]
  by_cases eq : low+1=high
  · rw [eq,BitVec.sub_self]
    simp
  · simp only [eq,decide_false,beq_eq_false_iff_ne,ne_eq]
    intro h
    have same := BitVec.sub_eq_iff_eq_add.mp h
    have := congrArg BitVec.toNat same
    simp only [BitVec.toNat_add] at this
    simp only [BitVec.toNat_ofNat] at this
    have hm := Nat.mod_eq_of_lt lowFit
    have hn := Nat.mod_eq_of_lt highFit
    simp only [hm,hn] at this
    change low+1=(0+high)%2^32 at this
    rw [Nat.zero_add,hn] at this
    exact eq this

theorem basisNext_raw (s : State) {base : BitVec 32} {len high : Nat}
    (locals : Locals base len s) (fit : 2*high<2^32)
    (saved : s.mem.readW (off (State.addr s.sp) 36) 32=BitVec.ofNat 32 high) :
    WP isa (.block basisNext) s fun t =>
      (t.mem=s.mem.writeW (off (State.addr s.sp) 36) (BitVec.ofNat 32 (2*high)) ∧
        t.z=decide (2*high=32)) ∧ Rest [.r3,.r12] s t := by
  have a36 : State.addr (s.sp+BitVec.ofNat 32 36)=off (State.addr s.sp) 36 := addr_add (by have := locals.space.nowrap; omega)
  have read := locals.read (d:=36) (by decide)
  have write := locals.space.write (off:=36) (by decide)
  have add : BitVec.ofNat 32 high+BitVec.ofNat 32 high=BitVec.ofNat 32 (2*high) := by
    rw [← BitVec.ofNat_add,Nat.two_mul]
  refine withRest_all (c:=.block basisNext) [.r3,.r12] ?_ (by rfl) rfl
  unfold basisNext VG.Impl.Ffdh.Arm.Domain.st
  ffrun [a36,read,write,saved,add,off,BitVec.add_zero,subFlags]
  by_cases eq : 2*high=32
  · rw [eq]
    decide
  · simp only [eq,decide_false,beq_eq_false_iff_ne,ne_eq]
    intro h
    have same := BitVec.sub_eq_iff_eq_add.mp h
    have := congrArg BitVec.toNat same
    simp only [BitVec.toNat_add] at this
    simp only [BitVec.toNat_ofNat] at this
    have hm := Nat.mod_eq_of_lt fit
    simp only [hm] at this
    exact eq this

end VG.Proof.Ffdh.Arm.CombBuilder
