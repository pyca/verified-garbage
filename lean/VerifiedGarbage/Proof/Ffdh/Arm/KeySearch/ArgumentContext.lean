module

import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ArgumentBlocks
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Fields
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Block

/-! The argument frame can be filled without changing the selected domain,
entropy-tape pointer, or register arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

structure ArgumentContext (p : KeyPublic) (used keys scalars : Nat) (s : State) : Prop where
  controller : Controller p.control s
  stack : Workspace s s.sp 32
  separate : (⟨State.addr p.control, 128⟩ : Region).Disjoint ⟨State.addr s.sp, 32⟩
  headers : Slots s.mem p.control (p.headers used keys scalars)
  stackBase : s.gpr .r12 = s.sp
  x : s.gpr .r0 = p.xp
  xlen : s.gpr .r1 = BitVec.ofNat 32 p.len
  y : s.gpr .r2 = p.yp
  ylen : s.gpr .r3 = BitVec.ofNat 32 p.len

theorem ArgumentContext.after {p : KeyPublic} {used keys scalars : Nat} {s t : State}
    (h : ArgumentContext p used keys scalars s) {rs : List Reg} (rest : Rest rs s t)
    (frame : Frame [⟨State.addr s.sp, 32⟩] s.mem t.mem)
    (kept : ∀ r ∈ [.r0, .r1, .r2, .r3, .r4, .r12], r ∉ rs := by decide) :
    ArgumentContext p used keys scalars t := by
  refine ⟨⟨h.controller.space.congr rest.wr, (rest.gpr .r4 (kept .r4 (by decide))).trans h.controller.ptr⟩,
    ?_, ?_, ?_, ?_, (rest.gpr .r0 (kept .r0 (by decide))).trans h.x,
    (rest.gpr .r1 (kept .r1 (by decide))).trans h.xlen,
    (rest.gpr .r2 (kept .r2 (by decide))).trans h.y,
    (rest.gpr .r3 (kept .r3 (by decide))).trans h.ylen⟩
  · rw [rest.sp]; exact h.stack.congr rest.wr
  · rw [rest.sp]; exact h.separate
  · apply (slots_fields _ _ _ _ _ _).mpr
    intro j hj
    have bound := headerIndices_bound hj
    exact (frame.readW (r := ⟨State.addr p.control, 128⟩)
      (Offset.contains_base _ (by omega) (by omega)) (by simpa using h.separate) (by decide)).trans
        ((slots_fields _ _ _ _ _ _).mp h.headers j hj)
  · rw [rest.sp]
    exact (rest.gpr .r12 (kept .r12 (by decide))).trans h.stackBase

theorem wp_argumentCopy {p : KeyPublic} {used keys scalars : Nat} {s : State} {is : List Instr}
    {Q : State → Prop} {value : BitVec 32} {j d : Nat}
    (h : ArgumentContext p used keys scalars s) (slot : j < 16) (fit : d + 4 ≤ 32)
    (source : lowWord s.mem p.control j = value)
    (next : ∀ t, ArgumentContext p used keys scalars t →
      t.mem = s.mem.writeW (off (State.addr s.sp) d) value → Rest [.r9] s t → WP isa (.block is) t Q) :
    WP isa (.block (VG.Impl.Ffdh.Arm.KeySearch.ldf .r9 j :: .str .r9 .r12 d :: is)) s Q := by
  change WP isa (.block ([VG.Impl.Ffdh.Arm.KeySearch.ldf .r9 j, .str .r9 .r12 d] ++ is)) s Q
  rw [WP.block_append_iff]
  refine WP.mono (argumentCopy_ok s h.controller slot h.stack fit h.stackBase source) ?_
  rintro t ⟨mem, rest⟩
  have frame : Frame [⟨State.addr s.sp, 32⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (by simp) _ (Offset.contains_base _ fit (by have := h.stack.nowrap; omega))
  exact next t (h.after rest frame) mem rest

theorem wp_argumentStore {p : KeyPublic} {used keys scalars : Nat} {s : State} {is : List Instr}
    {Q : State → Prop} {d : Nat} (h : ArgumentContext p used keys scalars s) (fit : d + 4 ≤ 32)
    (next : ∀ t, ArgumentContext p used keys scalars t →
      t.mem = s.mem.writeW (off (State.addr s.sp) d) (BitVec.ofNat 32 p.len) →
      Rest [] s t → WP isa (.block is) t Q) :
    WP isa (.block (.str .r1 .r12 d :: is)) s Q := by
  change WP isa (.block ([.str .r1 .r12 d] ++ is)) s Q
  rw [WP.block_append_iff]
  refine WP.mono (argumentStore_ok s .r1 h.stack fit h.stackBase h.xlen) ?_
  rintro t ⟨mem, rest⟩
  have frame : Frame [⟨State.addr s.sp, 32⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (by simp) _ (Offset.contains_base _ fit (by have := h.stack.nowrap; omega))
  exact next t (h.after rest frame) mem rest

end VG.Proof.Ffdh.Arm.KeySearch
