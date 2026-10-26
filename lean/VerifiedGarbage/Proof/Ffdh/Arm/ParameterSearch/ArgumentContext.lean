module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Params
import Mathlib.Util.CompileInductive

/-! Candidate argument construction retains public controller fields and register arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Controller lowWord)

structure ArgumentContext (p : SearchParams) (used : Nat) (s : State) : Prop where
  controller : Controller p.control s
  stack : Workspace s s.sp 24
  separate : (⟨State.addr p.control, 128⟩ : Region).Disjoint ⟨State.addr s.sp, 24⟩
  headers : ∀ j ∈ searchSlots, lowWord s.mem p.control j = searchValues p used j
  pointer : s.gpr .r12 = s.sp
  out : s.gpr .r0 = p.c.out
  width : s.gpr .r1 = BitVec.ofNat 32 p.c.length
  usedPtr : s.gpr .r2 = p.control + 112#32
  bits : s.gpr .r3 = BitVec.ofNat 32 p.c.bits

theorem ArgumentContext.after_frame {p : SearchParams} {used : Nat} {s t : State} {rs : List Reg}
    (h : ArgumentContext p used s) (kept : ∀ r ∈ [.r0, .r1, .r2, .r3, .r4, .r12], r ∉ rs)
    (changed : Frame [⟨State.addr s.sp, 24⟩] s.mem t.mem) (rest : Rest rs s t) : ArgumentContext p used t := by
  refine ⟨⟨h.controller.space.congr rest.wr, (rest.gpr .r4 (kept _ (by simp))).trans h.controller.ptr⟩,
    by rw [rest.sp]; exact h.stack.congr rest.wr,
    by rw [rest.sp]; exact h.separate, ?_,
    by rw [rest.gpr .r12 (kept _ (by simp)), h.pointer, rest.sp],
    (rest.gpr .r0 (kept _ (by simp))).trans h.out,
    (rest.gpr .r1 (kept _ (by simp))).trans h.width,
    (rest.gpr .r2 (kept _ (by simp))).trans h.usedPtr,
    (rest.gpr .r3 (kept _ (by simp))).trans h.bits⟩
  intro j member
  have bound : j < 16 := by
    simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at member
    omega
  unfold lowWord
  rw [changed.readW (r := ⟨State.addr p.control, 128⟩)
    (Offset.contains_base _ (by omega : 8 * j + 4 ≤ 128) (by omega))
    (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact h.separate) (by decide)]
  exact h.headers j member

end VG.Proof.Ffdh.Arm.ParameterSearch
