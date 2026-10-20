module

public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Guards
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Syms
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch

/-! Preservation of live and finished native controller states. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

abbrev keptRegisters : List Reg := [.r4, .r5, .r6, .r7, .r8]

theorem KeyLive.keep {p : KeyPublic sampling} {original s t : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) {rs : List Reg}
    (rest : Rest rs s t) (mem : t.mem = s.mem) (syms : t.syms = s.syms)
    (kept : ∀ r ∈ keptRegisters, r ∉ rs := by decide) : KeyLive p original used keys scalars t := by
  refine ⟨h.input, h.used_le, h.keys_le, h.scalars_le, rest.rd.trans h.rd,
    rest.wr.trans h.wr, rest.sp.trans h.sp,
    (rest.gpr .r4 (kept .r4 (by decide))).trans h.pointer,
    fun r hr => (rest.gpr r (kept r (List.mem_cons_of_mem _ hr))).trans (h.kept r hr),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem]; exact h.saved
  · rw [mem]; exact h.random
  · rw [mem]; exact h.domain
  · rw [mem]; exact h.headers
  · rw [mem]; exact h.high
  · cases sampling <;> simpa only [KeyConstants.tablePtr, syms] using h.tablePtr
  · rw [mem]; exact h.held

theorem KeyDone.keep {p : KeyPublic sampling} {original s t : State} {result : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original result s) {rs : List Reg} (rest : Rest rs s t) (mem : t.mem = s.mem)
    (kept : ∀ r ∈ keptRegisters, r ∉ rs := by decide) : KeyDone p original result t := by
  refine ⟨h.input, h.used_le, rest.rd.trans h.rd, rest.wr.trans h.wr, rest.sp.trans h.sp,
    (rest.gpr .r4 (kept .r4 (by decide))).trans h.pointer,
    fun r hr => (rest.gpr r (kept r (List.mem_cons_of_mem _ hr))).trans (h.kept r hr),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem]; exact h.saved
  · rw [mem]; exact h.usedPtr
  · rw [mem]; exact h.used
  · rw [mem]; exact h.status
  · rw [mem]; exact h.policy
  · rw [mem]; exact h.output

theorem KeyLive.header {p : KeyPublic sampling} {original s : State} {used keys scalars j : Nat}
    {v : BitVec 32} (h : KeyLive p original used keys scalars s)
    (value : (j, v) ∈ p.headers used keys scalars) : lowWord s.mem p.control j = v :=
  h.headers (j, v) value

theorem KeyLive.keys_guard {p : KeyPublic sampling} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r9 0, .cmp .r9 (.imm 0)]) s fun t =>
      KeyLive p original used keys scalars t ∧ t.z = decide (keys = 0) := by
  refine WP.mono_syms (budgetGuard_ok s (n := keys) h.controller (by decide) (by have := h.keys_le; omega)
    (h.header (by simp [KeyPublic.headers]))) ?_
  rintro t ⟨⟨flag, mem⟩, rest⟩ syms
  exact ⟨h.keep rest mem syms, flag⟩

theorem KeyLive.scalars_guard {p : KeyPublic sampling} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r9 1, .cmp .r9 (.imm 0)]) s fun t =>
      KeyLive p original used keys scalars t ∧ t.z = decide (scalars = 0) := by
  refine WP.mono_syms (budgetGuard_ok s (n := scalars) h.controller (by decide) (by have := h.scalars_le; omega)
    (h.header (by simp [KeyPublic.headers]))) ?_
  rintro t ⟨⟨flag, mem⟩, rest⟩ syms
  exact ⟨h.keep rest mem syms, flag⟩

theorem KeyLive.room_guard {p : KeyPublic sampling} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.room) s fun t =>
      KeyLive p original used keys scalars t ∧ t.z = decide (p.randLen - used < p.len) := by
  refine WP.mono_syms (roomGuard_ok s (remaining := p.randLen - used) (width := p.len) h.controller (by have := h.input.bounds.randomFits; omega)
    (by have := h.input.bounds.maxLength; omega) (h.header (by simp [KeyPublic.headers]))
    (h.header (by simp [KeyPublic.headers]))) ?_
  rintro t ⟨⟨flag, mem⟩, rest⟩ syms
  exact ⟨h.keep rest mem syms, flag⟩

end VG.Proof.Ffdh.Arm.KeySearch
