module

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ControlMemory
public import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Search
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchData
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Capture register arguments before loading the stack arguments -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

def searchHeadValues (s : State) : List (Nat × BitVec 64) :=
  [(4, s.gpr .r12), (5, s.gpr .rdi), (6, s.gpr .rsi), (7, s.gpr .rdx),
    (8, s.gpr .rcx), (9, ((s.gpr .r8).setWidth 32).setWidth 64), (10, s.gpr .r9)]

def searchTailValues (s : State) : List (Nat × BitVec 64) :=
  [(11, stackArg s 0), (13, stackArg s 1), (15, stackArg s 2), (12, 0)]

def searchEntryValues (s : State) : List (Nat × BitVec 64) := searchHeadValues s ++ searchTailValues s

theorem searchHeadValues_bound (s : State) : ∀ e ∈ searchHeadValues s, e.1 < 16 := by
  simp only [searchHeadValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem searchTailValues_bound (s : State) : ∀ e ∈ searchTailValues s, e.1 < 16 := by
  simp only [searchTailValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem input_arg_contains (s : State) {j : Nat} (hj : j < 4) :
    (inputArgs s).Contains (stackArgAddr s j) 8 := by
  rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
    simp only [stackArgAddr, Nat.zero_add, Nat.mul_one, Offset.add_add]
    congr 2
    omega_using [hj]]
  exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

theorem input_args {p : SearchPublic} {s : State} (h : SearchInput p s) :
    ∀ j < 4, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8 := by
  intro j hj
  refine ⟨inputArgs s, ?_, input_arg_contains s hj⟩
  rw [h.1.2.2.1]
  exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))

theorem search_entry_head_ok {p : SearchPublic} {s : State} (h : SearchInput p s) :
    WP isa (.block entryHead) s fun t =>
      t.gpr .r12 = p.control ∧
      t.mem = writeController s.mem p.control (searchHeadValues s) ∧
      Keep [.rax, .r8, .r12] s t := by
  have scr := h.control_scr (s := s) rfl
  have hd : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 32) 64 = p.control := congrArg SearchPublic.control h.2
  have hs : ∀ d, d + 8 ≤ 128 → InRegions s.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have ha : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 32) 8 := input_args h 3 (by decide)
  refine WP.mono (WP.keep [.rax, .r8, .r12] (Q := fun t =>
    t.gpr .r12 = p.control ∧ t.mem = writeController s.mem p.control (searchHeadValues s)) ?_ rfl)
    fun _ ⟨⟨hr, hm⟩, k⟩ => ⟨hr, hm, k⟩
  unfold entryHead writeController searchHeadValues
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, hd, ha,
    hs 32 (by decide), hs 40 (by decide), hs 48 (by decide), hs 56 (by decide),
    hs 64 (by decide), hs 72 (by decide), hs 80 (by decide)]

end VG.Proof.Ffdh.X86_64.Generation
