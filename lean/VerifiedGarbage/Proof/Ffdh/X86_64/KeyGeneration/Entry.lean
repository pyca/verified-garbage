module

import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Layout
public import VerifiedGarbage.Impl.Ffdh.X86_64.KeyGeneration.Search
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ControlMemory
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Data
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.Contract

/-! # The key-generation controller's entry -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.Generation (writeController writeController_frame writeController_word
  writeController_append controllerValue)
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

def headValues (s : State) : List (Nat × BitVec 64) :=
  [(4, s.gpr .r12), (5, s.gpr .rdi), (6, s.gpr .rdx), (15, s.gpr .r8), (7, s.gpr .r9)]

def tailValues (s : State) : List (Nat × BitVec 64) :=
  [(8, stackArg s 0), (9, stackArg s 2), (10, stackArg s 3), (12, stackArg s 4),
    (13, stackArg s 5), (11, 0)]

def entryValues (s : State) : List (Nat × BitVec 64) := headValues s ++ tailValues s

theorem entryValues_bound (s : State) : ∀ e ∈ entryValues s, e.1 < 16 := by
  simp only [entryValues, headValues, tailValues, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem arg_contains (s : State) {j : Nat} (hj : j < 7) :
    (inArgs s).Contains (stackArgAddr s j) 8 := by
  rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
    simp only [stackArgAddr, Nat.zero_add, Nat.mul_one, Offset.add_add]
    congr 2
    omega_using [hj]]
  exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

theorem input_args {p : KeyPublic} {s : State} (h : KeyInput p s) :
    ∀ j < 7, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8 := by
  intro j hj
  refine ⟨inArgs s, ?_, arg_contains s hj⟩
  rw [h.1.2.2.1]
  exact List.mem_append_left _ (by simp [inReads])

theorem entry_head_ok {p : KeyPublic} {s : State} (h : KeyInput p s) :
    WP isa (.block entryHead) s fun t =>
      t.gpr .r12 = p.control ∧ t.mem = writeController s.mem p.control (headValues s) ∧
      Keep [.rax, .r12] s t := by
  have scr := h.control_scr (t := s) rfl
  have hd : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 56) 64 = p.control :=
    congrArg KeyPublic.control h.2
  have hs : ∀ d, d + 8 ≤ 128 → InRegions s.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have ha : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 56) 8 := input_args h 6 (by decide)
  refine WP.mono (WP.keep [.rax, .r12] (Q := fun t =>
    t.gpr .r12 = p.control ∧ t.mem = writeController s.mem p.control (headValues s)) ?_ rfl)
    fun _ ⟨⟨hr, hm⟩, k⟩ => ⟨hr, hm, k⟩
  unfold entryHead writeController headValues
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, hd, ha,
    hs 32 (by decide), hs 40 (by decide), hs 48 (by decide), hs 120 (by decide), hs 56 (by decide)]

theorem entry_head_args {p : KeyPublic} {s t : State} (h : KeyInput p s)
    (hm : t.mem = writeController s.mem p.control (headValues s))
    (k : Keep [.rax, .r12] s t) (j : Nat) (hj : j < 7) : stackArg t j = stackArg s j := by
  have hf := writeController_frame s.mem p.control (headValues s) (fun e he =>
    entryValues_bound s e (List.mem_append_left _ he))
  have hd : (inArgs s).Disjoint ⟨p.control, 128⟩ := by
    rw [← h.2]
    exact h.write_disjoint (w := inCtl s) (by simp [inWrites]) (by simp [inReads]) |>.symm
  change t.mem.readW (stackArgAddr t j) 64 = _
  have ha : stackArgAddr t j = stackArgAddr s j := by
    simp only [stackArgAddr, k.1 .rsp (by simp)]
  rw [ha, hm]
  exact hf.readW (arg_contains s hj) (fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact hd) (by decide)

theorem entry_tail_ok {p : KeyPublic} {s t : State} (h : KeyInput p s)
    (hm : t.mem = writeController s.mem p.control (headValues s))
    (k : Keep [.rax, .r12] s t) (hr : t.gpr .r12 = p.control) :
    WP isa (.block entryTail) t fun u =>
      u.mem = writeController t.mem p.control (tailValues s) ∧ Keep [.rax, .r10, .r11, .rcx, .rsi] t u := by
  have scr := h.control_scr (t := t) k.2.2
  have hs : ∀ d, d + 8 ≤ 128 → InRegions t.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have ha (j : Nat) (hj : j < 7) : InRegions (t.rd ++ t.wr) (stackArgAddr t j) 8 := by
    simpa only [k.2.1, k.2.2, stackArgAddr, k.1 .rsp (by simp)] using input_args h j hj
  have hv (j : Nat) (hj : j < 7) : t.mem.readW (stackArgAddr t j) 64 = stackArg s j :=
    entry_head_args h hm k j hj
  refine WP.keep [.rax, .r10, .r11, .rcx, .rsi] ?_ rfl
  unfold entryTail writeController tailValues
  simp only [List.foldl_cons, List.foldl_nil]
  have ha0 : InRegions (t.rd ++ t.wr) (t.gpr .rsp + BitVec.ofNat 64 8) 8 := ha 0 (by decide)
  have ha2 : InRegions (t.rd ++ t.wr) (t.gpr .rsp + BitVec.ofNat 64 24) 8 := ha 2 (by decide)
  have ha3 : InRegions (t.rd ++ t.wr) (t.gpr .rsp + BitVec.ofNat 64 32) 8 := ha 3 (by decide)
  have ha4 : InRegions (t.rd ++ t.wr) (t.gpr .rsp + BitVec.ofNat 64 40) 8 := ha 4 (by decide)
  have ha5 : InRegions (t.rd ++ t.wr) (t.gpr .rsp + BitVec.ofNat 64 48) 8 := ha 5 (by decide)
  have hv0 : t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 8) 64 = stackArg s 0 := hv 0 (by decide)
  have hv2 : t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 24) 64 = stackArg s 2 := hv 2 (by decide)
  have hv3 : t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 32) 64 = stackArg s 3 := hv 3 (by decide)
  have hv4 : t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 40) 64 = stackArg s 4 := hv 4 (by decide)
  have hv5 : t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 48) 64 = stackArg s 5 := hv 5 (by decide)
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul,
    hr, ha0, ha2, ha3, ha4, ha5, hv0, hv2, hv3, hv4, hv5, hs 64 (by decide), hs 72 (by decide),
    hs 80 (by decide), hs 96 (by decide), hs 104 (by decide), hs 88 (by decide)]
  rfl

theorem entry_ok {p : KeyPublic} {s : State} (h : KeyInput p s) :
    WP isa (.block entry) s fun t =>
      t.gpr .r12 = p.control ∧ t.mem = writeController s.mem p.control (entryValues s) ∧
      Keep [.rax, .r12, .r10, .r11, .rcx, .rsi] s t := by
  rw [entry, WP.block_append_iff]
  refine WP.mono (entry_head_ok h) fun t ⟨hr, hm, k⟩ => ?_
  refine WP.mono (entry_tail_ok h hm k hr) fun u ⟨hu, ku⟩ => ?_
  exact ⟨(ku.gpr (by decide)).trans hr,
    by rw [hu, hm, entryValues, writeController_append],
    (k.trans ku).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.KeyGeneration
