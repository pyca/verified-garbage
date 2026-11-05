module

public import VerifiedGarbage.Proof.RsaPss.X86.VfVerified
public import VerifiedGarbage.Proof.RsaPss.X86.SgSat
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSASSA-PSS verification with a precomputed public key on x86: the contract is satisfiable

A state that meets `verifyPrecomputedTableContract` (`verify_sat`), with the
hash function's table that of any variant `w` of `vs` and MGF1's that of any
variant `wg` of `gs`: a modulus of 64 bytes, `e` of one byte, a signature of
64 bytes, the working space it needs, the precomputed values' 16 words, the
arguments above `esp = 0x20000`, and the tables where signing's are
(`Sg.withTabs`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes)
open VG.Proof.MdHashTable.X86 (MVar)
open VG.Proof.HashTable.X86 (TVar)
open VG.Proof.HashTable (symsOf32 symsOf32_distinct2)
open VG.Proof.RsaPss.X86.Sg (withTabs withTabs_arg withTabs_heldH withTabs_held D_mem)

/-- The state, but for the tables, for a digest of `D` bytes. -/
def satState (D : Nat) : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 131096 then BitVec.ofNat 8 D else if a = 131077 then 0x20 else if a = 131080 then 0x40 else
    if a = 131085 then 0x21 else if a = 131088 then 0x1 else if a = 131093 then 0x30 else
    if a = 131101 then 0x31 else if a = 131104 then 0x40 else if a = 131118 then 0x1 else
    if a = 131120 then 0x20 else if a = 131121 then 0x8 else if a = 131125 then 0x70 else
    if a = 131128 then 0x10 else if a = 131134 then 0x30 else if a = 131137 then 0x1 else
    if a = 131138 then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3000, D⟩, ⟨0x3100, 64⟩, ⟨0x7000, 128⟩, ⟨0x300000, 44⟩, ⟨0x300100, 20⟩]
  wr := [⟨0x10000, 2080 * 8⟩, ⟨0x20004, 64⟩]

theorem verify_sat16 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 16) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (vspec vs gs).pre s := by
  have hA : ∀ j < 16, (argAddr (satState 16) j).toNat + 4 ≤ 0x300000 := by decide
  have hhH := withTabs_heldH (satState 16) vs gs w wg
  have hhG := withTabs_held (satState 16) vs gs w wg
  have hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  refine ⟨withTabs (satState 16) vs gs w wg, ?_⟩
  have a0 : arg (withTabs (satState 16) vs gs w wg) 0 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  have a1 : arg (withTabs (satState 16) vs gs w wg) 1 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  have a2 : arg (withTabs (satState 16) vs gs w wg) 2 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  have a3 : arg (withTabs (satState 16) vs gs w wg) 3 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  have a4 : arg (withTabs (satState 16) vs gs w wg) 4 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  have a5 : arg (withTabs (satState 16) vs gs w wg) 5 = 0x10 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  have a6 : arg (withTabs (satState 16) vs gs w wg) 6 = 0x3100 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  have a7 : arg (withTabs (satState 16) vs gs w wg) 7 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  have a8 : arg (withTabs (satState 16) vs gs w wg) 8 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  have a9 : arg (withTabs (satState 16) vs gs w wg) 9 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  have a10 : arg (withTabs (satState 16) vs gs w wg) 10 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  have a11 : arg (withTabs (satState 16) vs gs w wg) 11 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  have a12 : arg (withTabs (satState 16) vs gs w wg) 12 = 0x7000 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  have a13 : arg (withTabs (satState 16) vs gs w wg) 13 = 0x10 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  have a14 : arg (withTabs (satState 16) vs gs w wg) 14 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  have a15 : arg (withTabs (satState 16) vs gs w wg) 15 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  have e : argAddr (withTabs (satState 16) vs gs w wg) 0 = 0x20004 := show argAddr (satState 16) 0 = _ by decide
  have esp : (withTabs (satState 16) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (satState 16) vs gs w wg).rd = (satState 16).rd := rfl
  have wr : (withTabs (satState 16) vs gs w wg).wr = (satState 16).wr := rfl
  have sy : (withTabs (satState 16) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (satState 16) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes, stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, e, esp, rd, wr, sy,
    satState]
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem verify_sat20 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 20) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (vspec vs gs).pre s := by
  have hA : ∀ j < 16, (argAddr (satState 20) j).toNat + 4 ≤ 0x300000 := by decide
  have hhH := withTabs_heldH (satState 20) vs gs w wg
  have hhG := withTabs_held (satState 20) vs gs w wg
  have hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  refine ⟨withTabs (satState 20) vs gs w wg, ?_⟩
  have a0 : arg (withTabs (satState 20) vs gs w wg) 0 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  have a1 : arg (withTabs (satState 20) vs gs w wg) 1 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  have a2 : arg (withTabs (satState 20) vs gs w wg) 2 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  have a3 : arg (withTabs (satState 20) vs gs w wg) 3 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  have a4 : arg (withTabs (satState 20) vs gs w wg) 4 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  have a5 : arg (withTabs (satState 20) vs gs w wg) 5 = 0x14 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  have a6 : arg (withTabs (satState 20) vs gs w wg) 6 = 0x3100 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  have a7 : arg (withTabs (satState 20) vs gs w wg) 7 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  have a8 : arg (withTabs (satState 20) vs gs w wg) 8 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  have a9 : arg (withTabs (satState 20) vs gs w wg) 9 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  have a10 : arg (withTabs (satState 20) vs gs w wg) 10 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  have a11 : arg (withTabs (satState 20) vs gs w wg) 11 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  have a12 : arg (withTabs (satState 20) vs gs w wg) 12 = 0x7000 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  have a13 : arg (withTabs (satState 20) vs gs w wg) 13 = 0x10 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  have a14 : arg (withTabs (satState 20) vs gs w wg) 14 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  have a15 : arg (withTabs (satState 20) vs gs w wg) 15 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  have e : argAddr (withTabs (satState 20) vs gs w wg) 0 = 0x20004 := show argAddr (satState 20) 0 = _ by decide
  have esp : (withTabs (satState 20) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (satState 20) vs gs w wg).rd = (satState 20).rd := rfl
  have wr : (withTabs (satState 20) vs gs w wg).wr = (satState 20).wr := rfl
  have sy : (withTabs (satState 20) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (satState 20) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes, stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, e, esp, rd, wr, sy,
    satState]
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem verify_sat28 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 28) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (vspec vs gs).pre s := by
  have hA : ∀ j < 16, (argAddr (satState 28) j).toNat + 4 ≤ 0x300000 := by decide
  have hhH := withTabs_heldH (satState 28) vs gs w wg
  have hhG := withTabs_held (satState 28) vs gs w wg
  have hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  refine ⟨withTabs (satState 28) vs gs w wg, ?_⟩
  have a0 : arg (withTabs (satState 28) vs gs w wg) 0 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  have a1 : arg (withTabs (satState 28) vs gs w wg) 1 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  have a2 : arg (withTabs (satState 28) vs gs w wg) 2 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  have a3 : arg (withTabs (satState 28) vs gs w wg) 3 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  have a4 : arg (withTabs (satState 28) vs gs w wg) 4 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  have a5 : arg (withTabs (satState 28) vs gs w wg) 5 = 0x1c := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  have a6 : arg (withTabs (satState 28) vs gs w wg) 6 = 0x3100 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  have a7 : arg (withTabs (satState 28) vs gs w wg) 7 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  have a8 : arg (withTabs (satState 28) vs gs w wg) 8 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  have a9 : arg (withTabs (satState 28) vs gs w wg) 9 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  have a10 : arg (withTabs (satState 28) vs gs w wg) 10 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  have a11 : arg (withTabs (satState 28) vs gs w wg) 11 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  have a12 : arg (withTabs (satState 28) vs gs w wg) 12 = 0x7000 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  have a13 : arg (withTabs (satState 28) vs gs w wg) 13 = 0x10 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  have a14 : arg (withTabs (satState 28) vs gs w wg) 14 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  have a15 : arg (withTabs (satState 28) vs gs w wg) 15 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  have e : argAddr (withTabs (satState 28) vs gs w wg) 0 = 0x20004 := show argAddr (satState 28) 0 = _ by decide
  have esp : (withTabs (satState 28) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (satState 28) vs gs w wg).rd = (satState 28).rd := rfl
  have wr : (withTabs (satState 28) vs gs w wg).wr = (satState 28).wr := rfl
  have sy : (withTabs (satState 28) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (satState 28) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes, stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, e, esp, rd, wr, sy,
    satState]
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem verify_sat32 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 32) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (vspec vs gs).pre s := by
  have hA : ∀ j < 16, (argAddr (satState 32) j).toNat + 4 ≤ 0x300000 := by decide
  have hhH := withTabs_heldH (satState 32) vs gs w wg
  have hhG := withTabs_held (satState 32) vs gs w wg
  have hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  refine ⟨withTabs (satState 32) vs gs w wg, ?_⟩
  have a0 : arg (withTabs (satState 32) vs gs w wg) 0 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  have a1 : arg (withTabs (satState 32) vs gs w wg) 1 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  have a2 : arg (withTabs (satState 32) vs gs w wg) 2 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  have a3 : arg (withTabs (satState 32) vs gs w wg) 3 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  have a4 : arg (withTabs (satState 32) vs gs w wg) 4 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  have a5 : arg (withTabs (satState 32) vs gs w wg) 5 = 0x20 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  have a6 : arg (withTabs (satState 32) vs gs w wg) 6 = 0x3100 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  have a7 : arg (withTabs (satState 32) vs gs w wg) 7 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  have a8 : arg (withTabs (satState 32) vs gs w wg) 8 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  have a9 : arg (withTabs (satState 32) vs gs w wg) 9 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  have a10 : arg (withTabs (satState 32) vs gs w wg) 10 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  have a11 : arg (withTabs (satState 32) vs gs w wg) 11 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  have a12 : arg (withTabs (satState 32) vs gs w wg) 12 = 0x7000 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  have a13 : arg (withTabs (satState 32) vs gs w wg) 13 = 0x10 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  have a14 : arg (withTabs (satState 32) vs gs w wg) 14 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  have a15 : arg (withTabs (satState 32) vs gs w wg) 15 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  have e : argAddr (withTabs (satState 32) vs gs w wg) 0 = 0x20004 := show argAddr (satState 32) 0 = _ by decide
  have esp : (withTabs (satState 32) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (satState 32) vs gs w wg).rd = (satState 32).rd := rfl
  have wr : (withTabs (satState 32) vs gs w wg).wr = (satState 32).wr := rfl
  have sy : (withTabs (satState 32) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (satState 32) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes, stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, e, esp, rd, wr, sy,
    satState]
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem verify_sat48 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 48) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (vspec vs gs).pre s := by
  have hA : ∀ j < 16, (argAddr (satState 48) j).toNat + 4 ≤ 0x300000 := by decide
  have hhH := withTabs_heldH (satState 48) vs gs w wg
  have hhG := withTabs_held (satState 48) vs gs w wg
  have hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  refine ⟨withTabs (satState 48) vs gs w wg, ?_⟩
  have a0 : arg (withTabs (satState 48) vs gs w wg) 0 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  have a1 : arg (withTabs (satState 48) vs gs w wg) 1 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  have a2 : arg (withTabs (satState 48) vs gs w wg) 2 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  have a3 : arg (withTabs (satState 48) vs gs w wg) 3 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  have a4 : arg (withTabs (satState 48) vs gs w wg) 4 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  have a5 : arg (withTabs (satState 48) vs gs w wg) 5 = 0x30 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  have a6 : arg (withTabs (satState 48) vs gs w wg) 6 = 0x3100 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  have a7 : arg (withTabs (satState 48) vs gs w wg) 7 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  have a8 : arg (withTabs (satState 48) vs gs w wg) 8 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  have a9 : arg (withTabs (satState 48) vs gs w wg) 9 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  have a10 : arg (withTabs (satState 48) vs gs w wg) 10 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  have a11 : arg (withTabs (satState 48) vs gs w wg) 11 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  have a12 : arg (withTabs (satState 48) vs gs w wg) 12 = 0x7000 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  have a13 : arg (withTabs (satState 48) vs gs w wg) 13 = 0x10 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  have a14 : arg (withTabs (satState 48) vs gs w wg) 14 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  have a15 : arg (withTabs (satState 48) vs gs w wg) 15 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  have e : argAddr (withTabs (satState 48) vs gs w wg) 0 = 0x20004 := show argAddr (satState 48) 0 = _ by decide
  have esp : (withTabs (satState 48) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (satState 48) vs gs w wg).rd = (satState 48).rd := rfl
  have wr : (withTabs (satState 48) vs gs w wg).wr = (satState 48).wr := rfl
  have sy : (withTabs (satState 48) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (satState 48) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes, stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, e, esp, rd, wr, sy,
    satState]
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem verify_sat64 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 64) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (vspec vs gs).pre s := by
  have hA : ∀ j < 16, (argAddr (satState 64) j).toNat + 4 ≤ 0x300000 := by decide
  have hhH := withTabs_heldH (satState 64) vs gs w wg
  have hhG := withTabs_held (satState 64) vs gs w wg
  have hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  refine ⟨withTabs (satState 64) vs gs w wg, ?_⟩
  have a0 : arg (withTabs (satState 64) vs gs w wg) 0 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  have a1 : arg (withTabs (satState 64) vs gs w wg) 1 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  have a2 : arg (withTabs (satState 64) vs gs w wg) 2 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  have a3 : arg (withTabs (satState 64) vs gs w wg) 3 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  have a4 : arg (withTabs (satState 64) vs gs w wg) 4 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  have a5 : arg (withTabs (satState 64) vs gs w wg) 5 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  have a6 : arg (withTabs (satState 64) vs gs w wg) 6 = 0x3100 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  have a7 : arg (withTabs (satState 64) vs gs w wg) 7 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  have a8 : arg (withTabs (satState 64) vs gs w wg) 8 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  have a9 : arg (withTabs (satState 64) vs gs w wg) 9 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  have a10 : arg (withTabs (satState 64) vs gs w wg) 10 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  have a11 : arg (withTabs (satState 64) vs gs w wg) 11 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  have a12 : arg (withTabs (satState 64) vs gs w wg) 12 = 0x7000 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  have a13 : arg (withTabs (satState 64) vs gs w wg) 13 = 0x10 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  have a14 : arg (withTabs (satState 64) vs gs w wg) 14 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  have a15 : arg (withTabs (satState 64) vs gs w wg) 15 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  have e : argAddr (withTabs (satState 64) vs gs w wg) 0 = 0x20004 := show argAddr (satState 64) 0 = _ by decide
  have esp : (withTabs (satState 64) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (satState 64) vs gs w wg).rd = (satState 64).rd := rfl
  have wr : (withTabs (satState 64) vs gs w wg).wr = (satState 64).wr := rfl
  have sy : (withTabs (satState 64) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (satState 64) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes, stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, e, esp, rd, wr, sy,
    satState]
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem verify_sat {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hs : Proof.MdHashTable.X86.Shape w)
    (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (vspec vs gs).pre s := by
  have hDm := D_mem hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hDm
  rcases hDm with e | e | e | e | e | e
  exacts [verify_sat16 hw hwg e hl, verify_sat20 hw hwg e hl, verify_sat28 hw hwg e hl, verify_sat32 hw hwg e hl,
    verify_sat48 hw hwg e hl, verify_sat64 hw hwg e hl]

end VG.Proof.RsaPss.X86.Vf
