module

public import VerifiedGarbage.Proof.RsaPss.X86.SgPCall
public import VerifiedGarbage.Proof.RsaPss.X86.SgSat
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSASSA-PSS signing on x86, given `pre`: the contract is satisfiable

As `SgSat.lean`, with the key of `Proof/Rsa/PreKey.lean` (`keyMem`): a
modulus of 64 bytes at `0x2000`, `p` and `q` of 32 at `0x4200` and
`0x4300`, `dP`, `dQ` and `qInv` of 32, and `pre` (24 words) at `0x4800`
(`satStateP`); the tables are written above all of it (`putWs_byte`).
-/

-- separate module: builds in parallel with the proof (`SgPVerified`), which it does not need.

@[expose] public section

namespace VG.Proof.RsaPss.X86.Sg

open VG
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes)
open VG.Proof.MdHashTable.X86 (MVar)
open VG.Proof.HashTable.X86 (TVar)
open VG.Proof.HashTable (symsOf32 symsOf32_distinct2)
open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)

/-- Words written from `p` on leave the bytes below `p` as they were. -/
theorem putWs_byte {a : Addr} : ∀ {ws : List (BitVec 32)} {m : Mem} {p : Addr},
    a.toNat < p.toNat → p.toNat + 4 * ws.length < 2 ^ 64 → putWs m p ws a = m a
  | [], _, _, _, _ => rfl
  | w :: ws, m, p, ha, hp => by
    have e : (p + 4).toNat = p.toNat + 4 := by
      rw [BitVec.toNat_add]; simp only [List.length_cons] at hp; simp; omega_using [hp]
    simp only [putWs]
    rw [putWs_byte (by rw [e]; omega_using [ha]) (by rw [e]; simp only [List.length_cons] at hp; omega_using [hp])]
    refine Mem.write_apply fun h => ?_
    rw [BitVec.toNat_sub] at h
    simp only [List.length_cons] at hp
    have := a.isLt
    omega_using [ha, hp, h]

/-- The memory: the key, the arguments that differ from `satState D`'s, and its. -/
def memP (D : Nat) (a : Addr) : Byte :=
  bif keyIn a.toNat then keyMem a
  else if a = 0x2001D then 0x42 else if a = 0x20020 then 32 else if a = 0x20025 then 0x43
  else if a = 0x20028 then 32 else if a = 0x20030 then 32 else if a = 0x20038 then 32
  else if a = 0x20040 then 32 else if a = 0x20065 then 0x48 else if a = 0x20068 then 24
  else (satState D).mem a

/-- `satState D` with the key and its precomputed values. -/
def satStateP (D : Nat) : State :=
  { satState D with
    mem := memP D
    rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x3300, 32⟩, ⟨0x3400, 32⟩, ⟨0x3500, 32⟩,
      ⟨0x3000, D⟩, ⟨0x3600, 0⟩, ⟨0x4800, 192⟩, ⟨0x300000, 44⟩, ⟨0x300100, 44⟩]
    wr := [⟨0x1000, 64⟩, ⟨0x10000, 2080 * 8⟩, ⟨0x20004, 104⟩] }

theorem withTabsP_key (D : Nat) (vs : List MVar) (gs : List TVar) (w : MVar) (wg : TVar) :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt (withTabs (satStateP D) vs gs w wg).mem 0x2000 64)
      (Spec.Rsa.bytesAt (withTabs (satStateP D) vs gs w wg).mem 0x4200 32)
      (Spec.Rsa.bytesAt (withTabs (satStateP D) vs gs w wg).mem 0x4300 32) =
    some (Spec.Rsa.wordsAt (withTabs (satStateP D) vs gs w wg).mem 0x4800 24) := by
  refine key_pre_of fun a ha => ?_
  have hlt : a.toNat < 0x48C0 := by
    simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha; omega
  simp only [withTabs]
  rw [putWs_byte (by show a.toNat < 0x300100; omega_using [hlt]) (by simp [FnTable.words, Proof.HashTable.X86.tableOf,
      Proof.MdHashTable.X86.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf]),
    putWs_byte (by show a.toNat < 0x300000; omega_using [hlt]) (by simp [FnTable.words, Proof.MdHashTable.X86.tableOf,
      Spec.MdHashTable.dataOf, Spec.HashTable.dataOf])]
  show memP D a = keyMem a
  simp only [memP, ha, Bool.cond_true]

theorem sign_satP16 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 16) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (sspecP vs gs).pre s := by
  have hA : ∀ j < 26, (argAddr (satStateP 16) j).toNat + 4 ≤ 0x300000 := by decide
  have hhH := withTabs_heldH (satStateP 16) vs gs w wg
  have hhG := withTabs_held (satStateP 16) vs gs w wg
  have hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  have hk := withTabsP_key 16 vs gs w wg
  refine ⟨withTabs (satStateP 16) vs gs w wg, ?_⟩
  have a0 : arg (withTabs (satStateP 16) vs gs w wg) 0 = 0x1000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  have a1 : arg (withTabs (satStateP 16) vs gs w wg) 1 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  have a2 : arg (withTabs (satStateP 16) vs gs w wg) 2 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  have a3 : arg (withTabs (satStateP 16) vs gs w wg) 3 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  have a4 : arg (withTabs (satStateP 16) vs gs w wg) 4 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  have a5 : arg (withTabs (satStateP 16) vs gs w wg) 5 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  have a6 : arg (withTabs (satStateP 16) vs gs w wg) 6 = 0x4200 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  have a7 : arg (withTabs (satStateP 16) vs gs w wg) 7 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  have a8 : arg (withTabs (satStateP 16) vs gs w wg) 8 = 0x4300 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  have a9 : arg (withTabs (satStateP 16) vs gs w wg) 9 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  have a10 : arg (withTabs (satStateP 16) vs gs w wg) 10 = 0x3300 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  have a11 : arg (withTabs (satStateP 16) vs gs w wg) 11 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  have a12 : arg (withTabs (satStateP 16) vs gs w wg) 12 = 0x3400 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  have a13 : arg (withTabs (satStateP 16) vs gs w wg) 13 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  have a14 : arg (withTabs (satStateP 16) vs gs w wg) 14 = 0x3500 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  have a15 : arg (withTabs (satStateP 16) vs gs w wg) 15 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  have a16 : arg (withTabs (satStateP 16) vs gs w wg) 16 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 16 (by decide))]; decide
  have a17 : arg (withTabs (satStateP 16) vs gs w wg) 17 = 0x10 := by rw [withTabs_arg _ vs gs w wg (hA 17 (by decide))]; decide
  have a18 : arg (withTabs (satStateP 16) vs gs w wg) 18 = 0x3600 := by rw [withTabs_arg _ vs gs w wg (hA 18 (by decide))]; decide
  have a19 : arg (withTabs (satStateP 16) vs gs w wg) 19 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 19 (by decide))]; decide
  have a20 : arg (withTabs (satStateP 16) vs gs w wg) 20 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 20 (by decide))]; decide
  have a21 : arg (withTabs (satStateP 16) vs gs w wg) 21 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 21 (by decide))]; decide
  have a22 : arg (withTabs (satStateP 16) vs gs w wg) 22 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 22 (by decide))]; decide
  have a23 : arg (withTabs (satStateP 16) vs gs w wg) 23 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 23 (by decide))]; decide
  have a24 : arg (withTabs (satStateP 16) vs gs w wg) 24 = 0x4800 := by rw [withTabs_arg _ vs gs w wg (hA 24 (by decide))]; decide
  have a25 : arg (withTabs (satStateP 16) vs gs w wg) 25 = 24 := by rw [withTabs_arg _ vs gs w wg (hA 25 (by decide))]; decide
  have e : argAddr (withTabs (satStateP 16) vs gs w wg) 0 = 0x20004 := show argAddr (satStateP 16) 0 = _ by decide
  have esp : (withTabs (satStateP 16) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (satStateP 16) vs gs w wg).rd = (satStateP 16).rd := rfl
  have wr : (withTabs (satStateP 16) vs gs w wg).wr = (satStateP 16).wr := rfl
  have sy : (withTabs (satStateP 16) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (satStateP 16) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, e, esp, rd, wr, sy, satStateP]
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · exact hk
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem sign_satP20 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 20) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (sspecP vs gs).pre s := by
  have hA : ∀ j < 26, (argAddr (satStateP 20) j).toNat + 4 ≤ 0x300000 := by decide
  have hhH := withTabs_heldH (satStateP 20) vs gs w wg
  have hhG := withTabs_held (satStateP 20) vs gs w wg
  have hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  have hk := withTabsP_key 20 vs gs w wg
  refine ⟨withTabs (satStateP 20) vs gs w wg, ?_⟩
  have a0 : arg (withTabs (satStateP 20) vs gs w wg) 0 = 0x1000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  have a1 : arg (withTabs (satStateP 20) vs gs w wg) 1 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  have a2 : arg (withTabs (satStateP 20) vs gs w wg) 2 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  have a3 : arg (withTabs (satStateP 20) vs gs w wg) 3 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  have a4 : arg (withTabs (satStateP 20) vs gs w wg) 4 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  have a5 : arg (withTabs (satStateP 20) vs gs w wg) 5 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  have a6 : arg (withTabs (satStateP 20) vs gs w wg) 6 = 0x4200 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  have a7 : arg (withTabs (satStateP 20) vs gs w wg) 7 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  have a8 : arg (withTabs (satStateP 20) vs gs w wg) 8 = 0x4300 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  have a9 : arg (withTabs (satStateP 20) vs gs w wg) 9 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  have a10 : arg (withTabs (satStateP 20) vs gs w wg) 10 = 0x3300 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  have a11 : arg (withTabs (satStateP 20) vs gs w wg) 11 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  have a12 : arg (withTabs (satStateP 20) vs gs w wg) 12 = 0x3400 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  have a13 : arg (withTabs (satStateP 20) vs gs w wg) 13 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  have a14 : arg (withTabs (satStateP 20) vs gs w wg) 14 = 0x3500 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  have a15 : arg (withTabs (satStateP 20) vs gs w wg) 15 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  have a16 : arg (withTabs (satStateP 20) vs gs w wg) 16 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 16 (by decide))]; decide
  have a17 : arg (withTabs (satStateP 20) vs gs w wg) 17 = 0x14 := by rw [withTabs_arg _ vs gs w wg (hA 17 (by decide))]; decide
  have a18 : arg (withTabs (satStateP 20) vs gs w wg) 18 = 0x3600 := by rw [withTabs_arg _ vs gs w wg (hA 18 (by decide))]; decide
  have a19 : arg (withTabs (satStateP 20) vs gs w wg) 19 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 19 (by decide))]; decide
  have a20 : arg (withTabs (satStateP 20) vs gs w wg) 20 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 20 (by decide))]; decide
  have a21 : arg (withTabs (satStateP 20) vs gs w wg) 21 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 21 (by decide))]; decide
  have a22 : arg (withTabs (satStateP 20) vs gs w wg) 22 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 22 (by decide))]; decide
  have a23 : arg (withTabs (satStateP 20) vs gs w wg) 23 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 23 (by decide))]; decide
  have a24 : arg (withTabs (satStateP 20) vs gs w wg) 24 = 0x4800 := by rw [withTabs_arg _ vs gs w wg (hA 24 (by decide))]; decide
  have a25 : arg (withTabs (satStateP 20) vs gs w wg) 25 = 24 := by rw [withTabs_arg _ vs gs w wg (hA 25 (by decide))]; decide
  have e : argAddr (withTabs (satStateP 20) vs gs w wg) 0 = 0x20004 := show argAddr (satStateP 20) 0 = _ by decide
  have esp : (withTabs (satStateP 20) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (satStateP 20) vs gs w wg).rd = (satStateP 20).rd := rfl
  have wr : (withTabs (satStateP 20) vs gs w wg).wr = (satStateP 20).wr := rfl
  have sy : (withTabs (satStateP 20) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (satStateP 20) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, e, esp, rd, wr, sy, satStateP]
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · exact hk
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem sign_satP28 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 28) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (sspecP vs gs).pre s := by
  have hA : ∀ j < 26, (argAddr (satStateP 28) j).toNat + 4 ≤ 0x300000 := by decide
  have hhH := withTabs_heldH (satStateP 28) vs gs w wg
  have hhG := withTabs_held (satStateP 28) vs gs w wg
  have hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  have hk := withTabsP_key 28 vs gs w wg
  refine ⟨withTabs (satStateP 28) vs gs w wg, ?_⟩
  have a0 : arg (withTabs (satStateP 28) vs gs w wg) 0 = 0x1000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  have a1 : arg (withTabs (satStateP 28) vs gs w wg) 1 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  have a2 : arg (withTabs (satStateP 28) vs gs w wg) 2 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  have a3 : arg (withTabs (satStateP 28) vs gs w wg) 3 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  have a4 : arg (withTabs (satStateP 28) vs gs w wg) 4 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  have a5 : arg (withTabs (satStateP 28) vs gs w wg) 5 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  have a6 : arg (withTabs (satStateP 28) vs gs w wg) 6 = 0x4200 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  have a7 : arg (withTabs (satStateP 28) vs gs w wg) 7 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  have a8 : arg (withTabs (satStateP 28) vs gs w wg) 8 = 0x4300 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  have a9 : arg (withTabs (satStateP 28) vs gs w wg) 9 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  have a10 : arg (withTabs (satStateP 28) vs gs w wg) 10 = 0x3300 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  have a11 : arg (withTabs (satStateP 28) vs gs w wg) 11 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  have a12 : arg (withTabs (satStateP 28) vs gs w wg) 12 = 0x3400 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  have a13 : arg (withTabs (satStateP 28) vs gs w wg) 13 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  have a14 : arg (withTabs (satStateP 28) vs gs w wg) 14 = 0x3500 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  have a15 : arg (withTabs (satStateP 28) vs gs w wg) 15 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  have a16 : arg (withTabs (satStateP 28) vs gs w wg) 16 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 16 (by decide))]; decide
  have a17 : arg (withTabs (satStateP 28) vs gs w wg) 17 = 0x1c := by rw [withTabs_arg _ vs gs w wg (hA 17 (by decide))]; decide
  have a18 : arg (withTabs (satStateP 28) vs gs w wg) 18 = 0x3600 := by rw [withTabs_arg _ vs gs w wg (hA 18 (by decide))]; decide
  have a19 : arg (withTabs (satStateP 28) vs gs w wg) 19 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 19 (by decide))]; decide
  have a20 : arg (withTabs (satStateP 28) vs gs w wg) 20 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 20 (by decide))]; decide
  have a21 : arg (withTabs (satStateP 28) vs gs w wg) 21 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 21 (by decide))]; decide
  have a22 : arg (withTabs (satStateP 28) vs gs w wg) 22 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 22 (by decide))]; decide
  have a23 : arg (withTabs (satStateP 28) vs gs w wg) 23 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 23 (by decide))]; decide
  have a24 : arg (withTabs (satStateP 28) vs gs w wg) 24 = 0x4800 := by rw [withTabs_arg _ vs gs w wg (hA 24 (by decide))]; decide
  have a25 : arg (withTabs (satStateP 28) vs gs w wg) 25 = 24 := by rw [withTabs_arg _ vs gs w wg (hA 25 (by decide))]; decide
  have e : argAddr (withTabs (satStateP 28) vs gs w wg) 0 = 0x20004 := show argAddr (satStateP 28) 0 = _ by decide
  have esp : (withTabs (satStateP 28) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (satStateP 28) vs gs w wg).rd = (satStateP 28).rd := rfl
  have wr : (withTabs (satStateP 28) vs gs w wg).wr = (satStateP 28).wr := rfl
  have sy : (withTabs (satStateP 28) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (satStateP 28) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, e, esp, rd, wr, sy, satStateP]
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · exact hk
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem sign_satP32 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 32) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (sspecP vs gs).pre s := by
  have hA : ∀ j < 26, (argAddr (satStateP 32) j).toNat + 4 ≤ 0x300000 := by decide
  have hhH := withTabs_heldH (satStateP 32) vs gs w wg
  have hhG := withTabs_held (satStateP 32) vs gs w wg
  have hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  have hk := withTabsP_key 32 vs gs w wg
  refine ⟨withTabs (satStateP 32) vs gs w wg, ?_⟩
  have a0 : arg (withTabs (satStateP 32) vs gs w wg) 0 = 0x1000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  have a1 : arg (withTabs (satStateP 32) vs gs w wg) 1 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  have a2 : arg (withTabs (satStateP 32) vs gs w wg) 2 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  have a3 : arg (withTabs (satStateP 32) vs gs w wg) 3 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  have a4 : arg (withTabs (satStateP 32) vs gs w wg) 4 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  have a5 : arg (withTabs (satStateP 32) vs gs w wg) 5 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  have a6 : arg (withTabs (satStateP 32) vs gs w wg) 6 = 0x4200 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  have a7 : arg (withTabs (satStateP 32) vs gs w wg) 7 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  have a8 : arg (withTabs (satStateP 32) vs gs w wg) 8 = 0x4300 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  have a9 : arg (withTabs (satStateP 32) vs gs w wg) 9 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  have a10 : arg (withTabs (satStateP 32) vs gs w wg) 10 = 0x3300 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  have a11 : arg (withTabs (satStateP 32) vs gs w wg) 11 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  have a12 : arg (withTabs (satStateP 32) vs gs w wg) 12 = 0x3400 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  have a13 : arg (withTabs (satStateP 32) vs gs w wg) 13 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  have a14 : arg (withTabs (satStateP 32) vs gs w wg) 14 = 0x3500 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  have a15 : arg (withTabs (satStateP 32) vs gs w wg) 15 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  have a16 : arg (withTabs (satStateP 32) vs gs w wg) 16 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 16 (by decide))]; decide
  have a17 : arg (withTabs (satStateP 32) vs gs w wg) 17 = 0x20 := by rw [withTabs_arg _ vs gs w wg (hA 17 (by decide))]; decide
  have a18 : arg (withTabs (satStateP 32) vs gs w wg) 18 = 0x3600 := by rw [withTabs_arg _ vs gs w wg (hA 18 (by decide))]; decide
  have a19 : arg (withTabs (satStateP 32) vs gs w wg) 19 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 19 (by decide))]; decide
  have a20 : arg (withTabs (satStateP 32) vs gs w wg) 20 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 20 (by decide))]; decide
  have a21 : arg (withTabs (satStateP 32) vs gs w wg) 21 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 21 (by decide))]; decide
  have a22 : arg (withTabs (satStateP 32) vs gs w wg) 22 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 22 (by decide))]; decide
  have a23 : arg (withTabs (satStateP 32) vs gs w wg) 23 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 23 (by decide))]; decide
  have a24 : arg (withTabs (satStateP 32) vs gs w wg) 24 = 0x4800 := by rw [withTabs_arg _ vs gs w wg (hA 24 (by decide))]; decide
  have a25 : arg (withTabs (satStateP 32) vs gs w wg) 25 = 24 := by rw [withTabs_arg _ vs gs w wg (hA 25 (by decide))]; decide
  have e : argAddr (withTabs (satStateP 32) vs gs w wg) 0 = 0x20004 := show argAddr (satStateP 32) 0 = _ by decide
  have esp : (withTabs (satStateP 32) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (satStateP 32) vs gs w wg).rd = (satStateP 32).rd := rfl
  have wr : (withTabs (satStateP 32) vs gs w wg).wr = (satStateP 32).wr := rfl
  have sy : (withTabs (satStateP 32) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (satStateP 32) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, e, esp, rd, wr, sy, satStateP]
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · exact hk
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem sign_satP48 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 48) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (sspecP vs gs).pre s := by
  have hA : ∀ j < 26, (argAddr (satStateP 48) j).toNat + 4 ≤ 0x300000 := by decide
  have hhH := withTabs_heldH (satStateP 48) vs gs w wg
  have hhG := withTabs_held (satStateP 48) vs gs w wg
  have hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  have hk := withTabsP_key 48 vs gs w wg
  refine ⟨withTabs (satStateP 48) vs gs w wg, ?_⟩
  have a0 : arg (withTabs (satStateP 48) vs gs w wg) 0 = 0x1000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  have a1 : arg (withTabs (satStateP 48) vs gs w wg) 1 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  have a2 : arg (withTabs (satStateP 48) vs gs w wg) 2 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  have a3 : arg (withTabs (satStateP 48) vs gs w wg) 3 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  have a4 : arg (withTabs (satStateP 48) vs gs w wg) 4 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  have a5 : arg (withTabs (satStateP 48) vs gs w wg) 5 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  have a6 : arg (withTabs (satStateP 48) vs gs w wg) 6 = 0x4200 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  have a7 : arg (withTabs (satStateP 48) vs gs w wg) 7 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  have a8 : arg (withTabs (satStateP 48) vs gs w wg) 8 = 0x4300 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  have a9 : arg (withTabs (satStateP 48) vs gs w wg) 9 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  have a10 : arg (withTabs (satStateP 48) vs gs w wg) 10 = 0x3300 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  have a11 : arg (withTabs (satStateP 48) vs gs w wg) 11 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  have a12 : arg (withTabs (satStateP 48) vs gs w wg) 12 = 0x3400 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  have a13 : arg (withTabs (satStateP 48) vs gs w wg) 13 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  have a14 : arg (withTabs (satStateP 48) vs gs w wg) 14 = 0x3500 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  have a15 : arg (withTabs (satStateP 48) vs gs w wg) 15 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  have a16 : arg (withTabs (satStateP 48) vs gs w wg) 16 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 16 (by decide))]; decide
  have a17 : arg (withTabs (satStateP 48) vs gs w wg) 17 = 0x30 := by rw [withTabs_arg _ vs gs w wg (hA 17 (by decide))]; decide
  have a18 : arg (withTabs (satStateP 48) vs gs w wg) 18 = 0x3600 := by rw [withTabs_arg _ vs gs w wg (hA 18 (by decide))]; decide
  have a19 : arg (withTabs (satStateP 48) vs gs w wg) 19 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 19 (by decide))]; decide
  have a20 : arg (withTabs (satStateP 48) vs gs w wg) 20 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 20 (by decide))]; decide
  have a21 : arg (withTabs (satStateP 48) vs gs w wg) 21 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 21 (by decide))]; decide
  have a22 : arg (withTabs (satStateP 48) vs gs w wg) 22 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 22 (by decide))]; decide
  have a23 : arg (withTabs (satStateP 48) vs gs w wg) 23 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 23 (by decide))]; decide
  have a24 : arg (withTabs (satStateP 48) vs gs w wg) 24 = 0x4800 := by rw [withTabs_arg _ vs gs w wg (hA 24 (by decide))]; decide
  have a25 : arg (withTabs (satStateP 48) vs gs w wg) 25 = 24 := by rw [withTabs_arg _ vs gs w wg (hA 25 (by decide))]; decide
  have e : argAddr (withTabs (satStateP 48) vs gs w wg) 0 = 0x20004 := show argAddr (satStateP 48) 0 = _ by decide
  have esp : (withTabs (satStateP 48) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (satStateP 48) vs gs w wg).rd = (satStateP 48).rd := rfl
  have wr : (withTabs (satStateP 48) vs gs w wg).wr = (satStateP 48).wr := rfl
  have sy : (withTabs (satStateP 48) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (satStateP 48) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, e, esp, rd, wr, sy, satStateP]
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · exact hk
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem sign_satP64 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 64) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (sspecP vs gs).pre s := by
  have hA : ∀ j < 26, (argAddr (satStateP 64) j).toNat + 4 ≤ 0x300000 := by decide
  have hhH := withTabs_heldH (satStateP 64) vs gs w wg
  have hhG := withTabs_held (satStateP 64) vs gs w wg
  have hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  have hk := withTabsP_key 64 vs gs w wg
  refine ⟨withTabs (satStateP 64) vs gs w wg, ?_⟩
  have a0 : arg (withTabs (satStateP 64) vs gs w wg) 0 = 0x1000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  have a1 : arg (withTabs (satStateP 64) vs gs w wg) 1 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  have a2 : arg (withTabs (satStateP 64) vs gs w wg) 2 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  have a3 : arg (withTabs (satStateP 64) vs gs w wg) 3 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  have a4 : arg (withTabs (satStateP 64) vs gs w wg) 4 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  have a5 : arg (withTabs (satStateP 64) vs gs w wg) 5 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  have a6 : arg (withTabs (satStateP 64) vs gs w wg) 6 = 0x4200 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  have a7 : arg (withTabs (satStateP 64) vs gs w wg) 7 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  have a8 : arg (withTabs (satStateP 64) vs gs w wg) 8 = 0x4300 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  have a9 : arg (withTabs (satStateP 64) vs gs w wg) 9 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  have a10 : arg (withTabs (satStateP 64) vs gs w wg) 10 = 0x3300 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  have a11 : arg (withTabs (satStateP 64) vs gs w wg) 11 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  have a12 : arg (withTabs (satStateP 64) vs gs w wg) 12 = 0x3400 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  have a13 : arg (withTabs (satStateP 64) vs gs w wg) 13 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  have a14 : arg (withTabs (satStateP 64) vs gs w wg) 14 = 0x3500 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  have a15 : arg (withTabs (satStateP 64) vs gs w wg) 15 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  have a16 : arg (withTabs (satStateP 64) vs gs w wg) 16 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 16 (by decide))]; decide
  have a17 : arg (withTabs (satStateP 64) vs gs w wg) 17 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 17 (by decide))]; decide
  have a18 : arg (withTabs (satStateP 64) vs gs w wg) 18 = 0x3600 := by rw [withTabs_arg _ vs gs w wg (hA 18 (by decide))]; decide
  have a19 : arg (withTabs (satStateP 64) vs gs w wg) 19 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 19 (by decide))]; decide
  have a20 : arg (withTabs (satStateP 64) vs gs w wg) 20 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 20 (by decide))]; decide
  have a21 : arg (withTabs (satStateP 64) vs gs w wg) 21 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 21 (by decide))]; decide
  have a22 : arg (withTabs (satStateP 64) vs gs w wg) 22 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 22 (by decide))]; decide
  have a23 : arg (withTabs (satStateP 64) vs gs w wg) 23 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 23 (by decide))]; decide
  have a24 : arg (withTabs (satStateP 64) vs gs w wg) 24 = 0x4800 := by rw [withTabs_arg _ vs gs w wg (hA 24 (by decide))]; decide
  have a25 : arg (withTabs (satStateP 64) vs gs w wg) 25 = 24 := by rw [withTabs_arg _ vs gs w wg (hA 25 (by decide))]; decide
  have e : argAddr (withTabs (satStateP 64) vs gs w wg) 0 = 0x20004 := show argAddr (satStateP 64) 0 = _ by decide
  have esp : (withTabs (satStateP 64) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (satStateP 64) vs gs w wg).rd = (satStateP 64).rd := rfl
  have wr : (withTabs (satStateP 64) vs gs w wg).wr = (satStateP 64).wr := rfl
  have sy : (withTabs (satStateP 64) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (satStateP 64) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, e, esp, rd, wr, sy, satStateP]
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · exact hk
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem sign_satP {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hs : Proof.MdHashTable.X86.Shape w)
    (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (sspecP vs gs).pre s := by
  have hDm := D_mem hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hDm
  rcases hDm with e | e | e | e | e | e
  exacts [sign_satP16 hw hwg e hl, sign_satP20 hw hwg e hl, sign_satP28 hw hwg e hl, sign_satP32 hw hwg e hl,
    sign_satP48 hw hwg e hl, sign_satP64 hw hwg e hl]

end VG.Proof.RsaPss.X86.Sg
