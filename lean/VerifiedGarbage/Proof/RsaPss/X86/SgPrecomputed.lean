module

public import VerifiedGarbage.Proof.RsaPss.X86.Inst
public import VerifiedGarbage.Proof.Framework.X86.AppendSlice
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_rsa_pss_sign_precomputed` on x86

`vg_rsa_pss_sign`'s code, which ignores the key's precomputed values `pre`
(`Spec/Rsa/PrivatePrecompute.lean` lets an implementation ignore them),
proven against `vg_rsa_pss_sign_precomputed`'s contract from its own
(`verified_withSlice_tables`), with a state that meets it (`preSat`): that of
`SgSat.lean`, with `p`, `q`, `dP`, `dQ` and `qInv` of 32 bytes and a real key
(`Proof/Rsa/PreKey.lean`).
-/

@[expose] public section
namespace VG.Proof.RsaPss.X86.Sg
open VG
open VG.X86 hiding frameBytes
open VG.Proof.MdHashTable.X86 (MVar)
open VG.Proof.HashTable.X86 (TVar)
open VG.Proof.HashTable (symsOf32 symsOf32_distinct2)
open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl)

/-- The contract, with the tables of `vs` and `gs`. -/
abbrev pspec (vs : List MVar) (gs : List TVar) : Contract isa :=
  Spec.RsaPss.signPrecomputedMdTableContract
    (abi.withTables Spec.RsaPss.signPrecomputedMdTableSig
      [("hash", Proof.MdHashTable.X86.tables vs), ("mgf1", Proof.HashTable.X86.tables gs)]) stackBytes

/-! ## A state that meets the contract -/

theorem putWs_byte {a : Addr} : ∀ {ws : List (BitVec 32)} {m : Mem} {p : Addr},
    a.toNat < p.toNat → p.toNat + 4 * ws.length < 2 ^ 64 → putWs m p ws a = m a
  | [], _, _, _, _ => rfl
  | w :: ws, m, p, ha, hp => by
    have e : (p + 4).toNat = p.toNat + 4 := by
      rw [BitVec.toNat_add]; simp only [List.length_cons] at hp; simp; omega
    simp only [putWs]
    rw [putWs_byte (by rw [e]; omega) (by rw [e]; simp only [List.length_cons] at hp; omega)]
    simp only [Mem.writeW, Mem.write]
    split
    · rename_i hh
      rw [BitVec.toNat_sub] at hh
      simp only [List.length_cons] at hp
      omega
    · rfl

/-- The arguments of `preState D`; the key (`keyMem`) has `n` at `0x2000`,
`p` at `0x4200`, `q` at `0x4300` and `pre` at `0x4800`. -/
def preArgs (D : Nat) : List Nat := [0x1000, 64, 0x2000, 64, 0x2100, 1, 0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0x3000, D, 0x3600, 0, 0x10000, 0x820, 0x300000, 0x300100, 0x4800, 24]

/-- The memory of `preState D`: the arguments on the stack from `0x20004`,
and the key. -/
def preMem (D : Nat) (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x20004 i && Nat.blt i 0x2006c then
    BitVec.ofNat 8 ((preArgs D).getD ((i - 0x20004) / 4) 0 / 256 ^ ((i - 0x20004) % 4))
  else bif keyIn i then keyMem a else 0

/-- The state, but for the tables, for a digest of `D` bytes. -/
def preState (D : Nat) : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := preMem D
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩, ⟨0x4600, 32⟩,
    ⟨0x3000, D⟩, ⟨0x3600, 0⟩, ⟨0x4800, 192⟩, ⟨0x300000, 44⟩, ⟨0x300100, 44⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x10000, 2080 * 8⟩, ⟨0x20004, 104⟩]

theorem preState_keyIn (D : Nat) (a : Addr) (ha : keyIn a.toNat = true) : (preState D).mem a = keyMem a := by
  have hs : (Nat.ble 0x20004 a.toNat && Nat.blt a.toNat 0x2006c) = false := by
    simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha
    refine Bool.eq_false_iff.mpr fun h => ?_
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    omega
  show (bif _ then _ else _) = _
  rw [hs, Bool.cond_false, ha, Bool.cond_true]

theorem withTabs_key (s : State) (vs : List MVar) (gs : List TVar) (w : MVar) (wg : TVar)
    (h : ∀ a : Addr, keyIn a.toNat = true → s.mem a = keyMem a) :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt (withTabs s vs gs w wg).mem 0x2000 64)
      (Spec.Rsa.bytesAt (withTabs s vs gs w wg).mem 0x4200 32) (Spec.Rsa.bytesAt (withTabs s vs gs w wg).mem 0x4300 32) =
        some (Spec.Rsa.wordsAt (withTabs s vs gs w wg).mem 0x4800 24) := by
  refine key_pre_of fun a ha => ?_
  have hlt : a.toNat < 0x300000 := by
    simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha; omega
  simp only [withTabs]
  rw [putWs_byte (by simp; omega) (by simp [FnTable.words, Proof.HashTable.X86.tableOf, Proof.MdHashTable.X86.tableOf,
      Spec.MdHashTable.dataOf, Spec.HashTable.dataOf]),
    putWs_byte (by simp; omega) (by simp [FnTable.words, Proof.MdHashTable.X86.tableOf, Spec.MdHashTable.dataOf,
      Spec.HashTable.dataOf])]
  exact h a ha

theorem preSat16 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 16) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (pspec vs gs).pre s := by
  have hA : ∀ j < 26, (argAddr (preState 16) j).toNat + 4 ≤ 0x300000 := by decide
  have hhH := withTabs_heldH (preState 16) vs gs w wg
  have hhG := withTabs_held (preState 16) vs gs w wg
  have hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  have hK := withTabs_key (preState 16) vs gs w wg (preState_keyIn 16)
  refine ⟨withTabs (preState 16) vs gs w wg, ?_⟩
  have a0 : arg (withTabs (preState 16) vs gs w wg) 0 = 0x1000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  have a1 : arg (withTabs (preState 16) vs gs w wg) 1 = 64 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  have a2 : arg (withTabs (preState 16) vs gs w wg) 2 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  have a3 : arg (withTabs (preState 16) vs gs w wg) 3 = 64 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  have a4 : arg (withTabs (preState 16) vs gs w wg) 4 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  have a5 : arg (withTabs (preState 16) vs gs w wg) 5 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  have a6 : arg (withTabs (preState 16) vs gs w wg) 6 = 0x4200 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  have a7 : arg (withTabs (preState 16) vs gs w wg) 7 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  have a8 : arg (withTabs (preState 16) vs gs w wg) 8 = 0x4300 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  have a9 : arg (withTabs (preState 16) vs gs w wg) 9 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  have a10 : arg (withTabs (preState 16) vs gs w wg) 10 = 0x4400 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  have a11 : arg (withTabs (preState 16) vs gs w wg) 11 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  have a12 : arg (withTabs (preState 16) vs gs w wg) 12 = 0x4500 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  have a13 : arg (withTabs (preState 16) vs gs w wg) 13 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  have a14 : arg (withTabs (preState 16) vs gs w wg) 14 = 0x4600 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  have a15 : arg (withTabs (preState 16) vs gs w wg) 15 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  have a16 : arg (withTabs (preState 16) vs gs w wg) 16 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 16 (by decide))]; decide
  have a17 : arg (withTabs (preState 16) vs gs w wg) 17 = 16 := by rw [withTabs_arg _ vs gs w wg (hA 17 (by decide))]; decide
  have a18 : arg (withTabs (preState 16) vs gs w wg) 18 = 0x3600 := by rw [withTabs_arg _ vs gs w wg (hA 18 (by decide))]; decide
  have a19 : arg (withTabs (preState 16) vs gs w wg) 19 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 19 (by decide))]; decide
  have a20 : arg (withTabs (preState 16) vs gs w wg) 20 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 20 (by decide))]; decide
  have a21 : arg (withTabs (preState 16) vs gs w wg) 21 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 21 (by decide))]; decide
  have a22 : arg (withTabs (preState 16) vs gs w wg) 22 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 22 (by decide))]; decide
  have a23 : arg (withTabs (preState 16) vs gs w wg) 23 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 23 (by decide))]; decide
  have a24 : arg (withTabs (preState 16) vs gs w wg) 24 = 0x4800 := by rw [withTabs_arg _ vs gs w wg (hA 24 (by decide))]; decide
  have a25 : arg (withTabs (preState 16) vs gs w wg) 25 = 24 := by rw [withTabs_arg _ vs gs w wg (hA 25 (by decide))]; decide
  have e : argAddr (withTabs (preState 16) vs gs w wg) 0 = 0x20004 := show argAddr (preState 16) 0 = _ by decide
  have esp : (withTabs (preState 16) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (preState 16) vs gs w wg).rd = (preState 16).rd := rfl
  have wr : (withTabs (preState 16) vs gs w wg).wr = (preState 16).wr := rfl
  have sy : (withTabs (preState 16) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (preState 16) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes, stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, e, esp, rd, wr, sy, preState]
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try (exact hK)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem preSat20 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 20) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (pspec vs gs).pre s := by
  have hA : ∀ j < 26, (argAddr (preState 20) j).toNat + 4 ≤ 0x300000 := by decide
  have hhH := withTabs_heldH (preState 20) vs gs w wg
  have hhG := withTabs_held (preState 20) vs gs w wg
  have hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  have hK := withTabs_key (preState 20) vs gs w wg (preState_keyIn 20)
  refine ⟨withTabs (preState 20) vs gs w wg, ?_⟩
  have a0 : arg (withTabs (preState 20) vs gs w wg) 0 = 0x1000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  have a1 : arg (withTabs (preState 20) vs gs w wg) 1 = 64 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  have a2 : arg (withTabs (preState 20) vs gs w wg) 2 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  have a3 : arg (withTabs (preState 20) vs gs w wg) 3 = 64 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  have a4 : arg (withTabs (preState 20) vs gs w wg) 4 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  have a5 : arg (withTabs (preState 20) vs gs w wg) 5 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  have a6 : arg (withTabs (preState 20) vs gs w wg) 6 = 0x4200 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  have a7 : arg (withTabs (preState 20) vs gs w wg) 7 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  have a8 : arg (withTabs (preState 20) vs gs w wg) 8 = 0x4300 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  have a9 : arg (withTabs (preState 20) vs gs w wg) 9 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  have a10 : arg (withTabs (preState 20) vs gs w wg) 10 = 0x4400 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  have a11 : arg (withTabs (preState 20) vs gs w wg) 11 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  have a12 : arg (withTabs (preState 20) vs gs w wg) 12 = 0x4500 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  have a13 : arg (withTabs (preState 20) vs gs w wg) 13 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  have a14 : arg (withTabs (preState 20) vs gs w wg) 14 = 0x4600 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  have a15 : arg (withTabs (preState 20) vs gs w wg) 15 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  have a16 : arg (withTabs (preState 20) vs gs w wg) 16 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 16 (by decide))]; decide
  have a17 : arg (withTabs (preState 20) vs gs w wg) 17 = 20 := by rw [withTabs_arg _ vs gs w wg (hA 17 (by decide))]; decide
  have a18 : arg (withTabs (preState 20) vs gs w wg) 18 = 0x3600 := by rw [withTabs_arg _ vs gs w wg (hA 18 (by decide))]; decide
  have a19 : arg (withTabs (preState 20) vs gs w wg) 19 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 19 (by decide))]; decide
  have a20 : arg (withTabs (preState 20) vs gs w wg) 20 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 20 (by decide))]; decide
  have a21 : arg (withTabs (preState 20) vs gs w wg) 21 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 21 (by decide))]; decide
  have a22 : arg (withTabs (preState 20) vs gs w wg) 22 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 22 (by decide))]; decide
  have a23 : arg (withTabs (preState 20) vs gs w wg) 23 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 23 (by decide))]; decide
  have a24 : arg (withTabs (preState 20) vs gs w wg) 24 = 0x4800 := by rw [withTabs_arg _ vs gs w wg (hA 24 (by decide))]; decide
  have a25 : arg (withTabs (preState 20) vs gs w wg) 25 = 24 := by rw [withTabs_arg _ vs gs w wg (hA 25 (by decide))]; decide
  have e : argAddr (withTabs (preState 20) vs gs w wg) 0 = 0x20004 := show argAddr (preState 20) 0 = _ by decide
  have esp : (withTabs (preState 20) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (preState 20) vs gs w wg).rd = (preState 20).rd := rfl
  have wr : (withTabs (preState 20) vs gs w wg).wr = (preState 20).wr := rfl
  have sy : (withTabs (preState 20) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (preState 20) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes, stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, e, esp, rd, wr, sy, preState]
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try (exact hK)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem preSat28 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 28) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (pspec vs gs).pre s := by
  have hA : ∀ j < 26, (argAddr (preState 28) j).toNat + 4 ≤ 0x300000 := by decide
  have hhH := withTabs_heldH (preState 28) vs gs w wg
  have hhG := withTabs_held (preState 28) vs gs w wg
  have hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  have hK := withTabs_key (preState 28) vs gs w wg (preState_keyIn 28)
  refine ⟨withTabs (preState 28) vs gs w wg, ?_⟩
  have a0 : arg (withTabs (preState 28) vs gs w wg) 0 = 0x1000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  have a1 : arg (withTabs (preState 28) vs gs w wg) 1 = 64 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  have a2 : arg (withTabs (preState 28) vs gs w wg) 2 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  have a3 : arg (withTabs (preState 28) vs gs w wg) 3 = 64 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  have a4 : arg (withTabs (preState 28) vs gs w wg) 4 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  have a5 : arg (withTabs (preState 28) vs gs w wg) 5 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  have a6 : arg (withTabs (preState 28) vs gs w wg) 6 = 0x4200 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  have a7 : arg (withTabs (preState 28) vs gs w wg) 7 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  have a8 : arg (withTabs (preState 28) vs gs w wg) 8 = 0x4300 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  have a9 : arg (withTabs (preState 28) vs gs w wg) 9 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  have a10 : arg (withTabs (preState 28) vs gs w wg) 10 = 0x4400 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  have a11 : arg (withTabs (preState 28) vs gs w wg) 11 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  have a12 : arg (withTabs (preState 28) vs gs w wg) 12 = 0x4500 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  have a13 : arg (withTabs (preState 28) vs gs w wg) 13 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  have a14 : arg (withTabs (preState 28) vs gs w wg) 14 = 0x4600 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  have a15 : arg (withTabs (preState 28) vs gs w wg) 15 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  have a16 : arg (withTabs (preState 28) vs gs w wg) 16 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 16 (by decide))]; decide
  have a17 : arg (withTabs (preState 28) vs gs w wg) 17 = 28 := by rw [withTabs_arg _ vs gs w wg (hA 17 (by decide))]; decide
  have a18 : arg (withTabs (preState 28) vs gs w wg) 18 = 0x3600 := by rw [withTabs_arg _ vs gs w wg (hA 18 (by decide))]; decide
  have a19 : arg (withTabs (preState 28) vs gs w wg) 19 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 19 (by decide))]; decide
  have a20 : arg (withTabs (preState 28) vs gs w wg) 20 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 20 (by decide))]; decide
  have a21 : arg (withTabs (preState 28) vs gs w wg) 21 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 21 (by decide))]; decide
  have a22 : arg (withTabs (preState 28) vs gs w wg) 22 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 22 (by decide))]; decide
  have a23 : arg (withTabs (preState 28) vs gs w wg) 23 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 23 (by decide))]; decide
  have a24 : arg (withTabs (preState 28) vs gs w wg) 24 = 0x4800 := by rw [withTabs_arg _ vs gs w wg (hA 24 (by decide))]; decide
  have a25 : arg (withTabs (preState 28) vs gs w wg) 25 = 24 := by rw [withTabs_arg _ vs gs w wg (hA 25 (by decide))]; decide
  have e : argAddr (withTabs (preState 28) vs gs w wg) 0 = 0x20004 := show argAddr (preState 28) 0 = _ by decide
  have esp : (withTabs (preState 28) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (preState 28) vs gs w wg).rd = (preState 28).rd := rfl
  have wr : (withTabs (preState 28) vs gs w wg).wr = (preState 28).wr := rfl
  have sy : (withTabs (preState 28) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (preState 28) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes, stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, e, esp, rd, wr, sy, preState]
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try (exact hK)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem preSat32 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 32) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (pspec vs gs).pre s := by
  have hA : ∀ j < 26, (argAddr (preState 32) j).toNat + 4 ≤ 0x300000 := by decide
  have hhH := withTabs_heldH (preState 32) vs gs w wg
  have hhG := withTabs_held (preState 32) vs gs w wg
  have hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  have hK := withTabs_key (preState 32) vs gs w wg (preState_keyIn 32)
  refine ⟨withTabs (preState 32) vs gs w wg, ?_⟩
  have a0 : arg (withTabs (preState 32) vs gs w wg) 0 = 0x1000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  have a1 : arg (withTabs (preState 32) vs gs w wg) 1 = 64 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  have a2 : arg (withTabs (preState 32) vs gs w wg) 2 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  have a3 : arg (withTabs (preState 32) vs gs w wg) 3 = 64 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  have a4 : arg (withTabs (preState 32) vs gs w wg) 4 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  have a5 : arg (withTabs (preState 32) vs gs w wg) 5 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  have a6 : arg (withTabs (preState 32) vs gs w wg) 6 = 0x4200 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  have a7 : arg (withTabs (preState 32) vs gs w wg) 7 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  have a8 : arg (withTabs (preState 32) vs gs w wg) 8 = 0x4300 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  have a9 : arg (withTabs (preState 32) vs gs w wg) 9 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  have a10 : arg (withTabs (preState 32) vs gs w wg) 10 = 0x4400 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  have a11 : arg (withTabs (preState 32) vs gs w wg) 11 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  have a12 : arg (withTabs (preState 32) vs gs w wg) 12 = 0x4500 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  have a13 : arg (withTabs (preState 32) vs gs w wg) 13 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  have a14 : arg (withTabs (preState 32) vs gs w wg) 14 = 0x4600 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  have a15 : arg (withTabs (preState 32) vs gs w wg) 15 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  have a16 : arg (withTabs (preState 32) vs gs w wg) 16 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 16 (by decide))]; decide
  have a17 : arg (withTabs (preState 32) vs gs w wg) 17 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 17 (by decide))]; decide
  have a18 : arg (withTabs (preState 32) vs gs w wg) 18 = 0x3600 := by rw [withTabs_arg _ vs gs w wg (hA 18 (by decide))]; decide
  have a19 : arg (withTabs (preState 32) vs gs w wg) 19 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 19 (by decide))]; decide
  have a20 : arg (withTabs (preState 32) vs gs w wg) 20 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 20 (by decide))]; decide
  have a21 : arg (withTabs (preState 32) vs gs w wg) 21 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 21 (by decide))]; decide
  have a22 : arg (withTabs (preState 32) vs gs w wg) 22 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 22 (by decide))]; decide
  have a23 : arg (withTabs (preState 32) vs gs w wg) 23 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 23 (by decide))]; decide
  have a24 : arg (withTabs (preState 32) vs gs w wg) 24 = 0x4800 := by rw [withTabs_arg _ vs gs w wg (hA 24 (by decide))]; decide
  have a25 : arg (withTabs (preState 32) vs gs w wg) 25 = 24 := by rw [withTabs_arg _ vs gs w wg (hA 25 (by decide))]; decide
  have e : argAddr (withTabs (preState 32) vs gs w wg) 0 = 0x20004 := show argAddr (preState 32) 0 = _ by decide
  have esp : (withTabs (preState 32) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (preState 32) vs gs w wg).rd = (preState 32).rd := rfl
  have wr : (withTabs (preState 32) vs gs w wg).wr = (preState 32).wr := rfl
  have sy : (withTabs (preState 32) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (preState 32) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes, stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, e, esp, rd, wr, sy, preState]
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try (exact hK)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem preSat48 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 48) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (pspec vs gs).pre s := by
  have hA : ∀ j < 26, (argAddr (preState 48) j).toNat + 4 ≤ 0x300000 := by decide
  have hhH := withTabs_heldH (preState 48) vs gs w wg
  have hhG := withTabs_held (preState 48) vs gs w wg
  have hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  have hK := withTabs_key (preState 48) vs gs w wg (preState_keyIn 48)
  refine ⟨withTabs (preState 48) vs gs w wg, ?_⟩
  have a0 : arg (withTabs (preState 48) vs gs w wg) 0 = 0x1000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  have a1 : arg (withTabs (preState 48) vs gs w wg) 1 = 64 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  have a2 : arg (withTabs (preState 48) vs gs w wg) 2 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  have a3 : arg (withTabs (preState 48) vs gs w wg) 3 = 64 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  have a4 : arg (withTabs (preState 48) vs gs w wg) 4 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  have a5 : arg (withTabs (preState 48) vs gs w wg) 5 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  have a6 : arg (withTabs (preState 48) vs gs w wg) 6 = 0x4200 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  have a7 : arg (withTabs (preState 48) vs gs w wg) 7 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  have a8 : arg (withTabs (preState 48) vs gs w wg) 8 = 0x4300 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  have a9 : arg (withTabs (preState 48) vs gs w wg) 9 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  have a10 : arg (withTabs (preState 48) vs gs w wg) 10 = 0x4400 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  have a11 : arg (withTabs (preState 48) vs gs w wg) 11 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  have a12 : arg (withTabs (preState 48) vs gs w wg) 12 = 0x4500 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  have a13 : arg (withTabs (preState 48) vs gs w wg) 13 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  have a14 : arg (withTabs (preState 48) vs gs w wg) 14 = 0x4600 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  have a15 : arg (withTabs (preState 48) vs gs w wg) 15 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  have a16 : arg (withTabs (preState 48) vs gs w wg) 16 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 16 (by decide))]; decide
  have a17 : arg (withTabs (preState 48) vs gs w wg) 17 = 48 := by rw [withTabs_arg _ vs gs w wg (hA 17 (by decide))]; decide
  have a18 : arg (withTabs (preState 48) vs gs w wg) 18 = 0x3600 := by rw [withTabs_arg _ vs gs w wg (hA 18 (by decide))]; decide
  have a19 : arg (withTabs (preState 48) vs gs w wg) 19 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 19 (by decide))]; decide
  have a20 : arg (withTabs (preState 48) vs gs w wg) 20 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 20 (by decide))]; decide
  have a21 : arg (withTabs (preState 48) vs gs w wg) 21 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 21 (by decide))]; decide
  have a22 : arg (withTabs (preState 48) vs gs w wg) 22 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 22 (by decide))]; decide
  have a23 : arg (withTabs (preState 48) vs gs w wg) 23 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 23 (by decide))]; decide
  have a24 : arg (withTabs (preState 48) vs gs w wg) 24 = 0x4800 := by rw [withTabs_arg _ vs gs w wg (hA 24 (by decide))]; decide
  have a25 : arg (withTabs (preState 48) vs gs w wg) 25 = 24 := by rw [withTabs_arg _ vs gs w wg (hA 25 (by decide))]; decide
  have e : argAddr (withTabs (preState 48) vs gs w wg) 0 = 0x20004 := show argAddr (preState 48) 0 = _ by decide
  have esp : (withTabs (preState 48) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (preState 48) vs gs w wg).rd = (preState 48).rd := rfl
  have wr : (withTabs (preState 48) vs gs w wg).wr = (preState 48).wr := rfl
  have sy : (withTabs (preState 48) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (preState 48) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes, stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, e, esp, rd, wr, sy, preState]
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try (exact hK)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem preSat64 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 64) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (pspec vs gs).pre s := by
  have hA : ∀ j < 26, (argAddr (preState 64) j).toNat + 4 ≤ 0x300000 := by decide
  have hhH := withTabs_heldH (preState 64) vs gs w wg
  have hhG := withTabs_held (preState 64) vs gs w wg
  have hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  have hK := withTabs_key (preState 64) vs gs w wg (preState_keyIn 64)
  refine ⟨withTabs (preState 64) vs gs w wg, ?_⟩
  have a0 : arg (withTabs (preState 64) vs gs w wg) 0 = 0x1000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  have a1 : arg (withTabs (preState 64) vs gs w wg) 1 = 64 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  have a2 : arg (withTabs (preState 64) vs gs w wg) 2 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  have a3 : arg (withTabs (preState 64) vs gs w wg) 3 = 64 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  have a4 : arg (withTabs (preState 64) vs gs w wg) 4 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  have a5 : arg (withTabs (preState 64) vs gs w wg) 5 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  have a6 : arg (withTabs (preState 64) vs gs w wg) 6 = 0x4200 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  have a7 : arg (withTabs (preState 64) vs gs w wg) 7 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  have a8 : arg (withTabs (preState 64) vs gs w wg) 8 = 0x4300 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  have a9 : arg (withTabs (preState 64) vs gs w wg) 9 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  have a10 : arg (withTabs (preState 64) vs gs w wg) 10 = 0x4400 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  have a11 : arg (withTabs (preState 64) vs gs w wg) 11 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  have a12 : arg (withTabs (preState 64) vs gs w wg) 12 = 0x4500 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  have a13 : arg (withTabs (preState 64) vs gs w wg) 13 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  have a14 : arg (withTabs (preState 64) vs gs w wg) 14 = 0x4600 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  have a15 : arg (withTabs (preState 64) vs gs w wg) 15 = 32 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  have a16 : arg (withTabs (preState 64) vs gs w wg) 16 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 16 (by decide))]; decide
  have a17 : arg (withTabs (preState 64) vs gs w wg) 17 = 64 := by rw [withTabs_arg _ vs gs w wg (hA 17 (by decide))]; decide
  have a18 : arg (withTabs (preState 64) vs gs w wg) 18 = 0x3600 := by rw [withTabs_arg _ vs gs w wg (hA 18 (by decide))]; decide
  have a19 : arg (withTabs (preState 64) vs gs w wg) 19 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 19 (by decide))]; decide
  have a20 : arg (withTabs (preState 64) vs gs w wg) 20 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 20 (by decide))]; decide
  have a21 : arg (withTabs (preState 64) vs gs w wg) 21 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 21 (by decide))]; decide
  have a22 : arg (withTabs (preState 64) vs gs w wg) 22 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 22 (by decide))]; decide
  have a23 : arg (withTabs (preState 64) vs gs w wg) 23 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 23 (by decide))]; decide
  have a24 : arg (withTabs (preState 64) vs gs w wg) 24 = 0x4800 := by rw [withTabs_arg _ vs gs w wg (hA 24 (by decide))]; decide
  have a25 : arg (withTabs (preState 64) vs gs w wg) 25 = 24 := by rw [withTabs_arg _ vs gs w wg (hA 25 (by decide))]; decide
  have e : argAddr (withTabs (preState 64) vs gs w wg) 0 = 0x20004 := show argAddr (preState 64) 0 = _ by decide
  have esp : (withTabs (preState 64) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (preState 64) vs gs w wg).rd = (preState 64).rd := rfl
  have wr : (withTabs (preState 64) vs gs w wg).wr = (preState 64).wr := rfl
  have sy : (withTabs (preState 64) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (preState 64) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes, stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, e, esp, rd, wr, sy, preState]
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try (exact hK)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem preSat {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hs : Proof.MdHashTable.X86.Shape w)
    (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (pspec vs gs).pre s := by
  have hDm := D_mem hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hDm
  rcases hDm with e | e | e | e | e | e
  exacts [preSat16 hw hwg e hl, preSat20 hw hwg e hl, preSat28 hw hwg e hl, preSat32 hw hwg e hl, preSat48 hw hwg e hl, preSat64 hw hwg e hl]

/-! ## The code -/

theorem wordVals_eq (s : State) : wordVals 24 s = [argVal s 32 0, argVal s 32 1, argVal s 32 2, argVal s 32 3, argVal s 32 4, argVal s 32 5, argVal s 32 6, argVal s 32 7, argVal s 32 8, argVal s 32 9, argVal s 32 10, argVal s 32 11, argVal s 32 12, argVal s 32 13, argVal s 32 14, argVal s 32 15, argVal s 32 16, argVal s 32 17, argVal s 32 18, argVal s 32 19, argVal s 32 20, argVal s 32 21, argVal s 32 22, argVal s 32 23] := rfl

/-- `Spec.RsaPss.signMdTableSig.words 32`. -/
abbrev sigWords : List ArgWord :=
  [.addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .addr]

theorem signPrecomputed_verified {vs : List MVar} {gs : List TVar} (hok : OK vs gs) (c : CrtImpl) :
    Verified target (signCode vs gs c) (pspec vs gs) := by
  refine verified_withSlice_tables (sig := Spec.RsaPss.signMdTableSig) (nm := "pre") (e := .u64) (ln := "pre_len")
    (fun u hu => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> exact ⟨_, rfl, by decide⟩)
    (by decide) (by decide) (Proof.RsaPss.X86.sign_ok vs gs hok c) ?_ ?_ ?_
    (let ⟨_, hw, _, hwg, hs⟩ := ok_sat hok; preSat hw hwg hs hok.2.2.2.2.2)
  · intro s h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -, -, h13⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  · intro s m' v hp hq
    exact hq
  · intro s₁ s₂ _ _ hpo h
    have e3 := hpo 3 (by decide)
    have e5 := hpo 5 (by decide)
    have hl : (Spec.RsaPss.signMdTableSig.words 32).length = 24 := by decide
    simp only [hl, sliceVals, wordVals_eq, List.cons_append, List.nil_append] at h e3 e5 ⊢
    change Curry.apply (α := Mem → List Nat) (sigWords ++ [.addr, .int 32]) _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) (sigWords ++ [.addr, .int 32]) _ _ s₂.mem at h
    change Curry.apply (α := Mem → List Nat) sigWords _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) sigWords _ _ s₂.mem
    change (argVal s₁ 32 3).setWidth 32 = (argVal s₂ 32 3).setWidth 32 at e3
    change (argVal s₁ 32 5).setWidth 32 = (argVal s₂ 32 5).setWidth 32 at e5
    dsimp only [sigWords, List.cons_append, List.nil_append, Curry.apply, ArgWord.ofRaw] at h ⊢
    refine List.append_inj_left h ?_
    simp only [List.length_map, List.length_append, Proof.Rsa.bytesAt_length', e3, e5]

end VG.Proof.RsaPss.X86.Sg
