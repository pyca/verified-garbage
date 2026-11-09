module

public import VerifiedGarbage.Proof.RsaPss.Arm.VfBase
public import VerifiedGarbage.Proof.RsaPss.Arm.SgSat
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7 with the tables: the contract is satisfiable

A state with the table of `MdHash` of `w` at `0x300000` and the table of
`Hash` of `wg` at `0x300100` (signing's `withTabs`), and the arguments of a
64-byte modulus, a one-byte `e`, a digest of `w`'s length, a 64-byte
signature, the working space it needs and the precomputed values' 16 words,
the stack arguments at `0x8000`: `verify_sat`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm
open VG.Proof.HashTable (symsOf32 symsOf32_distinct)
open VG.Proof.HashTable.Arm (TVar)
open VG.Proof.MdHashTable.Arm (MVar)

/-- The state but for the tables, for a digest of `D` bytes. -/
def satState (D : Nat) : State where
  gpr r := match r with
    | .r0 => 0x2000 | .r1 => 64 | .r2 => 0x2100 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x30 else
    if a = 0x8004 then BitVec.ofNat 8 D else
    if a = 0x8009 then 0x31 else
    if a = 0x800c then 0x40 else
    if a = 0x801a then 1 else
    if a = 0x801c then 0x20 else
    if a = 0x801d then 8 else
    if a = 0x8021 then 0x70 else
    if a = 0x8024 then 0x10 else
    if a = 0x802a then 0x30 else
    if a = 0x802d then 1 else
    if a = 0x802e then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3000, D⟩, ⟨0x3100, 64⟩, ⟨0x7000, 128⟩, ⟨0x300000, 44⟩, ⟨0x300100, 20⟩,
    ⟨0x8000, 48⟩]
  wr := [⟨0x10000, 2080 * 8⟩]

/-- Its stack arguments. -/
def satArgs (D : Nat) : Nat → BitVec 32
  | 0 => 0x3000 | 1 => BitVec.ofNat 32 D | 2 => 0x3100 | 3 => 64 | 4 => 0 | 5 => 0 | 6 => 0x10000 | 7 => 0x820
  | 8 => 0x7000 | 9 => 16 | 10 => 0x300000 | _ => 0x300100

theorem sat_args (D : Nat) : ∀ j < 12, (stackArgAddr (satState D) j).toNat + 4 ≤ 0x300000 := by
  show ∀ j < 12, (stackArgAddr (satState 0) j).toNat + 4 ≤ 0x300000
  decide

theorem sat_b16 : ∀ j < 12, stackArg (satState 16) j = satArgs 16 j := by decide
theorem sat_b20 : ∀ j < 12, stackArg (satState 20) j = satArgs 20 j := by decide
theorem sat_b28 : ∀ j < 12, stackArg (satState 28) j = satArgs 28 j := by decide
theorem sat_b32 : ∀ j < 12, stackArg (satState 32) j = satArgs 32 j := by decide
theorem sat_b48 : ∀ j < 12, stackArg (satState 48) j = satArgs 48 j := by decide
theorem sat_b64 : ∀ j < 12, stackArg (satState 64) j = satArgs 64 j := by decide

/-- Verification's precondition, from the facts of a state. -/
theorem verify_pre_of {hs ts : List FnTable} {D : Nat} (hD : D ≤ 64) {s : State}
    (hg : s.gpr = (satState D).gpr) (hsp : s.sp = (satState D).sp) (ha : ∀ j < 12, stackArg s j = satArgs D j)
    (hrd : s.rd = (satState D).rd) (hwr : s.wr = (satState D).wr)
    (hH : ∃ T ∈ hs, Abi.tableHeld 32 s.mem 0x300000 (FnTable.words isa s T))
    (hG : ∃ T ∈ ts, Abi.tableHeld 32 s.mem 0x300100 (FnTable.words isa s T))
    (hsy : ((hs.map (fun T : FnTable => T.fns)).flatten ++ ((ts.map (fun T : FnTable => T.fns)).flatten ++ [])).Pairwise
      fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64)
    (hd : Spec.RsaPss.digestLenOk 32 s.mem 0x300000 (BitVec.ofNat 32 D)) :
    (spec hs ts).pre s := by
  have g0 : s.gpr .r0 = 0x2000 := by rw [hg]; rfl
  have g1 : s.gpr .r1 = 64 := by rw [hg]; rfl
  have g2 : s.gpr .r2 = 0x2100 := by rw [hg]; rfl
  have g3 : s.gpr .r3 = 1 := by rw [hg]; rfl
  have sp0 : s.sp = 0x8000 := hsp
  have e0 : stackArgAddr s 0 = 0x8000 := by simp only [stackArgAddr, sp0]; decide
  have hD' : (BitVec.ofNat 32 D).toNat = D := by rw [BitVec.toNat_ofNat]; omega
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs,
    reduceClassify, Loc.val]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide),
    ha 11 (by decide), g0, g1, g2, g3, e0, sp0, hrd, hwr, satArgs]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs,
    reduceClassify, Loc.val]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | with_reducible assumption
    | exact hH
    | exact hG
    | exact hsy
    | exact hd
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (simp only [Spec.RsaPss.publicScratchWords, Spec.Rsa.publicScratchWords, Spec.Rsa.precomputedWords,
        Spec.Rsa.modulusWords]; decide)
    | (rw [hD']; rfl)
    | (rw [hD']; exact Sg.dig_disj hD (Region.disjoint_of_sep (by decide)))
    | (rw [hD']; exact (Sg.dig_disj hD (Region.disjoint_of_sep (by decide))).symm)
    | (rw [hD']; apply Region.disjoint_of_sep; simp [Region.sep]; omega)
    | (rw [hD']; simp; omega)
    | skip

theorem verify_sat_of {mvs : List MVar} {vs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ mvs) (hwg : wg ∈ vs)
    (hl : (allNames mvs vs).length < 2 ^ 24) {D : Nat} (hD : D ≤ 64) (hlen : w.h.G.len = D)
    (hb : ∀ j < 12, stackArg (satState D) j = satArgs D j) :
    (spec (MdHashTable.Arm.tables mvs) (HashTable.Arm.tables vs)).pre (withTabs (satState D) mvs vs w wg) :=
  verify_pre_of hD rfl rfl (fun j hj => (withTabs_arg _ (sat_args D j hj)).trans (hb j hj)) rfl rfl
    ⟨_, List.mem_map_of_mem hw, withTabs_heldH _⟩ ⟨_, List.mem_map_of_mem hwg, withTabs_heldG _⟩
    (by rw [List.append_nil]; exact symsOf32_distinct hl) fun H hH => by
      have e3 : State.addr (0x300000 : BitVec 32) = (0x300000 : Addr) := by decide
      have hheld := withTabs_heldH (satState D) (mvs := mvs) (vs := vs) (w := w) (wg := wg)
      rw [← e3] at hheld
      have hA := MdHashTable.Arm.hashAt_tableOf (p := 0x300000) (by decide)
        (MdHashTable.Arm.held_tableOf (by decide) hheld).2.2.2
      rw [e3] at hA
      rw [hA, Option.some.injEq] at hH
      subst hH
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hlen]

/-- Verification's contract, with the tables of `mvs` and `vs`, is satisfiable. -/
theorem verify_sat {mvs : List MVar} {vs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ mvs) (hwg : wg ∈ vs)
    (hl : (allNames mvs vs).length < 2 ^ 24) :
    ∃ s, (spec (MdHashTable.Arm.tables mvs) (HashTable.Arm.tables vs)).pre s := by
  have hG : w.h.G ∈ Spec.Mgf1.hashes := List.mem_of_getElem? w.idx
  have hlen : w.h.G.len = 16 ∨ w.h.G.len = 20 ∨ w.h.G.len = 28 ∨ w.h.G.len = 32 ∨ w.h.G.len = 48 ∨
      w.h.G.len = 64 := by
    simp only [Spec.Mgf1.hashes, List.mem_cons, List.not_mem_nil, or_false] at hG
    rcases hG with e | e | e | e | e | e | e | e | e | e | e | e | e | e <;> rw [e] <;> decide
  rcases hlen with e | e | e | e | e | e
  · exact ⟨_, verify_sat_of hw hwg hl (by decide) e sat_b16⟩
  · exact ⟨_, verify_sat_of hw hwg hl (by decide) e sat_b20⟩
  · exact ⟨_, verify_sat_of hw hwg hl (by decide) e sat_b28⟩
  · exact ⟨_, verify_sat_of hw hwg hl (by decide) e sat_b32⟩
  · exact ⟨_, verify_sat_of hw hwg hl (by decide) e sat_b48⟩
  · exact ⟨_, verify_sat_of hw hwg hl (by decide) e sat_b64⟩

end VG.Proof.RsaPss.Arm.Vf
