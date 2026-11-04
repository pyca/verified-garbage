module

public import VerifiedGarbage.Proof.RsaOaep.Arm.EncBase
public import VerifiedGarbage.Proof.HashTable.Arm
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-OAEP encryption with a precomputed public key on ARMv7: the contract is satisfiable

A state that meets `encryptTablesContract` (`encrypt_sat`), with both hash
functions the table of any `w` of `vs`: a modulus of 64 bytes, `e` of one
byte, an empty label and message, the seed of the hash function's digest
length, the working space it needs, the precomputed values' 16 words, the
stack arguments at `0x8000`, and the table, both arguments, at `0x300000`
(`withTable`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Enc

open VG VG.Arm
open VG.Proof.HashTable.Arm (TVar tables tableOf names withTable withTable_held withTable_below hashAt_tableOf
  held_tableOf)
open VG.Proof.HashTable (symsOf32_distinct2)

/-- The state, for a seed of `D` bytes, but for the table. -/
def satState (D : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x2000 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x21 else
    if a = 0x8004 then 1 else
    if a = 0x8009 then 0x30 else
    if a = 0x8011 then 0x31 else
    if a = 0x8019 then 0x32 else
    if a = 0x801c then BitVec.ofNat 8 D else
    if a = 0x8022 then 1 else
    if a = 0x8024 then 0x20 else
    if a = 0x8025 then 8 else
    if a = 0x8029 then 0x70 else
    if a = 0x802c then 0x10 else
    if a = 0x8032 then 0x30 else
    if a = 0x8036 then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, D⟩, ⟨0x7000, 128⟩, ⟨0x300000, 20⟩,
    ⟨0x300000, 20⟩, ⟨0x8000, 56⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x10000, 2080 * 8⟩]

theorem encrypt_sat {vs : List TVar} {w : TVar} (hw : w ∈ vs) (hl : (names vs).length < 2 ^ 24) :
    ∃ s, (spec (tables vs)).pre s := by
  have hha : ∀ s : State, Spec.HashTable.hashAt 32 (withTable s vs w).mem (State.addr (0x300000 : BitVec 32)) =
      some w.g.G := fun s => hashAt_tableOf (by decide) (held_tableOf (by decide) (withTable_held s vs w)).2.1
  have hl' : w.g.G.len ∈ Impl.RsaOaep.Arm.lens := w.g.glen ▸ w.g.lens
  generalize hDd : w.g.G.len = D at hl'
  refine ⟨withTable (satState D) vs w, ?_⟩
  have hA : ∀ D ∈ Impl.RsaOaep.Arm.lens, ∀ j < 14, (stackArgAddr (satState D) j).toNat + 4 ≤ 0x300000 := by decide
  have hA' := hA D hl'
  have a0 : stackArg (withTable (satState D) vs w) 0 = 0x2100 :=
    (withTable_below _ _ _ (hA' 0 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 0 = 0x2100 by decide) D hl')
  have a1 : stackArg (withTable (satState D) vs w) 1 = 1 :=
    (withTable_below _ _ _ (hA' 1 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 1 = 1 by decide) D hl')
  have a2 : stackArg (withTable (satState D) vs w) 2 = 0x3000 :=
    (withTable_below _ _ _ (hA' 2 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 2 = 0x3000 by decide) D hl')
  have a3 : stackArg (withTable (satState D) vs w) 3 = 0 :=
    (withTable_below _ _ _ (hA' 3 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 3 = 0 by decide) D hl')
  have a4 : stackArg (withTable (satState D) vs w) 4 = 0x3100 :=
    (withTable_below _ _ _ (hA' 4 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 4 = 0x3100 by decide) D hl')
  have a5 : stackArg (withTable (satState D) vs w) 5 = 0 :=
    (withTable_below _ _ _ (hA' 5 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 5 = 0 by decide) D hl')
  have a6 : stackArg (withTable (satState D) vs w) 6 = 0x3200 :=
    (withTable_below _ _ _ (hA' 6 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 6 = 0x3200 by decide) D hl')
  have a7 : stackArg (withTable (satState D) vs w) 7 = BitVec.ofNat 32 D :=
    (withTable_below _ _ _ (hA' 7 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 7 = BitVec.ofNat 32 D by decide) D hl')
  have a8 : stackArg (withTable (satState D) vs w) 8 = 0x10000 :=
    (withTable_below _ _ _ (hA' 8 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 8 = 0x10000 by decide) D hl')
  have a9 : stackArg (withTable (satState D) vs w) 9 = 0x820 :=
    (withTable_below _ _ _ (hA' 9 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 9 = 0x820 by decide) D hl')
  have a10 : stackArg (withTable (satState D) vs w) 10 = 0x7000 :=
    (withTable_below _ _ _ (hA' 10 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 10 = 0x7000 by decide) D hl')
  have a11 : stackArg (withTable (satState D) vs w) 11 = 16 :=
    (withTable_below _ _ _ (hA' 11 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 11 = 16 by decide) D hl')
  have a12 : stackArg (withTable (satState D) vs w) 12 = 0x300000 :=
    (withTable_below _ _ _ (hA' 12 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 12 = 0x300000 by decide) D hl')
  have a13 : stackArg (withTable (satState D) vs w) 13 = 0x300000 :=
    (withTable_below _ _ _ (hA' 13 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 13 = 0x300000 by decide) D hl')
  have e : stackArgAddr (withTable (satState D) vs w) 0 = 0x8000 := rfl
  have hha' := hha (satState D)
  simp only [Impl.RsaOaep.Arm.lens, List.mem_cons, List.not_mem_nil, or_false] at hl'
  rcases hl' with rfl | rfl | rfl | rfl | rfl
  all_goals
    sig_pre [Spec.RsaOaep.encryptTablesContract, Spec.RsaOaep.encryptTablesSig, Spec.RsaOaep.seedLenOk,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val]
    simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
      a12, a13, e]
    sig_pre [Spec.RsaOaep.encryptTablesContract, Spec.RsaOaep.encryptTablesSig, Spec.RsaOaep.seedLenOk,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val]
    sig_and_intros
    all_goals first
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)
      | exact ⟨tableOf w, List.mem_map_of_mem hw, withTable_held _ _ _⟩
      | (intro H' hH'
         obtain rfl := Option.some.inj (hha'.symm.trans hH')
         rw [hDd]; rfl)
      | (rw [List.append_eq, List.append_eq, List.append_nil]; exact symsOf32_distinct2 hl)
      | (simp only [Spec.Rsa.lenValid]; decide)

end VG.Proof.RsaOaep.Arm.Enc
