module

public import VerifiedGarbage.Proof.RsaOaep.Arm.EncBase
public import VerifiedGarbage.Proof.HashTable.Arm
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-OAEP encryption with a precomputed public key on ARMv7: the contract is satisfiable

A state that meets `encryptTableContract` (`encrypt_sat`), for each hash
function ARMv7 registers RSAES-OAEP with, with MGF1's the table of any `w`
of `vs`: a modulus of 64 bytes, `e` of one byte, an empty label and
message, the seed, the working space it needs, the precomputed values' 16
words, the stack arguments at `0x8000`, and the table at `0x300000`
(`withTable`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Enc

open VG VG.Arm
open VG.Proof.HashTable.Arm (TVar tables tableOf names withTable withTable_held withTable_below)
open VG.Proof.HashTable (symsOf32_distinct)

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
    if a = 0x801e then 1 else
    if a = 0x8020 then 0x20 else
    if a = 0x8021 then 8 else
    if a = 0x8025 then 0x70 else
    if a = 0x8028 then 0x10 else
    if a = 0x802e then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, D⟩, ⟨0x7000, 128⟩, ⟨0x300000, 20⟩, ⟨0x8000, 48⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x10000, 2080 * 8⟩]

/-- The hash functions ARMv7 registers RSAES-OAEP with. -/
def hashes : List Spec.Mgf1.Hash :=
  [Spec.Mgf1.sha1, Spec.Mgf1.sha224, Spec.Mgf1.sha256, Spec.Mgf1.sha384, Spec.Mgf1.sha512, Spec.Mgf1.sha512_224,
    Spec.Mgf1.sha512_256]

theorem encrypt_sat {H : Spec.Mgf1.Hash} (hH : H ∈ hashes) {vs : List TVar} {w : TVar} (hw : w ∈ vs)
    (hl : (names vs).length < 2 ^ 24) : ∃ s, (spec H (tables vs)).pre s := by
  refine ⟨withTable (satState H.len) vs w, ?_⟩
  have hA : ∀ D, ∀ j < 12, (stackArgAddr (satState D) j).toNat + 4 ≤ 0x300000 := fun _ => by
    show ∀ j < 12, (stackArgAddr (satState 0) j).toNat + 4 ≤ 0x300000; decide
  have a0 : ∀ D, stackArg (withTable (satState D) vs w) 0 = 0x2100 := fun D =>
    (withTable_below _ _ _ (hA D 0 (by decide))).trans (show stackArg (satState 0) 0 = 0x2100 by decide)
  have a1 : ∀ D, stackArg (withTable (satState D) vs w) 1 = 1 := fun D =>
    (withTable_below _ _ _ (hA D 1 (by decide))).trans (show stackArg (satState 0) 1 = 1 by decide)
  have a2 : ∀ D, stackArg (withTable (satState D) vs w) 2 = 0x3000 := fun D =>
    (withTable_below _ _ _ (hA D 2 (by decide))).trans (show stackArg (satState 0) 2 = 0x3000 by decide)
  have a3 : ∀ D, stackArg (withTable (satState D) vs w) 3 = 0 := fun D =>
    (withTable_below _ _ _ (hA D 3 (by decide))).trans (show stackArg (satState 0) 3 = 0 by decide)
  have a4 : ∀ D, stackArg (withTable (satState D) vs w) 4 = 0x3100 := fun D =>
    (withTable_below _ _ _ (hA D 4 (by decide))).trans (show stackArg (satState 0) 4 = 0x3100 by decide)
  have a5 : ∀ D, stackArg (withTable (satState D) vs w) 5 = 0 := fun D =>
    (withTable_below _ _ _ (hA D 5 (by decide))).trans (show stackArg (satState 0) 5 = 0 by decide)
  have a6 : ∀ D, stackArg (withTable (satState D) vs w) 6 = 0x3200 := fun D =>
    (withTable_below _ _ _ (hA D 6 (by decide))).trans (show stackArg (satState 0) 6 = 0x3200 by decide)
  have a7 : ∀ D, stackArg (withTable (satState D) vs w) 7 = 0x10000 := fun D =>
    (withTable_below _ _ _ (hA D 7 (by decide))).trans (show stackArg (satState 0) 7 = 0x10000 by decide)
  have a8 : ∀ D, stackArg (withTable (satState D) vs w) 8 = 0x820 := fun D =>
    (withTable_below _ _ _ (hA D 8 (by decide))).trans (show stackArg (satState 0) 8 = 0x820 by decide)
  have a9 : ∀ D, stackArg (withTable (satState D) vs w) 9 = 0x7000 := fun D =>
    (withTable_below _ _ _ (hA D 9 (by decide))).trans (show stackArg (satState 0) 9 = 0x7000 by decide)
  have a10 : ∀ D, stackArg (withTable (satState D) vs w) 10 = 16 := fun D =>
    (withTable_below _ _ _ (hA D 10 (by decide))).trans (show stackArg (satState 0) 10 = 16 by decide)
  have a11 : ∀ D, stackArg (withTable (satState D) vs w) 11 = 0x300000 := fun D =>
    (withTable_below _ _ _ (hA D 11 (by decide))).trans (show stackArg (satState 0) 11 = 0x300000 by decide)
  have e : ∀ D, stackArgAddr (withTable (satState D) vs w) 0 = 0x8000 := fun _ =>
    show stackArgAddr (satState 0) 0 = _ by decide
  simp only [hashes, List.mem_cons, List.not_mem_nil, or_false] at hH
  rcases hH with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    sig_pre [Spec.RsaOaep.encryptTableContract, Spec.RsaOaep.encryptTableSig, Spec.RsaOaep.encryptPrecomputedSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val]
    simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, e]
    sig_pre [Spec.RsaOaep.encryptTableContract, Spec.RsaOaep.encryptTableSig, Spec.RsaOaep.encryptPrecomputedSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val]
    sig_and_intros
    all_goals first
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)
      | exact ⟨tableOf w, List.mem_map_of_mem hw, withTable_held _ _ _⟩
      | (rw [List.append_eq, List.append_nil]; exact symsOf32_distinct hl)
      | (simp only [Spec.Rsa.lenValid]; decide)

end VG.Proof.RsaOaep.Arm.Enc
