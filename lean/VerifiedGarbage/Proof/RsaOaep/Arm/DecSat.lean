module

public import VerifiedGarbage.Proof.RsaOaep.Arm.DecBase
public import VerifiedGarbage.Proof.HashTable.Arm
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-OAEP decryption on ARMv7: the contract is satisfiable

A state that meets `decryptTableContract` (`dec_sat`), whatever the label's
hash function, with MGF1's the table of any `w` of `vs`: a modulus of 64
bytes, `e`, `p`, `q`, `dP`, `dQ` and `qInv` of one byte, an empty label, the
working space it needs, the stack arguments at `0x8000`, and the table at
`0x300000` (`withTable`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Dec

open VG VG.Arm
open VG.Proof.HashTable.Arm (TVar tables tableOf names withTable withTable_held withTable_below)
open VG.Proof.HashTable (symsOf32_distinct)

/-- The state, but for the table. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x1100 | .r3 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 0x40 else
    if a = 0x8005 then 0x21 else
    if a = 0x8008 then 1 else
    if a = 0x800d then 0x31 else
    if a = 0x8010 then 1 else
    if a = 0x8015 then 0x32 else
    if a = 0x8018 then 1 else
    if a = 0x801d then 0x33 else
    if a = 0x8020 then 1 else
    if a = 0x8025 then 0x34 else
    if a = 0x8028 then 1 else
    if a = 0x802d then 0x35 else
    if a = 0x8030 then 1 else
    if a = 0x8035 then 0x36 else
    if a = 0x803d then 0x37 else
    if a = 0x8040 then 0x40 else
    if a = 0x8046 then 1 else
    if a = 0x8048 then 0x20 else
    if a = 0x8049 then 8 else
    if a = 0x804e then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x3300, 1⟩, ⟨0x3400, 1⟩, ⟨0x3500, 1⟩,
    ⟨0x3600, 0⟩, ⟨0x3700, 64⟩, ⟨0x300000, 20⟩, ⟨0x8000, 80⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 8⟩, ⟨0x10000, 2080 * 8⟩]

theorem dec_sat (H : Spec.Mgf1.Hash) {vs : List TVar} {w : TVar} (hw : w ∈ vs) (hl : (names vs).length < 2 ^ 24) :
    ∃ s, (spec H (tables vs)).pre s := by
  refine ⟨withTable satState vs w, ?_⟩
  have hA : ∀ j < 20, (stackArgAddr satState j).toNat + 4 ≤ 0x300000 := by decide
  have a0 : stackArg (withTable satState vs w) 0 = 64 := (withTable_below _ _ _ (hA 0 (by decide))).trans (by decide)
  have a1 : stackArg (withTable satState vs w) 1 = 0x2100 := (withTable_below _ _ _ (hA 1 (by decide))).trans (by decide)
  have a2 : stackArg (withTable satState vs w) 2 = 1 := (withTable_below _ _ _ (hA 2 (by decide))).trans (by decide)
  have a3 : stackArg (withTable satState vs w) 3 = 0x3100 := (withTable_below _ _ _ (hA 3 (by decide))).trans (by decide)
  have a4 : stackArg (withTable satState vs w) 4 = 1 := (withTable_below _ _ _ (hA 4 (by decide))).trans (by decide)
  have a5 : stackArg (withTable satState vs w) 5 = 0x3200 := (withTable_below _ _ _ (hA 5 (by decide))).trans (by decide)
  have a6 : stackArg (withTable satState vs w) 6 = 1 := (withTable_below _ _ _ (hA 6 (by decide))).trans (by decide)
  have a7 : stackArg (withTable satState vs w) 7 = 0x3300 := (withTable_below _ _ _ (hA 7 (by decide))).trans (by decide)
  have a8 : stackArg (withTable satState vs w) 8 = 1 := (withTable_below _ _ _ (hA 8 (by decide))).trans (by decide)
  have a9 : stackArg (withTable satState vs w) 9 = 0x3400 := (withTable_below _ _ _ (hA 9 (by decide))).trans (by decide)
  have a10 : stackArg (withTable satState vs w) 10 = 1 := (withTable_below _ _ _ (hA 10 (by decide))).trans (by decide)
  have a11 : stackArg (withTable satState vs w) 11 = 0x3500 := (withTable_below _ _ _ (hA 11 (by decide))).trans (by decide)
  have a12 : stackArg (withTable satState vs w) 12 = 1 := (withTable_below _ _ _ (hA 12 (by decide))).trans (by decide)
  have a13 : stackArg (withTable satState vs w) 13 = 0x3600 := (withTable_below _ _ _ (hA 13 (by decide))).trans (by decide)
  have a14 : stackArg (withTable satState vs w) 14 = 0 := (withTable_below _ _ _ (hA 14 (by decide))).trans (by decide)
  have a15 : stackArg (withTable satState vs w) 15 = 0x3700 := (withTable_below _ _ _ (hA 15 (by decide))).trans (by decide)
  have a16 : stackArg (withTable satState vs w) 16 = 64 := (withTable_below _ _ _ (hA 16 (by decide))).trans (by decide)
  have a17 : stackArg (withTable satState vs w) 17 = 0x10000 := (withTable_below _ _ _ (hA 17 (by decide))).trans (by decide)
  have a18 : stackArg (withTable satState vs w) 18 = 0x820 := (withTable_below _ _ _ (hA 18 (by decide))).trans (by decide)
  have a19 : stackArg (withTable satState vs w) 19 = 0x300000 := (withTable_below _ _ _ (hA 19 (by decide))).trans (by decide)
  have e : stackArgAddr (withTable satState vs w) 0 = 0x8000 := show stackArgAddr satState 0 = _ by decide
  sig_pre [Spec.RsaOaep.decryptTableContract, Spec.RsaOaep.decryptTableSig, Spec.RsaOaep.decryptSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    abi, argRegs, reduceClassify, Loc.val]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, e]
  sig_pre [Spec.RsaOaep.decryptTableContract, Spec.RsaOaep.decryptTableSig, Spec.RsaOaep.decryptSig,
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

end VG.Proof.RsaOaep.Arm.Dec
