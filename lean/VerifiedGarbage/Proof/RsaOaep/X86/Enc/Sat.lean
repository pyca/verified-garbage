module

public import VerifiedGarbage.Proof.RsaOaep.X86.Enc.Base
public import VerifiedGarbage.Proof.HashTable.X86
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-OAEP encryption with a precomputed public key on x86: the contract is satisfiable

A state that meets `encryptTableContract` (`encrypt_sat`), for each hash
function x86 registers RSAES-OAEP with, with MGF1's the table of any variant
`w` of `vs`: a modulus of 64 bytes, `e` of one byte, an empty label and
message, the seed, the working space it needs, the precomputed values' 16
words, the arguments above `esp = 0x20000`, and the table at `0x300000`
(`withTable`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Enc

open VG
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes)
open VG.Proof.HashTable.X86 (TVar tables tableOf names withTable withTable_arg withTable_held)
open VG.Proof.HashTable (symsOf32_distinct)

/-- The state, for a seed of `D` bytes, but for the table. -/
def satState (D : Nat) : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 131077 then 0x10 else if a = 131080 then 0x40 else if a = 131085 then 0x20 else if a = 131088 then 0x40 else if a = 131093 then 0x21 else if a = 131096 then 0x1 else if a = 131101 then 0x30 else if a = 131109 then 0x31 else if a = 131117 then 0x32 else if a = 131122 then 0x1 else if a = 131124 then 0x20 else if a = 131125 then 0x8 else if a = 131129 then 0x70 else if a = 131132 then 0x10 else if a = 131138 then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, D⟩, ⟨0x7000, 128⟩, ⟨0x300000, 20⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x10000, 2080 * 8⟩, ⟨0x20004, 64⟩]

/-- The hash functions x86 registers RSAES-OAEP with. -/
def hashes : List Spec.Mgf1.Hash :=
  [Spec.Mgf1.sha1, Spec.Mgf1.sha224, Spec.Mgf1.sha256, Spec.Mgf1.sha384, Spec.Mgf1.sha512, Spec.Mgf1.sha512_224,
    Spec.Mgf1.sha512_256]

theorem encrypt_sat {H : Spec.Mgf1.Hash} (hH : H ∈ hashes) {vs : List TVar} {w : TVar} (hw : w ∈ vs)
    (hl : (names vs).length < 2 ^ 24) : ∃ s, (spec H (tables vs)).pre s := by
  refine ⟨withTable (satState H.len) vs w, ?_⟩
  have hA : ∀ D, ∀ j < 16, (argAddr (satState D) j).toNat + 4 ≤ 0x300000 := fun _ => by
    show ∀ j < 16, (argAddr (satState 0) j).toNat + 4 ≤ 0x300000; decide
  have a0 : ∀ D, arg (satState D) 0 = 0x1000 := fun _ => show arg (satState 0) 0 = 0x1000 by decide
  have a1 : ∀ D, arg (satState D) 1 = 64 := fun _ => show arg (satState 0) 1 = 64 by decide
  have a2 : ∀ D, arg (satState D) 2 = 0x2000 := fun _ => show arg (satState 0) 2 = 0x2000 by decide
  have a3 : ∀ D, arg (satState D) 3 = 64 := fun _ => show arg (satState 0) 3 = 64 by decide
  have a4 : ∀ D, arg (satState D) 4 = 0x2100 := fun _ => show arg (satState 0) 4 = 0x2100 by decide
  have a5 : ∀ D, arg (satState D) 5 = 1 := fun _ => show arg (satState 0) 5 = 1 by decide
  have a6 : ∀ D, arg (satState D) 6 = 0x3000 := fun _ => show arg (satState 0) 6 = 0x3000 by decide
  have a7 : ∀ D, arg (satState D) 7 = 0 := fun _ => show arg (satState 0) 7 = 0 by decide
  have a8 : ∀ D, arg (satState D) 8 = 0x3100 := fun _ => show arg (satState 0) 8 = 0x3100 by decide
  have a9 : ∀ D, arg (satState D) 9 = 0 := fun _ => show arg (satState 0) 9 = 0 by decide
  have a10 : ∀ D, arg (satState D) 10 = 0x3200 := fun _ => show arg (satState 0) 10 = 0x3200 by decide
  have a11 : ∀ D, arg (satState D) 11 = 0x10000 := fun _ => show arg (satState 0) 11 = 0x10000 by decide
  have a12 : ∀ D, arg (satState D) 12 = 0x820 := fun _ => show arg (satState 0) 12 = 0x820 by decide
  have a13 : ∀ D, arg (satState D) 13 = 0x7000 := fun _ => show arg (satState 0) 13 = 0x7000 by decide
  have a14 : ∀ D, arg (satState D) 14 = 16 := fun _ => show arg (satState 0) 14 = 16 by decide
  have a15 : ∀ D, arg (satState D) 15 = 0x300000 := fun _ => show arg (satState 0) 15 = 0x300000 by decide
  have e : ∀ D, argAddr (withTable (satState D) vs w) 0 = 0x20004 := fun _ => show argAddr (satState 0) 0 = _ by decide
  simp only [hashes, List.mem_cons, List.not_mem_nil, or_false] at hH
  rcases hH with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    sig_pre [Spec.RsaOaep.encryptTableContract, Spec.RsaOaep.encryptTableSig, Spec.RsaOaep.encryptPrecomputedSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argSlots, argVal, argBytes, stackBelow]
    simp only [withTable_arg _ vs w (hA _ 0 (by decide)), withTable_arg _ vs w (hA _ 1 (by decide)), withTable_arg _ vs w (hA _ 2 (by decide)), withTable_arg _ vs w (hA _ 3 (by decide)), withTable_arg _ vs w (hA _ 4 (by decide)), withTable_arg _ vs w (hA _ 5 (by decide)), withTable_arg _ vs w (hA _ 6 (by decide)), withTable_arg _ vs w (hA _ 7 (by decide)), withTable_arg _ vs w (hA _ 8 (by decide)), withTable_arg _ vs w (hA _ 9 (by decide)), withTable_arg _ vs w (hA _ 10 (by decide)), withTable_arg _ vs w (hA _ 11 (by decide)), withTable_arg _ vs w (hA _ 12 (by decide)), withTable_arg _ vs w (hA _ 13 (by decide)), withTable_arg _ vs w (hA _ 14 (by decide)), withTable_arg _ vs w (hA _ 15 (by decide))]
    simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
      a12, a13, a14, a15, e]
    sig_pre [Spec.RsaOaep.encryptTableContract, Spec.RsaOaep.encryptTableSig, Spec.RsaOaep.encryptPrecomputedSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argSlots, argVal, argBytes, stackBelow]
    sig_and_intros
    all_goals first
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)
      | exact ⟨tableOf w, List.mem_map_of_mem hw, withTable_held _ _ _⟩
      | (rw [List.append_eq, List.append_nil]; exact symsOf32_distinct hl)
      | (simp only [Spec.Rsa.lenValid]; decide)

end VG.Proof.RsaOaep.X86.Enc
