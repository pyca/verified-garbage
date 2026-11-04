module

public import VerifiedGarbage.Proof.RsaOaep.X86.Enc.Base
public import VerifiedGarbage.Proof.HashTable.X86
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-OAEP encryption with a precomputed public key on x86: the contract is satisfiable

A state that meets `encryptTablesContract` (`encrypt_sat`), with both
hash functions' tables that of any variant `w` of `vs`: a modulus of 64 bytes, `e` of one byte, an empty label and
message, the seed, the working space it needs, the precomputed values' 16
words, the arguments above `esp = 0x20000`, and the table at `0x300000`
(`withTable`), for both.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Enc

open VG
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes)
open VG.Proof.HashTable.X86 (TVar tables tableOf names withTable withTable_arg withTable_held hashAt_tableOf held_tableOf)
open VG.Proof.HashTable (symsOf32_distinct2)

/-- The state, for a seed of `D` bytes, but for the tables. -/
def satState (D : Nat) : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 131077 then 0x10 else if a = 131080 then 0x40 else if a = 131085 then 0x20 else if a = 131088 then 0x40 else if a = 131093 then 0x21 else if a = 131096 then 0x1 else if a = 131101 then 0x30 else if a = 131109 then 0x31 else if a = 131117 then 0x32 else if a = 131120 then BitVec.ofNat 8 D else if a = 131126 then 0x1 else if a = 131128 then 0x20 else if a = 131129 then 0x8 else if a = 131133 then 0x70 else if a = 131136 then 0x10 else if a = 131142 then 0x30 else if a = 131146 then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, D⟩, ⟨0x7000, 128⟩, ⟨0x300000, 20⟩,
    ⟨0x300000, 20⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x10000, 2080 * 8⟩, ⟨0x20004, 72⟩]

theorem encrypt_sat {vs : List TVar} {w : TVar} (hw : w ∈ vs) (hl : (names vs).length < 2 ^ 24) :
    ∃ s, (spec (tables vs)).pre s := by
  have hha : ∀ s : State, Spec.HashTable.hashAt 32 (withTable s vs w).mem ((0x300000 : BitVec 32).setWidth 64) =
      some w.g.G := fun s => hashAt_tableOf (by decide) (held_tableOf (by decide) (withTable_held s vs w)).2.1
  have hl' : w.g.G.len ∈ Impl.RsaOaep.X86.lens := w.g.glen ▸ w.g.lens
  generalize hDd : w.g.G.len = D at hl'
  refine ⟨withTable (satState D) vs w, ?_⟩
  have hA : ∀ D ∈ Impl.RsaOaep.X86.lens, ∀ j < 18, (argAddr (satState D) j).toNat + 4 ≤ 0x300000 := by decide
  have a0 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 0 = 0x1000 by decide) D hl'
  have a1 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 1 = 64 by decide) D hl'
  have a2 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 2 = 0x2000 by decide) D hl'
  have a3 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 3 = 64 by decide) D hl'
  have a4 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 4 = 0x2100 by decide) D hl'
  have a5 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 5 = 1 by decide) D hl'
  have a6 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 6 = 0x3000 by decide) D hl'
  have a7 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 7 = 0 by decide) D hl'
  have a8 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 8 = 0x3100 by decide) D hl'
  have a9 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 9 = 0 by decide) D hl'
  have a10 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 10 = 0x3200 by decide) D hl'
  have a11 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 11 = BitVec.ofNat 32 D by decide) D hl'
  have a12 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 12 = 0x10000 by decide) D hl'
  have a13 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 13 = 0x820 by decide) D hl'
  have a14 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 14 = 0x7000 by decide) D hl'
  have a15 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 15 = 16 by decide) D hl'
  have a16 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 16 = 0x300000 by decide) D hl'
  have a17 := (show ∀ D ∈ Impl.RsaOaep.X86.lens, arg (satState D) 17 = 0x300000 by decide) D hl'
  have hA' := hA D hl'
  have e : argAddr (withTable (satState D) vs w) 0 = 0x20004 := rfl
  have hha' := hha (satState D)
  simp only [Impl.RsaOaep.X86.lens, List.mem_cons, List.not_mem_nil, or_false] at hl'
  rcases hl' with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    sig_pre [Spec.RsaOaep.encryptTablesContract, Spec.RsaOaep.encryptTablesSig, Spec.RsaOaep.seedLenOk,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argSlots, argVal, argBytes, stackBelow]
    simp only [withTable_arg _ vs w (hA' 0 (by decide)), withTable_arg _ vs w (hA' 1 (by decide)),
      withTable_arg _ vs w (hA' 2 (by decide)), withTable_arg _ vs w (hA' 3 (by decide)),
      withTable_arg _ vs w (hA' 4 (by decide)), withTable_arg _ vs w (hA' 5 (by decide)),
      withTable_arg _ vs w (hA' 6 (by decide)), withTable_arg _ vs w (hA' 7 (by decide)),
      withTable_arg _ vs w (hA' 8 (by decide)), withTable_arg _ vs w (hA' 9 (by decide)),
      withTable_arg _ vs w (hA' 10 (by decide)), withTable_arg _ vs w (hA' 11 (by decide)),
      withTable_arg _ vs w (hA' 12 (by decide)), withTable_arg _ vs w (hA' 13 (by decide)),
      withTable_arg _ vs w (hA' 14 (by decide)), withTable_arg _ vs w (hA' 15 (by decide)),
      withTable_arg _ vs w (hA' 16 (by decide)), withTable_arg _ vs w (hA' 17 (by decide))]
    simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
      a12, a13, a14, a15, a16, a17, e]
    sig_pre [Spec.RsaOaep.encryptTablesContract, Spec.RsaOaep.encryptTablesSig, Spec.RsaOaep.seedLenOk,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argSlots, argVal, argBytes, stackBelow]
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

end VG.Proof.RsaOaep.X86.Enc
