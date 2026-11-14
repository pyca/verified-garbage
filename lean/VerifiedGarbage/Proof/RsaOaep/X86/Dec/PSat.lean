module

public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.PCall
public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Sat
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-OAEP decryption on x86, given `pre`: the contract is satisfiable

As `Dec/Sat.lean`, with the key of `Proof/Rsa/PreKey.lean` (`keyMem`): a
modulus of 64 bytes at `0x2000`, `p` and `q` of 32 at `0x4200` and
`0x4300`, `dP`, `dQ` and `qInv` of 32, and `pre` (24 words) at `0x4800`
(`satStateP`); the table is written above all of it (`putWs32_byte`).
-/

-- separate module: builds in parallel with the proof (`Dec/PVerified`), which it does not need.

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Dec

open VG
open VG.X86 hiding frameBytes
open VG.Proof.HashTable (putWs32 add4_toNat symsOf32_distinct2)
open VG.Proof.HashTable.X86 (TVar tables tableOf names withTable withTable_arg held_twL twL twL_room)
open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)

/-- Words written from `p` on leave the bytes below `p` as they were. -/
theorem putWs32_byte {a : Addr} : ∀ {p : Addr} {ws : List (BitVec 64)} {m : Mem},
    a.toNat < p.toNat → p.toNat + 4 * ws.length < 2 ^ 64 → putWs32 m p ws a = m a
  | _, [], _, _, _ => rfl
  | p, w :: ws, m, ha, hp => by
    simp only [List.length_cons] at hp
    have h4 := add4_toNat (p := p) (by omega_using [hp])
    simp only [putWs32]
    rw [putWs32_byte (by rw [h4]; omega_using [ha]) (by rw [h4]; omega_using [hp])]
    refine Mem.write_apply fun h => ?_
    rw [BitVec.toNat_sub] at h
    have := a.isLt
    omega_using [ha, hp, h]

/-- The memory: the key, the arguments that differ from `satState`'s, and its. -/
def memP (a : Addr) : Byte :=
  bif keyIn a.toNat then keyMem a
  else if a = 0x20021 then 0x42 else if a = 0x20024 then 32 else if a = 0x20029 then 0x43
  else if a = 0x2002C then 32 else if a = 0x20034 then 32 else if a = 0x2003C then 32
  else if a = 0x20044 then 32 else if a = 0x20069 then 0x48 else if a = 0x2006C then 24
  else satState.mem a

/-- `satState` with the key and its precomputed values. -/
def satStateP : State :=
  { satState with
    mem := memP
    rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x3300, 32⟩, ⟨0x3400, 32⟩, ⟨0x3500, 32⟩,
      ⟨0x3600, 0⟩, ⟨0x3700, 64⟩, ⟨0x4800, 192⟩, ⟨0x300000, 44⟩, ⟨0x300000, 44⟩]
    wr := [⟨0x1000, 64⟩, ⟨0x1100, 8⟩, ⟨0x10000, 2080 * 8⟩, ⟨0x20004, 108⟩] }

theorem withTableP_key (vs : List TVar) (w : TVar) :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt (withTable satStateP vs w).mem 0x2000 64)
      (Spec.Rsa.bytesAt (withTable satStateP vs w).mem 0x4200 32)
      (Spec.Rsa.bytesAt (withTable satStateP vs w).mem 0x4300 32) =
    some (Spec.Rsa.wordsAt (withTable satStateP vs w).mem 0x4800 24) := by
  refine key_pre_of fun a ha => ?_
  have hlt : a.toNat < 0x48C0 := by
    simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha; omega
  simp only [withTable]
  rw [putWs32_byte (by show a.toNat < 0x300000; omega_using [hlt]) (twL_room vs w)]
  show memP a = keyMem a
  simp only [memP, ha, Bool.cond_true]

theorem dec_satP {vs : List TVar} {w : TVar} (hw : w ∈ vs) (hl : (names vs).length < 2 ^ 24) :
    ∃ s, (specP (tables vs)).pre s := by
  refine ⟨withTable satStateP vs w, ?_⟩
  have hk := withTableP_key vs w
  have hk' : Spec.Rsa.privatePrecompute
      (Spec.Rsa.bytesAt (putWs32 memP 3145728 (twL vs w)) (BitVec.setWidth 64 (8192 : BitVec 32))
        (BitVec.toNat (64 : BitVec 32)))
      (Spec.Rsa.bytesAt (putWs32 memP 3145728 (twL vs w)) (BitVec.setWidth 64 (16896 : BitVec 32))
        (BitVec.toNat (32 : BitVec 32)))
      (Spec.Rsa.bytesAt (putWs32 memP 3145728 (twL vs w)) (BitVec.setWidth 64 (17152 : BitVec 32))
        (BitVec.toNat (32 : BitVec 32))) =
    some (Spec.Rsa.wordsAt (putWs32 memP 3145728 (twL vs w)) (BitVec.setWidth 64 (18432 : BitVec 32))
      (BitVec.toNat (24 : BitVec 32))) := hk
  have hA : ∀ j < 27, (argAddr satStateP j).toNat + 4 ≤ 0x300000 := by decide
  have a0 : arg satStateP 0 = 0x1000 := by decide
  have a1 : arg satStateP 1 = 64 := by decide
  have a2 : arg satStateP 2 = 0x1100 := by decide
  have a3 : arg satStateP 3 = 0x2000 := by decide
  have a4 : arg satStateP 4 = 64 := by decide
  have a5 : arg satStateP 5 = 0x2100 := by decide
  have a6 : arg satStateP 6 = 1 := by decide
  have a7 : arg satStateP 7 = 0x4200 := by decide
  have a8 : arg satStateP 8 = 32 := by decide
  have a9 : arg satStateP 9 = 0x4300 := by decide
  have a10 : arg satStateP 10 = 32 := by decide
  have a11 : arg satStateP 11 = 0x3300 := by decide
  have a12 : arg satStateP 12 = 32 := by decide
  have a13 : arg satStateP 13 = 0x3400 := by decide
  have a14 : arg satStateP 14 = 32 := by decide
  have a15 : arg satStateP 15 = 0x3500 := by decide
  have a16 : arg satStateP 16 = 32 := by decide
  have a17 : arg satStateP 17 = 0x3600 := by decide
  have a18 : arg satStateP 18 = 0 := by decide
  have a19 : arg satStateP 19 = 0x3700 := by decide
  have a20 : arg satStateP 20 = 64 := by decide
  have a21 : arg satStateP 21 = 0x10000 := by decide
  have a22 : arg satStateP 22 = 0x820 := by decide
  have a23 : arg satStateP 23 = 0x300000 := by decide
  have a24 : arg satStateP 24 = 0x300000 := by decide
  have a25 : arg satStateP 25 = 0x4800 := by decide
  have a26 : arg satStateP 26 = 24 := by decide
  have e : argAddr (withTable satStateP vs w) 0 = 0x20004 := show argAddr satStateP 0 = _ by decide
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [withTable_arg _ vs w (hA 0 (by decide)), withTable_arg _ vs w (hA 1 (by decide)), withTable_arg _ vs w (hA 2 (by decide)), withTable_arg _ vs w (hA 3 (by decide)), withTable_arg _ vs w (hA 4 (by decide)), withTable_arg _ vs w (hA 5 (by decide)), withTable_arg _ vs w (hA 6 (by decide)), withTable_arg _ vs w (hA 7 (by decide)), withTable_arg _ vs w (hA 8 (by decide)), withTable_arg _ vs w (hA 9 (by decide)), withTable_arg _ vs w (hA 10 (by decide)), withTable_arg _ vs w (hA 11 (by decide)), withTable_arg _ vs w (hA 12 (by decide)), withTable_arg _ vs w (hA 13 (by decide)), withTable_arg _ vs w (hA 14 (by decide)), withTable_arg _ vs w (hA 15 (by decide)), withTable_arg _ vs w (hA 16 (by decide)), withTable_arg _ vs w (hA 17 (by decide)), withTable_arg _ vs w (hA 18 (by decide)), withTable_arg _ vs w (hA 19 (by decide)), withTable_arg _ vs w (hA 20 (by decide)), withTable_arg _ vs w (hA 21 (by decide)), withTable_arg _ vs w (hA 22 (by decide)), withTable_arg _ vs w (hA 23 (by decide)), withTable_arg _ vs w (hA 24 (by decide)), withTable_arg _ vs w (hA 25 (by decide)), withTable_arg _ vs w (hA 26 (by decide))]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, e]
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (exact ⟨tableOf w, List.mem_map_of_mem hw, held_twL _ _ _ rfl⟩)
  all_goals try (rw [List.append_eq, List.append_eq, List.append_nil]; exact symsOf32_distinct2 hl)
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  rotate_right
  · exact hk'
  all_goals rfl

end VG.Proof.RsaOaep.X86.Dec
