module

public import VerifiedGarbage.Proof.RsaOaep.Arm.DecBase
public import VerifiedGarbage.Proof.HashTable.Arm
public import VerifiedGarbage.Proof.RsaOaep.Arm.DecP
public import VerifiedGarbage.Proof.Rsa.PreKey
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-OAEP decryption on ARMv7: the contract is satisfiable

A state that meets `decryptMdTablesContract` (`dec_sat`), with both hash
functions the table of any `w` of `vs`: a modulus of 64 bytes, `e`, `p`,
`q`, `dP`, `dQ` and `qInv` of one byte, an empty label, the working space it
needs, the stack arguments at `0x8000`, and the table, both arguments, at
`0x300000` (`withTable`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Dec

open VG VG.Arm
open VG.Proof.HashTable.Arm (TVar tables tableOf names withTable withTable_held held_twL withTable_below)
open VG.Proof.HashTable (symsOf32_distinct2)

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
    if a = 0x804e then 0x30 else
    if a = 0x8052 then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x3300, 1⟩, ⟨0x3400, 1⟩, ⟨0x3500, 1⟩,
    ⟨0x3600, 0⟩, ⟨0x3700, 64⟩, ⟨0x300000, 44⟩, ⟨0x300000, 44⟩, ⟨0x8000, 84⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 8⟩, ⟨0x10000, 2080 * 8⟩]

theorem dec_sat {vs : List TVar} {w : TVar} (hw : w ∈ vs) (hl : (names vs).length < 2 ^ 24) :
    ∃ s, (spec (tables vs)).pre s := by
  refine ⟨withTable satState vs w, ?_⟩
  have hA : ∀ j < 21, (stackArgAddr satState j).toNat + 4 ≤ 0x300000 := by decide
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
  have a20 : stackArg (withTable satState vs w) 20 = 0x300000 := (withTable_below _ _ _ (hA 20 (by decide))).trans (by decide)
  have e : stackArgAddr (withTable satState vs w) 0 = 0x8000 := show stackArgAddr satState 0 = _ by decide
  sig_pre [Spec.RsaOaep.decryptMdTablesContract, Spec.RsaOaep.decryptMdTablesSig, Spec.RsaOaep.decryptSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
    abi, argRegs, reduceClassify, Loc.val]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, e]
  sig_pre [Spec.RsaOaep.decryptMdTablesContract, Spec.RsaOaep.decryptMdTablesSig, Spec.RsaOaep.decryptSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
    abi, argRegs, reduceClassify, Loc.val]
  sig_and_intros
  all_goals first
    | exact ⟨tableOf w, List.mem_map_of_mem hw, held_twL _ _ _ rfl⟩
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (rw [List.append_eq, List.append_eq, List.append_nil]; exact symsOf32_distinct2 hl)
    | (simp only [Spec.Rsa.lenValid]; decide)

/-! ## Decryption with the key's precomputed values -/

open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)
open VG.Proof.HashTable (putWs32 add4_toNat)

/-- The stack arguments of `satStateP`: the key (`keyMem`'s), an empty
label, a 64-byte ciphertext, a working space of 2080 words, both tables at
`0x300000`, and `pre` at `0x4800`. -/
def satArgsP : List Nat :=
  [64, 0x2100, 1, 0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0x3600, 0, 0x3700, 64, 0x10000,
    0x820, 0x300000, 0x300000, 0x4800, 24]

/-- The memory of `satStateP`: the stack arguments from `0x8000`, and the
key. -/
def satMemP (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x8000 i && Nat.blt i 0x805C then
    BitVec.ofNat 8 (satArgsP.getD ((i - 0x8000) / 4) 0 / 256 ^ ((i - 0x8000) % 4))
  else bif keyIn i then keyMem a else 0

/-- A state meeting the precomputed decryption's precondition but for the
tables: the key `keyMem` holds (a 512-bit modulus at `0x2000`, 256-bit
primes at `0x4200` and `0x4300` and `pre` at `0x4800`), one-byte `e`. -/
def satStateP : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x1100 | .r3 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem := satMemP
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩, ⟨0x4600, 32⟩,
    ⟨0x3600, 0⟩, ⟨0x3700, 64⟩, ⟨0x4800, 192⟩, ⟨0x300000, 44⟩, ⟨0x300000, 44⟩, ⟨0x8000, 92⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 8⟩, ⟨0x10000, 2080 * 8⟩]

theorem satP_args : ∀ j < 23, stackArg satStateP j = BitVec.ofNat 32 (satArgsP.getD j 0) := by decide

/-- Below the words `putWs32` writes, a byte as before. -/
theorem putWs32_byte {m : Mem} {a : Addr} : ∀ {p : Addr} {ws : List (BitVec 64)}, a.toNat < p.toNat →
    p.toNat + 4 * ws.length < 2 ^ 64 → putWs32 m p ws a = m a
  | _, [], _, _ => rfl
  | p, w :: ws, h, hp => by
    simp only [List.length_cons] at hp
    have h4 := add4_toNat (p := p) (by omega_using [hp])
    simp only [putWs32]
    rw [putWs32_byte (by rw [h4]; omega_using [h]) (by rw [h4]; omega_using [hp])]
    have hne : ¬ (a - p).toNat < 32 / 8 := by
      rw [BitVec.toNat_sub, Nat.mod_eq_of_lt (by omega_using [h])]; omega_using [hp]
    simp only [Mem.writeW, Mem.write, hne, ↓reduceIte]

theorem satP_key (vs : List TVar) (w : TVar) :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt (withTable satStateP vs w).mem 0x2000 64)
      (Spec.Rsa.bytesAt (withTable satStateP vs w).mem 0x4200 32)
      (Spec.Rsa.bytesAt (withTable satStateP vs w).mem 0x4300 32) =
    some (Spec.Rsa.wordsAt (withTable satStateP vs w).mem 0x4800 24) :=
  key_pre_of fun a ha => by
    have hk : a.toNat < 0x48C0 := by
      simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha; omega
    have h2 : (Nat.ble 0x8000 a.toNat && Nat.blt a.toNat 0x805C) = false := by
      rw [Bool.eq_false_iff]; intro h; simp only [Bool.and_eq_true, Nat.ble_eq] at h; omega
    show putWs32 satMemP 0x300000 (VG.Proof.HashTable.Arm.twL vs w) a = keyMem a
    rw [putWs32_byte (by show a.toNat < 0x300000; omega_using [hk]) (VG.Proof.HashTable.Arm.twL_room vs w)]
    show (bif _ then _ else _) = _
    rw [h2, Bool.cond_false, ha, Bool.cond_true]

theorem dec_satP {vs : List TVar} {w : TVar} (hw : w ∈ vs) (hl : (names vs).length < 2 ^ 24) :
    ∃ s, (specP (tables vs)).pre s := by
  refine ⟨withTable satStateP vs w, ?_⟩
  have hA : ∀ j < 23, (stackArgAddr satStateP j).toNat + 4 ≤ 0x300000 := by decide
  have hb : ∀ j < 23, stackArg (withTable satStateP vs w) j = BitVec.ofNat 32 (satArgsP.getD j 0) :=
    fun j hj => (withTable_below _ _ _ (hA j hj)).trans (satP_args j hj)
  have e : stackArgAddr (withTable satStateP vs w) 0 = 0x8000 := show stackArgAddr satStateP 0 = _ by decide
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Abi.withTables, Sig.wordIndex, abi, argRegs, reduceClassify, Loc.val]
  simp only [hb 0 (by decide), hb 1 (by decide), hb 2 (by decide), hb 3 (by decide), hb 4 (by decide),
    hb 5 (by decide), hb 6 (by decide), hb 7 (by decide), hb 8 (by decide), hb 9 (by decide), hb 10 (by decide),
    hb 11 (by decide), hb 12 (by decide), hb 13 (by decide), hb 14 (by decide), hb 15 (by decide),
    hb 16 (by decide), hb 17 (by decide), hb 18 (by decide), hb 19 (by decide), hb 20 (by decide),
    hb 21 (by decide), hb 22 (by decide), e, satArgsP]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Abi.withTables, Sig.wordIndex, abi, argRegs, reduceClassify, Loc.val]
  sig_and_intros
  all_goals first
    | (show Spec.Rsa.privatePrecompute _ _ _ = _; exact satP_key vs w)
    | exact ⟨tableOf w, List.mem_map_of_mem hw, held_twL _ _ _ rfl⟩
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (rw [List.append_eq, List.append_eq, List.append_nil]; exact symsOf32_distinct2 hl)
    | (simp only [Spec.Rsa.lenValid]; decide)

end VG.Proof.RsaOaep.Arm.Dec
