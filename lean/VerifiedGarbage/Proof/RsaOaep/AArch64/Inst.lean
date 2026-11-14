module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncVerified
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecVerified
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Callees
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecPCT
public import VerifiedGarbage.Proof.Rsa.PreKey
import Mathlib.Data.Nat.Basic

/-!
# RSAES-OAEP on AArch64: the instances emitted

States meeting both contracts, with both tables at `0x300000`
(`withTable`), and the instances' proofs against the contracts the
registrations state (`dec_ok`, `enc_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK MgfLink MdHash mdHashes)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.HashTable.AArch64 (tables fnsOf names Coh tableOf)
open VG.Proof.HashTable (symsOf_distinct2)
open VG.Proof.MdHashTable.AArch64 (withTable withTable_below withTable_held held_twL)
open VG.Proof.HashTable.AArch64 (held_tableOf hashAt_tableOf)

theorem withTable_addr (s : State) (vs : List MdHash) (w : MdHash) (j : Nat) :
    stackArgAddr (withTable s vs w) j = stackArgAddr s j := rfl

theorem withTable_arg (s : State) (vs : List MdHash) (w : MdHash) {j : Nat}
    (hj : (stackArgAddr s j).toNat + 8 ≤ 0x300000) : stackArg (withTable s vs w) j = stackArg s j :=
  withTable_below s vs w hj

/-! ## Decryption -/

/-- A state meeting decryption's contract but for the tables: a 512-bit
modulus, one-byte `e`, primes, exponents and `qInv`, an empty label, a
working space of 2080 words, the stack arguments at `0x10000`, and both
tables' address `0x300000`. -/
def decSatBase : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x1800 | .x3 => 0x2000 | .x4 => 64 | .x5 => 0x3000 | .x6 => 1
    | .x7 => 0x4200 | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10070 then 0x20
    else bif Nat.beq a.toNat 0x10000 then 1 else bif Nat.beq a.toNat 0x10009 then 0x43
    else bif Nat.beq a.toNat 0x10010 then 1 else bif Nat.beq a.toNat 0x10019 then 0x44
    else bif Nat.beq a.toNat 0x10020 then 1 else bif Nat.beq a.toNat 0x10029 then 0x45
    else bif Nat.beq a.toNat 0x10030 then 1 else bif Nat.beq a.toNat 0x10039 then 0x46
    else bif Nat.beq a.toNat 0x10040 then 1 else bif Nat.beq a.toNat 0x10049 then 0x47
    else bif Nat.beq a.toNat 0x10059 then 0x41 else bif Nat.beq a.toNat 0x10060 then 64
    else bif Nat.beq a.toNat 0x1006A then 0x02 else bif Nat.beq a.toNat 0x10071 then 0x08
    else bif Nat.beq a.toNat 0x1007A then 0x30 else bif Nat.beq a.toNat 0x10082 then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩, ⟨0x4500, 1⟩, ⟨0x4600, 1⟩,
    ⟨0x4700, 0⟩, ⟨0x4100, 64⟩, ⟨0x300000, 88⟩, ⟨0x300000, 88⟩, ⟨0x10000, 136⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 16640⟩]

theorem dec_sat {vs : List MdHash} {w : MdHash} (hw : w ∈ vs) (hl : (names vs).length < 2 ^ 32)
    (c : Proof.Rsa.AArch64.CrtImpl) :
    ∃ s, (Dec.decSpec (tables vs) ((RsaPkcs1Enc.AArch64.privOf c).S + 1)).pre s := by
  refine ⟨withTable decSatBase vs w, ?_⟩
  have hA : ∀ j < 17, (stackArgAddr decSatBase j).toNat + 8 ≤ 0x300000 := by decide
  have hS : (RsaPkcs1Enc.AArch64.privOf c).S + 1 = 3248 := by
    rw [← Nat.add_right_cancel_iff (n := 288), ← Dec.decStack_eq]; rfl
  rw [hS]
  sig_pre [Spec.RsaOaep.decryptMdTablesContract, Spec.RsaOaep.decryptMdTablesSig, Spec.RsaOaep.decryptSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
    AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
  simp only [withTable_arg _ vs w (hA 0 (by decide)), withTable_arg _ vs w (hA 1 (by decide)),
    withTable_arg _ vs w (hA 2 (by decide)), withTable_arg _ vs w (hA 3 (by decide)),
    withTable_arg _ vs w (hA 4 (by decide)), withTable_arg _ vs w (hA 5 (by decide)),
    withTable_arg _ vs w (hA 6 (by decide)), withTable_arg _ vs w (hA 7 (by decide)),
    withTable_arg _ vs w (hA 8 (by decide)), withTable_arg _ vs w (hA 9 (by decide)),
    withTable_arg _ vs w (hA 10 (by decide)), withTable_arg _ vs w (hA 11 (by decide)),
    withTable_arg _ vs w (hA 12 (by decide)), withTable_arg _ vs w (hA 13 (by decide)),
    withTable_arg _ vs w (hA 14 (by decide)), withTable_arg _ vs w (hA 15 (by decide)),
    withTable_arg _ vs w (hA 16 (by decide))]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', withTable_addr]
  sig_pre [Spec.RsaOaep.decryptMdTablesContract, Spec.RsaOaep.decryptMdTablesSig, Spec.RsaOaep.decryptSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
    AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
  sig_and_intros
  all_goals first
    | exact ⟨tableOf w, List.mem_map_of_mem hw, by
        rw [show stackArg decSatBase 15 = 0x300000 by decide]; exact held_twL _ _ _ rfl⟩
    | exact ⟨tableOf w, List.mem_map_of_mem hw, by
        rw [show stackArg decSatBase 16 = 0x300000 by decide]; exact held_twL _ _ _ rfl⟩
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact symsOf_distinct2 hl
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (intro a h₁ h₂
       set_option linter.unusedSimpArgs false in
       sig_simp_only [Region.Contains, decSatBase, stackArg, stackArgAddr, Mem.readW, Mem.read] at h₁ h₂
       bv_omega)

/-! ## Decryption with the key's precomputed values -/

open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)
open VG.Proof.HashTable (putWs add8_toNat)

/-- The stack arguments of `decPSatBase`: the key (`keyMem`'s), an empty
label, a 64-byte ciphertext, a working space of 2080 words, both tables at
`0x300000`, and `pre` at `0x4800`. -/
def decPArgs : List Nat :=
  [32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0x4700, 0, 0x4100, 64, 0x20000, 2080, 0x300000, 0x300000,
    0x4800, 24]

/-- The memory of `decPSatBase`: the stack arguments from `0x10000`, and the
key. -/
def decPMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x10000 i && Nat.blt i 0x10098 then
    BitVec.ofNat 8 (decPArgs.getD ((i - 0x10000) / 8) 0 / 256 ^ ((i - 0x10000) % 8))
  else bif keyIn i then keyMem a else 0

/-- A state meeting the precomputed decryption's precondition but for the
tables: the key `keyMem` holds (a 512-bit modulus at `0x2000`, 256-bit
primes at `0x4200` and `0x4300` and `pre` at `0x4800`), one-byte `e`. -/
def decPSatBase : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x1800 | .x3 => 0x2000 | .x4 => 64 | .x5 => 0x3000 | .x6 => 1
    | .x7 => 0x4200 | _ => 0
  sp := 0x10000
  mem := decPMem
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩, ⟨0x4600, 32⟩,
    ⟨0x4700, 0⟩, ⟨0x4100, 64⟩, ⟨0x4800, 192⟩, ⟨0x300000, 88⟩, ⟨0x300000, 88⟩, ⟨0x10000, 152⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 16640⟩]

theorem decPSat_args : ∀ j < 19, stackArg decPSatBase j = BitVec.ofNat 64 (decPArgs.getD j 0) := by decide

/-- Below the words `putWs` writes, a byte as before. -/
theorem putWs_byte {m : Mem} {a : Addr} : ∀ {p : Addr} {ws : List (BitVec 64)}, a.toNat < p.toNat →
    p.toNat + 8 * ws.length < 2 ^ 64 → putWs m p ws a = m a
  | _, [], _, _ => rfl
  | p, w :: ws, h, hp => by
    simp only [List.length_cons] at hp
    have h8 := add8_toNat (p := p) (by omega_using [hp])
    simp only [putWs]
    rw [putWs_byte (by rw [h8]; omega_using [h]) (by rw [h8]; omega_using [hp])]
    have hne : ¬ (a - p).toNat < 64 / 8 := by
      rw [BitVec.toNat_sub, Nat.mod_eq_of_lt (by omega_using [h])]; omega_using [hp]
    simp only [Mem.writeW, Mem.write, hne, ↓reduceIte]

theorem decPSat_key (vs : List MdHash) (w : MdHash) :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt (withTable decPSatBase vs w).mem 0x2000 64)
      (Spec.Rsa.bytesAt (withTable decPSatBase vs w).mem 0x4200 32)
      (Spec.Rsa.bytesAt (withTable decPSatBase vs w).mem 0x4300 32) =
    some (Spec.Rsa.wordsAt (withTable decPSatBase vs w).mem 0x4800 24) :=
  key_pre_of fun a ha => by
    have hk : a.toNat < 0x48C0 := by
      simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha; omega
    have h2 : (Nat.ble 0x10000 a.toNat && Nat.blt a.toNat 0x10098) = false := by
      rw [Bool.eq_false_iff]; intro h; simp only [Bool.and_eq_true, Nat.ble_eq] at h; omega
    show putWs decPMem 0x300000 (MdHashTable.AArch64.twL vs w) a = keyMem a
    rw [putWs_byte (by show a.toNat < 0x300000; omega_using [hk]) (MdHashTable.AArch64.twL_room vs w)]
    show (bif _ then _ else _) = _
    rw [h2, Bool.cond_false, ha, Bool.cond_true]

theorem decP_sat {vs : List MdHash} {w : MdHash} (hw : w ∈ vs) (hl : (names vs).length < 2 ^ 32)
    (c : Proof.Rsa.AArch64.CrtImpl) :
    ∃ s, (Dec.decSpecP (tables vs) (RsaPkcs1Sig.AArch64.privPOf c).stack).pre s := by
  refine ⟨withTable decPSatBase vs w, ?_⟩
  have hA : ∀ j < 19, (stackArgAddr decPSatBase j).toNat + 8 ≤ 0x300000 := by decide
  have hb : ∀ j < 19, stackArg (withTable decPSatBase vs w) j = BitVec.ofNat 64 (decPArgs.getD j 0) :=
    fun j hj => (withTable_arg _ vs w (hA j hj)).trans (decPSat_args j hj)
  rw [show (RsaPkcs1Sig.AArch64.privPOf c).stack = 3248 from rfl]
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Abi.withTables, Sig.wordIndex, AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop,
    List.append_eq]
  simp only [hb 0 (by decide), hb 1 (by decide), hb 2 (by decide), hb 3 (by decide), hb 4 (by decide),
    hb 5 (by decide), hb 6 (by decide), hb 7 (by decide), hb 8 (by decide), hb 9 (by decide), hb 10 (by decide),
    hb 11 (by decide), hb 12 (by decide), hb 13 (by decide), hb 14 (by decide), hb 15 (by decide),
    hb 16 (by decide), hb 17 (by decide), hb 18 (by decide), decPArgs]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', withTable_addr]
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Abi.withTables, Sig.wordIndex, AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop,
    List.append_eq]
  sig_and_intros
  all_goals first
    | (show Spec.Rsa.privatePrecompute _ _ _ = _; exact decPSat_key vs w)
    | exact ⟨tableOf w, List.mem_map_of_mem hw, held_twL _ _ _ rfl⟩
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact symsOf_distinct2 hl
    | (simp only [Spec.Rsa.lenValid]; decide)

/-! ## Encryption with a precomputed key -/

/-- A state meeting encryption's contract for `H` but for the tables: a
512-bit modulus, a one-byte `e`, an empty label and message, `H`'s seed, a
working space of 2080 words, 16 words of `pre` at `0x5000`, the stack
arguments at `0x10000`, and both tables' address `0x300000`. -/
def encSatBase (H : Spec.Mgf1.Hash) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 64 | .x4 => 0x3000 | .x5 => 1 | .x6 => 0x4000
    | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10028 then 0x20
    else bif Nat.beq a.toNat 0x10001 then 0x41 else bif Nat.beq a.toNat 0x10011 then 0x42
    else bif Nat.beq a.toNat 0x10018 then BitVec.ofNat 8 H.len
    else bif Nat.beq a.toNat 0x10022 then 0x02 else bif Nat.beq a.toNat 0x10029 then 0x08
    else bif Nat.beq a.toNat 0x10031 then 0x50 else bif Nat.beq a.toNat 0x10038 then 16
    else bif Nat.beq a.toNat 0x10042 then 0x30 else bif Nat.beq a.toNat 0x1004A then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 0⟩, ⟨0x4100, 0⟩, ⟨0x4200, H.len⟩, ⟨0x5000, 128⟩,
    ⟨0x300000, 88⟩, ⟨0x300000, 88⟩, ⟨0x10000, 80⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 16640⟩]

theorem enc_sat {vs : List MdHash} {w : MdHash} (hw : w ∈ vs) (hl : (names vs).length < 2 ^ 32)
    (v : Proof.Rsa.AArch64.PublicImpl) :
    ∃ s, (Enc.encSpec (tables vs) (Enc.encP (RsaPkcs1Sig.AArch64.pdOf v))).pre s := by
  have hha : ∀ s : State, Spec.MdHashTable.hashAt 64 (withTable s vs w).mem 0x300000 = some w.mgf.G := fun s =>
    hashAt_tableOf (held_tableOf (withTable_held s vs w)).2.1
  have hH := w.mgf.mem
  generalize w.mgf.G = H at hha hH
  refine ⟨withTable (encSatBase H) vs w, ?_⟩
  have hB : ∀ j < 10, ((0x10000 : Addr) + BitVec.ofNat 64 (8 * j)).toNat + 8 ≤ 0x300000 := by decide
  have hA : ∀ (G : Spec.Mgf1.Hash), ∀ j < 10, (stackArgAddr (encSatBase G) j).toNat + 8 ≤ 0x300000 :=
    fun _ j hj => hB j hj
  have hha' := hha (encSatBase H)
  have hP : Enc.encP (RsaPkcs1Sig.AArch64.pdOf v) = 16 := rfl
  rw [hP]
  simp only [mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hH
  rcases hH with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    sig_pre [Spec.RsaOaep.encryptMdTablesContract, Spec.RsaOaep.encryptMdTablesSig, Spec.RsaOaep.seedLenMdOk,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
      AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
    simp only [withTable_arg _ vs w (hA _ 0 (by decide)), withTable_arg _ vs w (hA _ 1 (by decide)),
      withTable_arg _ vs w (hA _ 2 (by decide)), withTable_arg _ vs w (hA _ 3 (by decide)),
      withTable_arg _ vs w (hA _ 4 (by decide)), withTable_arg _ vs w (hA _ 5 (by decide)),
      withTable_arg _ vs w (hA _ 6 (by decide)), withTable_arg _ vs w (hA _ 7 (by decide)),
      withTable_arg _ vs w (hA _ 8 (by decide)), withTable_arg _ vs w (hA _ 9 (by decide))]
    simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq, exists_eq_left', withTable_addr]
    sig_pre [Spec.RsaOaep.encryptMdTablesContract, Spec.RsaOaep.encryptMdTablesSig, Spec.RsaOaep.seedLenMdOk,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
      AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
    sig_and_intros
    all_goals first
      | exact ⟨tableOf w, List.mem_map_of_mem hw, by
          rw [show stackArg (encSatBase _) 8 = 0x300000 by decide]; exact held_twL _ _ _ rfl⟩
      | exact ⟨tableOf w, List.mem_map_of_mem hw, by
          rw [show stackArg (encSatBase _) 9 = 0x300000 by decide]; exact held_twL _ _ _ rfl⟩
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)
      | (intro H' hH'
         rw [show stackArg (encSatBase _) 8 = 0x300000 by decide] at hH'
         obtain rfl := Option.some.inj (hha'.symm.trans hH')
         decide)
      | exact symsOf_distinct2 hl
      | (simp only [Spec.Rsa.lenValid]; decide)
      | (intro a h₁ h₂
         set_option linter.unusedSimpArgs false in
         sig_simp_only [Region.Contains, encSatBase, stackArg, stackArgAddr, Mem.readW, Mem.read] at h₁ h₂
         bv_omega)

/-! ## The instances -/

/-- What the registrations check of the variants whose tables a function
takes. -/
def OK (vs : List MdHash) : Prop := Coh vs ∧ (names vs).length < 2 ^ 32 ∧ vs ≠ []

instance (vs : List MdHash) : Decidable (OK vs) := by unfold OK; infer_instance

theorem OK.mem {vs : List MdHash} (h : OK vs) : ∃ w, w ∈ vs := List.exists_mem_of_ne_nil _ h.2.2

/-- `vg_rsa_oaep_decrypt`, with the tables of `vs` and the private-key
operation of `c`. -/
theorem dec_ok (vs : List MdHash) (h : OK vs) (c : Proof.Rsa.AArch64.CrtImpl) :
    Verified AArch64.target (Impl.RsaOaep.AArch64.decrypt (fnsOf vs) (RsaPkcs1Enc.AArch64.privOf c).name
        (RsaPkcs1Enc.AArch64.privOf c).code)
      (Spec.RsaOaep.decryptMdTablesContract
        (AArch64.abi.withTables Spec.RsaOaep.decryptMdTablesSig [("hash", tables vs), ("mgf1", tables vs)])
        (Dec.decStack (RsaPkcs1Enc.AArch64.privOf c))) := by
  rw [Dec.decStack_eq]
  exact Dec.dec_verified h.1 _ (let ⟨_, hw⟩ := h.mem; dec_sat hw h.2.1 c)

/-- `vg_rsa_oaep_decrypt_precomputed`, with the tables of `vs`, calling
`vg_rsa_private_checked_precomputed` of the implementation `c`. -/
theorem decP_ok (vs : List MdHash) (h : OK vs) (c : Proof.Rsa.AArch64.CrtImpl) :
    Verified AArch64.target (Impl.RsaOaep.AArch64.decryptP (fnsOf vs) (RsaPkcs1Sig.AArch64.privPOf c).name
        (RsaPkcs1Sig.AArch64.privPOf c).code)
      (Spec.RsaOaep.decryptPrecomputedMdTablesContract
        (AArch64.abi.withTables Spec.RsaOaep.decryptPrecomputedMdTablesSig [("hash", tables vs), ("mgf1", tables vs)])
        ((RsaPkcs1Sig.AArch64.privPOf c).stack + 288)) :=
  Dec.decP_verified h.1 _ (by show 16 ≤ Proof.Rsa.AArch64.stackBytes; decide)
    (let ⟨_, hw⟩ := h.mem; decP_sat hw h.2.1 c)

/-- `vg_rsa_oaep_encrypt_precomputed`, with the tables of `vs` and the
precomputed public operation of `c`. -/
theorem enc_ok (vs : List MdHash) (h : OK vs) (c : Proof.Rsa.AArch64.PublicImpl) :
    Verified AArch64.target (Impl.RsaOaep.AArch64.Precomputed.encrypt (fnsOf vs)
        (RsaPkcs1Sig.AArch64.pdOf c).name (RsaPkcs1Sig.AArch64.pdOf c).code)
      (Spec.RsaOaep.encryptMdTablesContract
        (AArch64.abi.withTables Spec.RsaOaep.encryptMdTablesSig [("hash", tables vs), ("mgf1", tables vs)])
        (Enc.encStack (RsaPkcs1Sig.AArch64.pdOf c))) :=
  Enc.enc_verified h.1 _ (let ⟨_, hw⟩ := h.mem; enc_sat hw h.2.1 c)

end VG.Proof.RsaOaep.AArch64
