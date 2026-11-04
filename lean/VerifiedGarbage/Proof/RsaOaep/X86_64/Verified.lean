module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecCT
public import VerifiedGarbage.Proof.RsaOaep.X86_64.PcCT
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-OAEP on x86-64 with both hash functions as tables: the instances

The contracts with tables are satisfiable (`dec_sat`, `enc_sat`): by a
state with the table of a variant `w` of `vs` at `0x300000`, the value of
both table arguments, and its functions at distinct addresses (`symsOf`).
So for the variants `vs` of `MdHash` that pass the checks the registrations
make (`OK`: their functions of the same name have the same code, there are
some, and not too many names), decryption and encryption with a
precomputed key, taking the tables of `vs` for both hash functions, meet
their contracts (`dec_ok`, `enc_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink MdHash)
open VG.Proof.RsaPkcs1Enc.X86_64 (PrivImpl)
open VG.Proof.Rsa.X86_64 (PublicImpl)
open VG.Proof.HashTable.X86_64 (tables fnsOf names Coh tableOf held_tableOf hashAt_tableOf)
open VG.Proof.HashTable (symsOf symsOf_distinct put5 put5_held put5_below)
open VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaPkcs1Enc.X86_64 (privStack)

/-- The words of `w`'s table, at the addresses `symsOf` gives `vs`' functions. -/
def tw (vs : List MdHash) (w : MdHash) : List (BitVec 64) :=
  [symsOf (names vs) w.H.initN, symsOf (names vs) w.H.updN, symsOf (names vs) w.H.finN,
    BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G), BitVec.ofNat 64 w.mgf.G.len]

/-- A state with `s`'s registers and regions, `w`'s table at `0x300000`,
and `vs`' functions at distinct addresses. -/
def withTable (s : State) (vs : List MdHash) (w : MdHash) : State :=
  { s with
    mem := put5 s.mem 0x300000 ((tw vs w).getD 0 0) ((tw vs w).getD 1 0) ((tw vs w).getD 2 0)
      ((tw vs w).getD 3 0) ((tw vs w).getD 4 0)
    syms := symsOf (names vs) }

theorem withTable_gpr (s : State) (vs : List MdHash) (w : MdHash) : (withTable s vs w).gpr = s.gpr := rfl
theorem withTable_rd (s : State) (vs : List MdHash) (w : MdHash) : (withTable s vs w).rd = s.rd := rfl
theorem withTable_wr (s : State) (vs : List MdHash) (w : MdHash) : (withTable s vs w).wr = s.wr := rfl
theorem withTable_addr (s : State) (vs : List MdHash) (w : MdHash) (j : Nat) :
    stackArgAddr (withTable s vs w) j = stackArgAddr s j := rfl

theorem withTable_arg (s : State) (vs : List MdHash) (w : MdHash) {j : Nat}
    (hj : (stackArgAddr s j).toNat + 8 ≤ 0x300000) : stackArg (withTable s vs w) j = stackArg s j :=
  put5_below hj _ _ _ _ _

/-- The table of `w`, at `0x300000`. -/
theorem withTable_held (s : State) (vs : List MdHash) (w : MdHash) :
    Abi.tableHeld 64 (withTable s vs w).mem 0x300000 (FnTable.words isa (withTable s vs w) (tableOf w)) :=
  put5_held (ws := tw vs w) rfl

/-- The functions' addresses are distinct, in the list of the functions of
both tables. -/
theorem symsOf_distinct2 {ns : List String} (h : ns.length < 2 ^ 32) :
    (ns ++ ns).Pairwise fun f g => f ≠ g → symsOf ns f ≠ symsOf ns g :=
  (List.pairwise_of_forall (R := fun _ _ => True) fun _ _ => trivial).imp_of_mem fun {f g} hf hg _ hne e => by
    have hf' : f ∈ ns := (List.mem_append.mp hf).elim id id
    have hg' : g ∈ ns := (List.mem_append.mp hg).elim id id
    have i1 := List.idxOf_lt_length_of_mem hf'
    have i2 := List.idxOf_lt_length_of_mem hg'
    have e' := congrArg BitVec.toNat e
    simp only [symsOf, BitVec.toNat_ofNat] at e'
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e'
    have hi : ns.idxOf f = ns.idxOf g := by omega
    exact hne (by rw [← List.getElem_idxOf i1, ← List.getElem_idxOf i2]; simp only [hi])

/-! ## Decryption -/

/-- A state meeting `decK.pre` but for the tables: a 512-bit modulus, one-byte
`e`, primes, exponents and `qInv`, an empty label, the stack arguments at
`0x10008`, and both tables' address `0x300000`. -/
def decSatBase : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x1800 | .rcx => 0x2000 | .r8 => 64 | .r9 => 0x3000
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := bif Nat.beq a.toNat 0x10088 then 0x20
    else bif Nat.beq a.toNat 0x10008 then 1 else bif Nat.beq a.toNat 0x10011 then 0x41
    else bif Nat.beq a.toNat 0x10018 then 1 else bif Nat.beq a.toNat 0x10021 then 0x42
    else bif Nat.beq a.toNat 0x10028 then 1 else bif Nat.beq a.toNat 0x10031 then 0x43
    else bif Nat.beq a.toNat 0x10038 then 1 else bif Nat.beq a.toNat 0x10041 then 0x44
    else bif Nat.beq a.toNat 0x10048 then 1 else bif Nat.beq a.toNat 0x10051 then 0x45
    else bif Nat.beq a.toNat 0x10058 then 1 else bif Nat.beq a.toNat 0x10061 then 0x46
    else bif Nat.beq a.toNat 0x10071 then 0x47 else bif Nat.beq a.toNat 0x10078 then 64
    else bif Nat.beq a.toNat 0x10082 then 0x02 else bif Nat.beq a.toNat 0x10089 then 0x08
    else bif Nat.beq a.toNat 0x10092 then 0x30 else bif Nat.beq a.toNat 0x1009A then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩, ⟨0x4500, 1⟩,
    ⟨0x4600, 0⟩, ⟨0x4700, 64⟩, ⟨0x300000, 40⟩, ⟨0x300000, 40⟩, ⟨0x10008, 152⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 2080 * 8⟩]

theorem dec_sat {vs : List MdHash} {w : MdHash} (hw : w ∈ vs)
    (hl : (names vs).length < 2 ^ 32) : ∃ s, (decC (tables vs)).pre s := by
  refine ⟨withTable decSatBase vs w, ?_⟩
  sig_pre [Spec.RsaOaep.decryptTablesContract, Spec.RsaOaep.decryptTablesSig, Spec.RsaOaep.decryptSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argRegs, decStack, privStack, Impl.RsaOaep.X86_64.frameBytes, stackArgs_nineteen, List.append_eq]
  have hA : ∀ j < 19, (stackArgAddr decSatBase j).toNat + 8 ≤ 0x300000 := by decide
  simp only [withTable_arg _ vs w (hA 0 (by decide)), withTable_arg _ vs w (hA 1 (by decide)), withTable_arg _ vs w (hA 2 (by decide)), withTable_arg _ vs w (hA 3 (by decide)), withTable_arg _ vs w (hA 4 (by decide)), withTable_arg _ vs w (hA 5 (by decide)), withTable_arg _ vs w (hA 6 (by decide)), withTable_arg _ vs w (hA 7 (by decide)), withTable_arg _ vs w (hA 8 (by decide)), withTable_arg _ vs w (hA 9 (by decide)), withTable_arg _ vs w (hA 10 (by decide)), withTable_arg _ vs w (hA 11 (by decide)), withTable_arg _ vs w (hA 12 (by decide)), withTable_arg _ vs w (hA 13 (by decide)), withTable_arg _ vs w (hA 14 (by decide)), withTable_arg _ vs w (hA 15 (by decide)), withTable_arg _ vs w (hA 16 (by decide)), withTable_arg _ vs w (hA 17 (by decide)), withTable_arg _ vs w (hA 18 (by decide))]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', withTable_addr]
  sig_pre [Spec.RsaOaep.decryptTablesContract, Spec.RsaOaep.decryptTablesSig, Spec.RsaOaep.decryptSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argRegs, decStack, privStack, Impl.RsaOaep.X86_64.frameBytes, stackArgs_nineteen, List.append_eq]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact ⟨tableOf w, List.mem_map_of_mem hw, by
        rw [show stackArg decSatBase 17 = 0x300000 by decide]; exact withTable_held _ _ _⟩
    | exact ⟨tableOf w, List.mem_map_of_mem hw, by
        rw [show stackArg decSatBase 18 = 0x300000 by decide]; exact withTable_held _ _ _⟩
    | exact symsOf_distinct2 hl
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (intro a h₁ h₂
       set_option linter.unusedSimpArgs false in
       sig_simp_only [Region.Contains, decSatBase, stackArg, stackArgAddr, Mem.readW, Mem.read] at h₁ h₂
       bv_omega)

/-! ## Encryption with a precomputed key -/

/-- A state meeting the encryption's precondition but for the tables: a
512-bit modulus, one-byte `e`, an empty label and message, a seed of
`H.len` bytes at `0x4600`, 16 words of `pre` at `0x5000`, the stack
arguments at `0x10008`, and both tables' address `0x300000`. -/
def encSatBase (H : Spec.Mgf1.Hash) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x3000 | .r9 => 1
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x10030 then BitVec.ofNat 8 H.len
    else if a = 0x10009 then 0x41 else if a = 0x10019 then 0x42 else if a = 0x10029 then 0x46
    else if a = 0x1003A then 0x02 else if a = 0x10040 then 0x20 else if a = 0x10041 then 0x08
    else if a = 0x10049 then 0x50 else if a = 0x10050 then 16 else if a = 0x1005A then 0x30
    else if a = 0x10062 then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4100, 0⟩, ⟨0x4200, 0⟩, ⟨0x4600, H.len⟩, ⟨0x5000, 128⟩,
    ⟨0x300000, 40⟩, ⟨0x300000, 40⟩, ⟨0x10008, 96⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 2080 * 8⟩]

/-- Encryption's precondition, with the tables of `w`. -/
theorem enc_sat {vs : List MdHash} {w : MdHash} (hw : w ∈ vs) (hl : (names vs).length < 2 ^ 32) :
    ∃ s, (Pc.encC (tables vs)).pre s := by
  have hha : ∀ s : State, Spec.HashTable.hashAt 64 (withTable s vs w).mem 0x300000 = some w.mgf.G := fun s =>
    hashAt_tableOf (held_tableOf (withTable_held s vs w)).2.1
  have hH := w.mgf.mem
  generalize w.mgf.G = H at hha hH
  refine ⟨withTable (encSatBase H) vs w, ?_⟩
  have hB : ∀ j < 12, ((0x10000 : Addr) + BitVec.ofNat 64 (8 * (j + 1))).toNat + 8 ≤ 0x300000 := by decide
  have hA : ∀ (G : Spec.Mgf1.Hash), ∀ j < 12, (stackArgAddr (encSatBase G) j).toNat + 8 ≤ 0x300000 :=
    fun _ j hj => hB j hj
  have hha' := hha (encSatBase H)
  simp only [Pbkdf2.Md.X86_64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hH
  rcases hH with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    sig_pre [Spec.RsaOaep.encryptTablesContract, Spec.RsaOaep.encryptTablesSig, Spec.RsaOaep.seedLenOk,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
      argRegs, encStack, Pc.stackArgs_twelve, List.append_eq, List.range, List.range.loop]
    simp only [withTable_arg _ vs w (hA _ 0 (by decide)), withTable_arg _ vs w (hA _ 1 (by decide)), withTable_arg _ vs w (hA _ 2 (by decide)), withTable_arg _ vs w (hA _ 3 (by decide)), withTable_arg _ vs w (hA _ 4 (by decide)), withTable_arg _ vs w (hA _ 5 (by decide)), withTable_arg _ vs w (hA _ 6 (by decide)), withTable_arg _ vs w (hA _ 7 (by decide)), withTable_arg _ vs w (hA _ 8 (by decide)), withTable_arg _ vs w (hA _ 9 (by decide)), withTable_arg _ vs w (hA _ 10 (by decide)), withTable_arg _ vs w (hA _ 11 (by decide))]
    simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq, exists_eq_left', withTable_addr]
    sig_pre [Spec.RsaOaep.encryptTablesContract, Spec.RsaOaep.encryptTablesSig, Spec.RsaOaep.seedLenOk,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
      argRegs, encStack, Pc.stackArgs_twelve, List.append_eq, List.range, List.range.loop]
    sig_and_intros
    all_goals first
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)
      | exact ⟨tableOf w, List.mem_map_of_mem hw, withTable_held _ _ _⟩
      | (intro H' hH'
         rw [show stackArg (encSatBase _) 10 = 0x300000 by decide] at hH'
         obtain rfl := Option.some.inj (hha'.symm.trans hH')
         decide)
      | exact ⟨tableOf w, List.mem_map_of_mem hw, by
          rw [show stackArg (encSatBase _) 11 = 0x300000 by decide]; exact withTable_held _ _ _⟩
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

/-- `vg_rsa_oaep_decrypt`, with the tables of `vs`. -/
theorem dec_ok (vs : List MdHash) (h : OK vs) (v : PrivImpl) :
    Verified target (Impl.RsaOaep.X86_64.decrypt (fnsOf vs) v.name v.code) (decC (tables vs)) :=
  dec_verified h.1 v (let ⟨_, hw⟩ := h.mem; dec_sat hw h.2.1)

/-- `vg_rsa_oaep_encrypt_precomputed`, with the tables of `vs`. -/
theorem enc_ok (vs : List MdHash) (h : OK vs) (v : PublicImpl) :
    Verified target (Impl.RsaOaep.X86_64.Precomputed.encrypt (fnsOf vs) v.name v.code) (Pc.encC (tables vs)) :=
  Pc.code_verified h.1 v (let ⟨_, hw⟩ := h.mem; enc_sat hw h.2.1)

end VG.Proof.RsaOaep.X86_64
