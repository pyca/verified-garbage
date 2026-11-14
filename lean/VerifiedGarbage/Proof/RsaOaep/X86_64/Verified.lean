module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecCT
public import VerifiedGarbage.Proof.RsaOaep.X86_64.PcCT
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl

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
open VG.Proof.Rsa.X86_64 (PublicImpl)
open VG.Proof.HashTable.X86_64 (tables fnsOf names Coh tableOf held_tableOf hashAt_tableOf)
open VG.Proof.HashTable (symsOf symsOf_distinct symsOf_distinct2 putWs putWs_out putWs_held)
open VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaPkcs1Enc.X86_64 (privStack)

/-- The words of `w`'s table, its functions at the addresses `symsOf` gives
`vs`' functions. -/
def tw (vs : List MdHash) (w : MdHash) : List (BitVec 64) :=
  (tableOf w).fns.map (symsOf (names vs)) ++ (tableOf w).data

/-- The words of `w`'s table, one by one: a list whose cells unfold without
evaluating the words (`tw_eq`). -/
def twL (vs : List MdHash) (w : MdHash) : List (BitVec 64) :=
  [(tw vs w).getD 0 0, (tw vs w).getD 1 0, (tw vs w).getD 2 0, (tw vs w).getD 3 0, (tw vs w).getD 4 0,
    (tw vs w).getD 5 0, (tw vs w).getD 6 0, (tw vs w).getD 7 0, (tw vs w).getD 8 0, (tw vs w).getD 9 0,
    (tw vs w).getD 10 0]

theorem tw_eq (vs : List MdHash) (w : MdHash) : twL vs w = tw vs w := rfl

theorem twL_room (vs : List MdHash) (w : MdHash) :
    (0x300000 : Addr).toNat + 8 * (twL vs w).length < 2 ^ 64 := by
  simp only [twL, List.length_cons, List.length_nil]; decide

/-- A state with `s`'s registers and regions, `w`'s table at `0x300000`,
and `vs`' functions at distinct addresses. -/
def withTable (s : State) (vs : List MdHash) (w : MdHash) : State :=
  { s with mem := putWs s.mem 0x300000 (twL vs w), syms := symsOf (names vs) }

theorem withTable_addr (s : State) (vs : List MdHash) (w : MdHash) (j : Nat) :
    stackArgAddr (withTable s vs w) j = stackArgAddr s j := rfl

theorem withTable_arg (s : State) (vs : List MdHash) (w : MdHash) {j : Nat}
    (hj : (stackArgAddr s j).toNat + 8 ≤ 0x300000) : stackArg (withTable s vs w) j = stackArg s j :=
  putWs_out (m := s.mem) (a := stackArgAddr s j) (ws := twL vs w) (.inl (by simpa using hj)) (twL_room vs w)
    (by omega_using [hj])

/-- `w`'s table at `0x300000`, in any memory `putWs` writes it to, with
`vs`' functions at the addresses `symsOf` gives them: a statement about the
memory as the contracts unfold it, which `exact` matches without unfolding
`putWs`. -/
theorem held_twL (m : Mem) (vs : List MdHash) (w : MdHash) {st : State} (hs : st.syms = symsOf (names vs)) :
    Abi.tableHeld 64 (putWs m 0x300000 (twL vs w)) 0x300000 (FnTable.words isa st (tableOf w)) := by
  have h := putWs_held (m := m) (p := 0x300000) (ws := twL vs w) (twL_room vs w)
  rw [tw_eq] at h
  have e : FnTable.words isa st (tableOf w) = tw vs w := by
    simp only [FnTable.words, tw]; rw [hs]
  rwa [e]

/-- The table of `w`, at `0x300000`. -/
theorem withTable_held (s : State) (vs : List MdHash) (w : MdHash) :
    Abi.tableHeld 64 (withTable s vs w).mem 0x300000 (FnTable.words isa (withTable s vs w) (tableOf w)) :=
  held_twL _ _ _ rfl

/-! ## Decryption -/

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
    ⟨0x300000, 88⟩, ⟨0x300000, 88⟩, ⟨0x10008, 96⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 2080 * 8⟩]

/-- Encryption's precondition, with the tables of `w`. -/
theorem enc_sat {vs : List MdHash} {w : MdHash} (hw : w ∈ vs) (hl : (names vs).length < 2 ^ 32) :
    ∃ s, (Pc.encC (tables vs)).pre s := by
  have hha : ∀ s : State, Spec.MdHashTable.hashAt 64 (withTable s vs w).mem 0x300000 = some w.mgf.G := fun s =>
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
    sig_pre [Spec.RsaOaep.encryptMdTablesContract, Spec.RsaOaep.encryptMdTablesSig, Spec.RsaOaep.seedLenMdOk,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
      argRegs, encStack, Pc.stackArgs_twelve, List.append_eq, List.range, List.range.loop]
    simp only [withTable_arg _ vs w (hA _ 0 (by decide)), withTable_arg _ vs w (hA _ 1 (by decide)), withTable_arg _ vs w (hA _ 2 (by decide)), withTable_arg _ vs w (hA _ 3 (by decide)), withTable_arg _ vs w (hA _ 4 (by decide)), withTable_arg _ vs w (hA _ 5 (by decide)), withTable_arg _ vs w (hA _ 6 (by decide)), withTable_arg _ vs w (hA _ 7 (by decide)), withTable_arg _ vs w (hA _ 8 (by decide)), withTable_arg _ vs w (hA _ 9 (by decide)), withTable_arg _ vs w (hA _ 10 (by decide)), withTable_arg _ vs w (hA _ 11 (by decide))]
    simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq, exists_eq_left', withTable_addr]
    sig_pre [Spec.RsaOaep.encryptMdTablesContract, Spec.RsaOaep.encryptMdTablesSig, Spec.RsaOaep.seedLenMdOk,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
      argRegs, encStack, Pc.stackArgs_twelve, List.append_eq, List.range, List.range.loop]
    sig_and_intros
    all_goals first
      | exact ⟨tableOf w, List.mem_map_of_mem hw, held_twL _ _ _ rfl⟩
      | exact ⟨tableOf w, List.mem_map_of_mem hw, by
          rw [show stackArg (encSatBase _) 11 = 0x300000 by decide]; exact held_twL _ _ _ rfl⟩
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)
      | (intro H' hH'
         rw [show stackArg (encSatBase _) 10 = 0x300000 by decide] at hH'
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

/-- `vg_rsa_oaep_encrypt_precomputed`, with the tables of `vs`. -/
theorem enc_ok (vs : List MdHash) (h : OK vs) (v : PublicImpl) :
    Verified target (Impl.RsaOaep.X86_64.Precomputed.encrypt (fnsOf vs) v.name v.code) (Pc.encC (tables vs)) :=
  Pc.code_verified h.1 v (let ⟨_, hw⟩ := h.mem; enc_sat hw h.2.1)

end VG.Proof.RsaOaep.X86_64
