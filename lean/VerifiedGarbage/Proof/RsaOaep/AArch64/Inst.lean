module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncVerified
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecVerified
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Callees
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
import Mathlib.Data.Nat.Basic

/-!
# RSAES-OAEP on AArch64: the instances emitted

Which `MdHash` variants of the label's hash function encryption and
decryption are emitted for, and their names, as on x86-64
(`Proof/RsaOaep/X86_64/Sp.lean`); states meeting both contracts, with MGF1's
table at `0x300000` (`withTable`); and the instances' proofs against the
contracts the registrations state (`dec_ok`, `enc_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK MgfLink MdHash mdHashes)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.HashTable.AArch64 (tables fnsOf names Coh tableOf)
open VG.Proof.HashTable (symsOf symsOf_distinct put5 put5_held put5_below)

namespace Inst

/-- Whether `vg_rsa_oaep_<H>_mgf1_*` is emitted for `H`'s variant `v`: for
every hash function but MD5. -/
def emitted (v : MdHash) : Bool := v.mgf.G.rust != "md5"

/-- The tags and suffixes of an instance's name (`Emit.qualifiedName`): `H`'s
variant tagged with `H`. -/
def parts (v : MdHash) : List (String × String) := [(v.mgf.G.rust, v.suffix)]

end Inst

/-! ## States holding a table -/

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

theorem withTable_addr (s : State) (vs : List MdHash) (w : MdHash) (j : Nat) :
    stackArgAddr (withTable s vs w) j = stackArgAddr s j := rfl

theorem withTable_arg (s : State) (vs : List MdHash) (w : MdHash) {j : Nat}
    (hj : (stackArgAddr s j).toNat + 8 ≤ 0x300000) : stackArg (withTable s vs w) j = stackArg s j :=
  put5_below hj _ _ _ _ _

/-- The table of `w`, at `0x300000`. -/
theorem withTable_held (s : State) (vs : List MdHash) (w : MdHash) :
    Abi.tableHeld 64 (withTable s vs w).mem 0x300000 (FnTable.words isa (withTable s vs w) (tableOf w)) :=
  put5_held (ws := tw vs w) rfl

/-! ## Decryption -/

/-- A state meeting decryption's contract but for the table: a 512-bit
modulus, one-byte `e`, primes, exponents and `qInv`, an empty label, a
working space of 2080 words, the stack arguments at `0x10000`, and the
table's address `0x300000`. -/
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
    else bif Nat.beq a.toNat 0x1007A then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩, ⟨0x4500, 1⟩, ⟨0x4600, 1⟩,
    ⟨0x4700, 0⟩, ⟨0x4100, 64⟩, ⟨0x300000, 40⟩, ⟨0x10000, 128⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 16640⟩]

theorem dec_sat (H : Spec.Mgf1.Hash) {vs : List MdHash} {w : MdHash} (hw : w ∈ vs)
    (hl : (names vs).length < 2 ^ 32) (c : Proof.Rsa.AArch64.CrtImpl) :
    ∃ s, (Dec.decSpec H (tables vs) ((RsaPkcs1Enc.AArch64.privOf c).S + 1)).pre s := by
  refine ⟨withTable decSatBase vs w, ?_⟩
  have hA : ∀ j < 16, (stackArgAddr decSatBase j).toNat + 8 ≤ 0x300000 := by decide
  have hS : (RsaPkcs1Enc.AArch64.privOf c).S + 1 = 3248 := by
    rw [← Nat.add_right_cancel_iff (n := 288), ← Dec.decStack_eq]; rfl
  rw [hS]
  sig_pre [Spec.RsaOaep.decryptTableContract, Spec.RsaOaep.decryptTableSig, Spec.RsaOaep.decryptSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
  simp only [withTable_arg _ vs w (hA 0 (by decide)), withTable_arg _ vs w (hA 1 (by decide)),
    withTable_arg _ vs w (hA 2 (by decide)), withTable_arg _ vs w (hA 3 (by decide)),
    withTable_arg _ vs w (hA 4 (by decide)), withTable_arg _ vs w (hA 5 (by decide)),
    withTable_arg _ vs w (hA 6 (by decide)), withTable_arg _ vs w (hA 7 (by decide)),
    withTable_arg _ vs w (hA 8 (by decide)), withTable_arg _ vs w (hA 9 (by decide)),
    withTable_arg _ vs w (hA 10 (by decide)), withTable_arg _ vs w (hA 11 (by decide)),
    withTable_arg _ vs w (hA 12 (by decide)), withTable_arg _ vs w (hA 13 (by decide)),
    withTable_arg _ vs w (hA 14 (by decide)), withTable_arg _ vs w (hA 15 (by decide))]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', withTable_addr]
  sig_pre [Spec.RsaOaep.decryptTableContract, Spec.RsaOaep.decryptTableSig, Spec.RsaOaep.decryptSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact ⟨tableOf w, List.mem_map_of_mem hw, by
        rw [show stackArg decSatBase 15 = 0x300000 by decide]; exact withTable_held _ _ _⟩
    | exact symsOf_distinct hl
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (intro a h₁ h₂
       set_option linter.unusedSimpArgs false in
       sig_simp_only [Region.Contains, decSatBase, stackArg, stackArgAddr, Mem.readW, Mem.read] at h₁ h₂
       bv_omega)

/-! ## Encryption with a precomputed key -/

/-- A state meeting encryption's contract for `H` but for the table: a
512-bit modulus, a one-byte `e`, an empty label and message, `H`'s seed, a
working space of 2080 words, 16 words of `pre` at `0x5000`, the stack
arguments at `0x10000`, and the table's address `0x300000`. -/
def encSatBase (H : Spec.Mgf1.Hash) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 64 | .x4 => 0x3000 | .x5 => 1 | .x6 => 0x4000
    | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10020 then 0x20
    else bif Nat.beq a.toNat 0x10001 then 0x41 else bif Nat.beq a.toNat 0x10011 then 0x42
    else bif Nat.beq a.toNat 0x1001A then 0x02 else bif Nat.beq a.toNat 0x10021 then 0x08
    else bif Nat.beq a.toNat 0x10029 then 0x50 else bif Nat.beq a.toNat 0x10030 then 16
    else bif Nat.beq a.toNat 0x1003A then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 0⟩, ⟨0x4100, 0⟩, ⟨0x4200, H.len⟩, ⟨0x5000, 128⟩,
    ⟨0x300000, 40⟩, ⟨0x10000, 64⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 16640⟩]

theorem enc_sat {H : Spec.Mgf1.Hash} (hH : H ∈ mdHashes) {vs : List MdHash} {w : MdHash} (hw : w ∈ vs)
    (hl : (names vs).length < 2 ^ 32) (v : Proof.Rsa.AArch64.PublicImpl) :
    ∃ s, (Enc.encSpec H (tables vs) (Enc.encP (RsaPkcs1Sig.AArch64.pdOf v))).pre s := by
  refine ⟨withTable (encSatBase H) vs w, ?_⟩
  have hB : ∀ j < 8, ((0x10000 : Addr) + BitVec.ofNat 64 (8 * j)).toNat + 8 ≤ 0x300000 := by decide
  have hA : ∀ (G : Spec.Mgf1.Hash), ∀ j < 8, (stackArgAddr (encSatBase G) j).toNat + 8 ≤ 0x300000 :=
    fun _ j hj => hB j hj
  have hP : Enc.encP (RsaPkcs1Sig.AArch64.pdOf v) = 16 := rfl
  rw [hP]
  simp only [mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hH
  rcases hH with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    sig_pre [Spec.RsaOaep.encryptTableContract, Spec.RsaOaep.encryptTableSig, Spec.RsaOaep.encryptPrecomputedSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
    simp only [withTable_arg _ vs w (hA _ 0 (by decide)), withTable_arg _ vs w (hA _ 1 (by decide)),
      withTable_arg _ vs w (hA _ 2 (by decide)), withTable_arg _ vs w (hA _ 3 (by decide)),
      withTable_arg _ vs w (hA _ 4 (by decide)), withTable_arg _ vs w (hA _ 5 (by decide)),
      withTable_arg _ vs w (hA _ 6 (by decide)), withTable_arg _ vs w (hA _ 7 (by decide))]
    simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq, exists_eq_left', withTable_addr]
    sig_pre [Spec.RsaOaep.encryptTableContract, Spec.RsaOaep.encryptTableSig, Spec.RsaOaep.encryptPrecomputedSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
    sig_and_intros
    all_goals first
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)
      | exact ⟨tableOf w, List.mem_map_of_mem hw, by
          rw [show stackArg (encSatBase _) 7 = 0x300000 by decide]; exact withTable_held _ _ _⟩
      | exact symsOf_distinct hl
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

/-- `vg_rsa_oaep_<H>_mgf1_decrypt`, for `v`'s variant of `H`, with the
tables of `vs` and the private-key operation of `c`. -/
theorem dec_ok (v : MdHash) (vs : List MdHash) (h : OK vs) (c : Proof.Rsa.AArch64.CrtImpl) :
    Verified AArch64.target (Impl.RsaOaep.AArch64.decrypt v.H (fnsOf vs) (RsaPkcs1Enc.AArch64.privOf c).name
        (RsaPkcs1Enc.AArch64.privOf c).code)
      (Spec.RsaOaep.decryptTableContract v.mgf.G
        (AArch64.abi.withTables Spec.RsaOaep.decryptTableSig [("mgf1", tables vs)])
        (Dec.decStack (RsaPkcs1Enc.AArch64.privOf c))) := by
  rw [Dec.decStack_eq]
  exact Dec.dec_verified v.ok.stream v.mgf.hash v.mgf.len (mgf_valid v.mgf) h.1 _
    (let ⟨_, hw⟩ := h.mem; dec_sat v.mgf.G hw h.2.1 c)

/-- `vg_rsa_oaep_<H>_mgf1_encrypt_precomputed`, for `v`'s variant of `H`,
with the tables of `vs` and the precomputed public operation of `c`. -/
theorem enc_ok (v : MdHash) (vs : List MdHash) (h : OK vs) (c : Proof.Rsa.AArch64.PublicImpl) :
    Verified AArch64.target (Impl.RsaOaep.AArch64.Precomputed.encrypt v.H (fnsOf vs)
        (RsaPkcs1Sig.AArch64.pdOf c).name (RsaPkcs1Sig.AArch64.pdOf c).code)
      (Spec.RsaOaep.encryptTableContract v.mgf.G
        (AArch64.abi.withTables (Spec.RsaOaep.encryptTableSig v.mgf.G) [("mgf1", tables vs)])
        (Enc.encStack (RsaPkcs1Sig.AArch64.pdOf c))) :=
  Enc.enc_verified v.ok.stream v.mgf.hash v.mgf.len (mgf_valid v.mgf) h.1 _
    (let ⟨_, hw⟩ := h.mem; enc_sat v.mgf.mem hw h.2.1 c)

end VG.Proof.RsaOaep.AArch64
