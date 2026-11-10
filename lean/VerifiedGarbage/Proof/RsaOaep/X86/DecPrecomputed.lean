module

public import VerifiedGarbage.Proof.RsaOaep.X86.Inst
public import VerifiedGarbage.Proof.Framework.X86.AppendSlice
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_rsa_oaep_decrypt_precomputed` on x86

`vg_rsa_oaep_decrypt`'s code, which ignores the key's precomputed values
`pre` (`Spec/Rsa/PrivatePrecompute.lean` lets an implementation ignore them),
proven against `vg_rsa_oaep_decrypt_precomputed`'s contract from its own
(`verified_withSlice_tables`), with a state that meets it (`preSat`): that of
`Dec/Sat.lean`, with `p`, `q`, `dP`, `dQ` and `qInv` of 32 bytes and a real
key (`Proof/Rsa/PreKey.lean`).
-/

@[expose] public section
namespace VG.Proof.RsaOaep.X86.Dec
open VG
open VG.X86 hiding frameBytes
open VG.Proof.HashTable.X86 (TVar tables tableOf names withTable withTable_arg held_twL twL)
open VG.Proof.HashTable (symsOf32_distinct2 putWs32 add4_toNat)
open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl)

/-- The contract, with the tables of `vs`. -/
abbrev pspec (vs : List TVar) : Contract isa :=
  Spec.RsaOaep.decryptPrecomputedMdTablesContract
    (abi.withTables Spec.RsaOaep.decryptPrecomputedMdTablesSig [("hash", tables vs), ("mgf1", tables vs)])
    stackBytes

/-! ## A state that meets the contract -/

theorem putWs32_byte {a : Addr} : ∀ {ws : List (BitVec 64)} {m : Mem} {p : Addr},
    a.toNat < p.toNat → p.toNat + 4 * ws.length < 2 ^ 64 → putWs32 m p ws a = m a
  | [], _, _, _, _ => rfl
  | w :: ws, m, p, ha, hp => by
    simp only [List.length_cons] at hp
    have e := add4_toNat (p := p) (by omega)
    simp only [putWs32]
    rw [putWs32_byte (by rw [e]; omega) (by rw [e]; omega)]
    simp only [Mem.writeW, Mem.write]
    split
    · rename_i hh
      rw [BitVec.toNat_sub] at hh
      omega
    · rfl

/-- The arguments of `preState`; the key (`keyMem`) has `n` at `0x2000`,
`p` at `0x4200`, `q` at `0x4300` and `pre` at `0x4800`. -/
def preArgs : List Nat := [0x1000, 64, 0x1100, 0x2000, 64, 0x2100, 1, 0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0x3600, 0, 0x3700, 64, 0x10000, 0x820, 0x300000, 0x300000, 0x4800, 24]

/-- The memory of `preState`: the arguments on the stack from `0x20004`,
and the key. -/
def preMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x20004 i && Nat.blt i 0x20070 then
    BitVec.ofNat 8 (preArgs.getD ((i - 0x20004) / 4) 0 / 256 ^ ((i - 0x20004) % 4))
  else bif keyIn i then keyMem a else 0

/-- The state, but for the table. -/
def preState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := preMem
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩, ⟨0x4600, 32⟩,
    ⟨0x3600, 0⟩, ⟨0x3700, 64⟩, ⟨0x4800, 192⟩, ⟨0x300000, 44⟩, ⟨0x300000, 44⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 8⟩, ⟨0x10000, 2080 * 8⟩, ⟨0x20004, 108⟩]

theorem preState_key (vs : List TVar) (w : TVar) :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt (withTable preState vs w).mem 0x2000 64)
      (Spec.Rsa.bytesAt (withTable preState vs w).mem 0x4200 32)
      (Spec.Rsa.bytesAt (withTable preState vs w).mem 0x4300 32) =
        some (Spec.Rsa.wordsAt (withTable preState vs w).mem 0x4800 24) := by
  refine key_pre_of fun a ha => ?_
  have hlt : a.toNat < 0x20004 ∨ (0x20070 ≤ a.toNat ∧ a.toNat < 0x300000) := by
    simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha; omega
  have hs : (Nat.ble 0x20004 a.toNat && Nat.blt a.toNat 0x20070) = false := by
    refine Bool.eq_false_iff.mpr fun h => ?_
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    omega
  show putWs32 preMem 0x300000 (twL vs w) a = _
  rw [putWs32_byte (by simp; omega) (Proof.HashTable.X86.twL_room vs w)]
  show (bif _ then _ else _) = _
  rw [hs, Bool.cond_false, ha, Bool.cond_true]

theorem preSat {vs : List TVar} {w : TVar} (hw : w ∈ vs) (hl : (names vs).length < 2 ^ 24) :
    ∃ s, (pspec vs).pre s := by
  refine ⟨withTable preState vs w, ?_⟩
  have hK := preState_key vs w
  have hA : ∀ j < 27, (argAddr preState j).toNat + 4 ≤ 0x300000 := by decide
  have a0 : arg preState 0 = 0x1000 := by decide
  have a1 : arg preState 1 = 64 := by decide
  have a2 : arg preState 2 = 0x1100 := by decide
  have a3 : arg preState 3 = 0x2000 := by decide
  have a4 : arg preState 4 = 64 := by decide
  have a5 : arg preState 5 = 0x2100 := by decide
  have a6 : arg preState 6 = 1 := by decide
  have a7 : arg preState 7 = 0x4200 := by decide
  have a8 : arg preState 8 = 32 := by decide
  have a9 : arg preState 9 = 0x4300 := by decide
  have a10 : arg preState 10 = 32 := by decide
  have a11 : arg preState 11 = 0x4400 := by decide
  have a12 : arg preState 12 = 32 := by decide
  have a13 : arg preState 13 = 0x4500 := by decide
  have a14 : arg preState 14 = 32 := by decide
  have a15 : arg preState 15 = 0x4600 := by decide
  have a16 : arg preState 16 = 32 := by decide
  have a17 : arg preState 17 = 0x3600 := by decide
  have a18 : arg preState 18 = 0 := by decide
  have a19 : arg preState 19 = 0x3700 := by decide
  have a20 : arg preState 20 = 64 := by decide
  have a21 : arg preState 21 = 0x10000 := by decide
  have a22 : arg preState 22 = 0x820 := by decide
  have a23 : arg preState 23 = 0x300000 := by decide
  have a24 : arg preState 24 = 0x300000 := by decide
  have a25 : arg preState 25 = 0x4800 := by decide
  have a26 : arg preState 26 = 24 := by decide
  have e : argAddr (withTable preState vs w) 0 = 0x20004 := show argAddr preState 0 = _ by decide
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables,
    Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [withTable_arg _ vs w (hA 0 (by decide)), withTable_arg _ vs w (hA 1 (by decide)), withTable_arg _ vs w (hA 2 (by decide)), withTable_arg _ vs w (hA 3 (by decide)), withTable_arg _ vs w (hA 4 (by decide)), withTable_arg _ vs w (hA 5 (by decide)), withTable_arg _ vs w (hA 6 (by decide)), withTable_arg _ vs w (hA 7 (by decide)), withTable_arg _ vs w (hA 8 (by decide)), withTable_arg _ vs w (hA 9 (by decide)), withTable_arg _ vs w (hA 10 (by decide)), withTable_arg _ vs w (hA 11 (by decide)), withTable_arg _ vs w (hA 12 (by decide)), withTable_arg _ vs w (hA 13 (by decide)), withTable_arg _ vs w (hA 14 (by decide)), withTable_arg _ vs w (hA 15 (by decide)), withTable_arg _ vs w (hA 16 (by decide)), withTable_arg _ vs w (hA 17 (by decide)), withTable_arg _ vs w (hA 18 (by decide)), withTable_arg _ vs w (hA 19 (by decide)), withTable_arg _ vs w (hA 20 (by decide)), withTable_arg _ vs w (hA 21 (by decide)), withTable_arg _ vs w (hA 22 (by decide)), withTable_arg _ vs w (hA 23 (by decide)), withTable_arg _ vs w (hA 24 (by decide)), withTable_arg _ vs w (hA 25 (by decide)), withTable_arg _ vs w (hA 26 (by decide))]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, e]
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables,
    Sig.wordIndex, abi, argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals try (exact ⟨tableOf w, List.mem_map_of_mem hw, held_twL _ _ _ rfl⟩)
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (rw [List.append_eq, List.append_eq, List.append_nil]; exact symsOf32_distinct2 hl)
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  rw [show BitVec.setWidth 64 (8192 : BitVec 32) = (0x2000 : Addr) by decide,
    show BitVec.setWidth 64 (16896 : BitVec 32) = (0x4200 : Addr) by decide,
    show BitVec.setWidth 64 (17152 : BitVec 32) = (0x4300 : Addr) by decide,
    show BitVec.setWidth 64 (18432 : BitVec 32) = (0x4800 : Addr) by decide,
    show BitVec.toNat (64 : BitVec 32) = 64 by decide, show BitVec.toNat (32 : BitVec 32) = 32 by decide,
    show BitVec.toNat (24 : BitVec 32) = 24 by decide]
  exact hK

/-! ## The code -/

theorem wordVals_eq (s : State) : wordVals 25 s = [argVal s 32 0, argVal s 32 1, argVal s 32 2, argVal s 32 3, argVal s 32 4, argVal s 32 5, argVal s 32 6, argVal s 32 7, argVal s 32 8, argVal s 32 9, argVal s 32 10, argVal s 32 11, argVal s 32 12, argVal s 32 13, argVal s 32 14, argVal s 32 15, argVal s 32 16, argVal s 32 17, argVal s 32 18, argVal s 32 19, argVal s 32 20, argVal s 32 21, argVal s 32 22, argVal s 32 23, argVal s 32 24] := rfl

/-- `Spec.RsaOaep.decryptMdTablesSig.words 32`. -/
abbrev sigWords : List ArgWord :=
  [.addr, .int 32, .addr, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .addr]

theorem decPrecomputed_verified {vs : List TVar} (hok : OK vs) (c : CrtImpl) :
    Verified target (decCode vs c) (pspec vs) := by
  refine verified_withSlice_tables (sig := Spec.RsaOaep.decryptMdTablesSig) (nm := "pre") (e := .u64)
    (ln := "pre_len")
    (fun u hu => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> exact ⟨_, rfl, by decide⟩)
    (by decide) (by decide) (Proof.RsaOaep.X86.dec_ok vs hok c) ?_ ?_ ?_
    (let ⟨_, hw⟩ := hok.mem; preSat hw hok.2.1)
  · intro s h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, -, -⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  · intro s m' v hp hq
    exact hq
  · intro s₁ s₂ _ _ hpo h
    have e4 := hpo 4 (by decide)
    have e6 := hpo 6 (by decide)
    have hl : (Spec.RsaOaep.decryptMdTablesSig.words 32).length = 25 := by decide
    simp only [hl, sliceVals, wordVals_eq, List.cons_append, List.nil_append] at h e4 e6 ⊢
    change Curry.apply (α := Mem → List Nat) (sigWords ++ [.addr, .int 32]) _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) (sigWords ++ [.addr, .int 32]) _ _ s₂.mem at h
    change Curry.apply (α := Mem → List Nat) sigWords _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) sigWords _ _ s₂.mem
    change (argVal s₁ 32 4).setWidth 32 = (argVal s₂ 32 4).setWidth 32 at e4
    change (argVal s₁ 32 6).setWidth 32 = (argVal s₂ 32 6).setWidth 32 at e6
    dsimp only [sigWords, List.cons_append, List.nil_append, Curry.apply, ArgWord.ofRaw] at h ⊢
    refine List.append_inj_left h ?_
    simp only [List.length_map, List.length_append, Proof.Rsa.bytesAt_length', e4, e6]

end VG.Proof.RsaOaep.X86.Dec
