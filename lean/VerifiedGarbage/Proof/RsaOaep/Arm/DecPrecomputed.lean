module

public import VerifiedGarbage.Proof.RsaOaep.Arm.Inst
public import VerifiedGarbage.Proof.Framework.Arm.AppendSlice
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_rsa_oaep_decrypt_precomputed` on ARMv7

`vg_rsa_oaep_decrypt`'s code, which ignores the key's precomputed values
`pre` (`Spec/Rsa/PrivatePrecompute.lean` lets an implementation ignore them),
proven against `vg_rsa_oaep_decrypt_precomputed`'s contract from its own
(`verified_withSlice_tables`), with a state that meets it (`preSat`): that of
`DecSat.lean`, with `p`, `q`, `dP`, `dQ` and `qInv` of 32 bytes and a real
key (`Proof/Rsa/PreKey.lean`).
-/

@[expose] public section
namespace VG.Proof.RsaOaep.Arm.Dec
open VG VG.Arm
open VG.Proof.HashTable.Arm (TVar tables tableOf names withTable held_twL withTable_below twL)
open VG.Proof.HashTable (symsOf32_distinct2 putWs32 add4_toNat)
open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)

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

/-- The stack arguments of `preState`; the key (`keyMem`) has `n` at
`0x2000`, `p` at `0x4200`, `q` at `0x4300` and `pre` at `0x4800`. -/
def preArgs : List Nat := [64, 0x2100, 1, 0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0x3600, 0, 0x3700, 64, 0x10000, 0x820, 0x300000, 0x300000, 0x4800, 24]

/-- The memory of `preState`: the stack arguments from `0x8000`, and the
key. -/
def preMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x8000 i && Nat.blt i 0x805c then
    BitVec.ofNat 8 (preArgs.getD ((i - 0x8000) / 4) 0 / 256 ^ ((i - 0x8000) % 4))
  else bif keyIn i then keyMem a else 0

/-- The state, but for the table. -/
def preState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x1100 | .r3 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem := preMem
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩, ⟨0x4600, 32⟩,
    ⟨0x3600, 0⟩, ⟨0x3700, 64⟩, ⟨0x4800, 192⟩, ⟨0x300000, 44⟩, ⟨0x300000, 44⟩, ⟨0x8000, 92⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 8⟩, ⟨0x10000, 2080 * 8⟩]

theorem preState_key (vs : List TVar) (w : TVar) :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt (withTable preState vs w).mem 0x2000 64)
      (Spec.Rsa.bytesAt (withTable preState vs w).mem 0x4200 32)
      (Spec.Rsa.bytesAt (withTable preState vs w).mem 0x4300 32) =
        some (Spec.Rsa.wordsAt (withTable preState vs w).mem 0x4800 24) := by
  refine key_pre_of fun a ha => ?_
  have hlt : a.toNat < 0x8000 := by
    simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha; omega
  have hs : (Nat.ble 0x8000 a.toNat && Nat.blt a.toNat 0x805c) = false := by
    refine Bool.eq_false_iff.mpr fun h => ?_
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    omega
  show putWs32 preMem 0x300000 (twL vs w) a = _
  rw [putWs32_byte (by simp; omega) (Proof.HashTable.Arm.twL_room vs w)]
  show (bif _ then _ else _) = _
  rw [hs, Bool.cond_false, ha, Bool.cond_true]

theorem preSat {vs : List TVar} {w : TVar} (hw : w ∈ vs) (hl : (names vs).length < 2 ^ 24) :
    ∃ s, (pspec vs).pre s := by
  refine ⟨withTable preState vs w, ?_⟩
  have hK := preState_key vs w
  have hA : ∀ j < 23, (stackArgAddr preState j).toNat + 4 ≤ 0x300000 := by
    intro j hj
    simp only [stackArgAddr, State.addr, show preState.sp = 0x8000 from rfl, BitVec.toNat_setWidth,
      BitVec.toNat_add, BitVec.toNat_ofNat, show BitVec.toNat (32768 : BitVec 32) = 32768 from rfl]
    omega
  have a0 : stackArg (withTable preState vs w) 0 = 64 := (withTable_below _ _ _ (hA 0 (by decide))).trans (by decide)
  have a1 : stackArg (withTable preState vs w) 1 = 0x2100 := (withTable_below _ _ _ (hA 1 (by decide))).trans (by decide)
  have a2 : stackArg (withTable preState vs w) 2 = 1 := (withTable_below _ _ _ (hA 2 (by decide))).trans (by decide)
  have a3 : stackArg (withTable preState vs w) 3 = 0x4200 := (withTable_below _ _ _ (hA 3 (by decide))).trans (by decide)
  have a4 : stackArg (withTable preState vs w) 4 = 32 := (withTable_below _ _ _ (hA 4 (by decide))).trans (by decide)
  have a5 : stackArg (withTable preState vs w) 5 = 0x4300 := (withTable_below _ _ _ (hA 5 (by decide))).trans (by decide)
  have a6 : stackArg (withTable preState vs w) 6 = 32 := (withTable_below _ _ _ (hA 6 (by decide))).trans (by decide)
  have a7 : stackArg (withTable preState vs w) 7 = 0x4400 := (withTable_below _ _ _ (hA 7 (by decide))).trans (by decide)
  have a8 : stackArg (withTable preState vs w) 8 = 32 := (withTable_below _ _ _ (hA 8 (by decide))).trans (by decide)
  have a9 : stackArg (withTable preState vs w) 9 = 0x4500 := (withTable_below _ _ _ (hA 9 (by decide))).trans (by decide)
  have a10 : stackArg (withTable preState vs w) 10 = 32 := (withTable_below _ _ _ (hA 10 (by decide))).trans (by decide)
  have a11 : stackArg (withTable preState vs w) 11 = 0x4600 := (withTable_below _ _ _ (hA 11 (by decide))).trans (by decide)
  have a12 : stackArg (withTable preState vs w) 12 = 32 := (withTable_below _ _ _ (hA 12 (by decide))).trans (by decide)
  have a13 : stackArg (withTable preState vs w) 13 = 0x3600 := (withTable_below _ _ _ (hA 13 (by decide))).trans (by decide)
  have a14 : stackArg (withTable preState vs w) 14 = 0 := (withTable_below _ _ _ (hA 14 (by decide))).trans (by decide)
  have a15 : stackArg (withTable preState vs w) 15 = 0x3700 := (withTable_below _ _ _ (hA 15 (by decide))).trans (by decide)
  have a16 : stackArg (withTable preState vs w) 16 = 64 := (withTable_below _ _ _ (hA 16 (by decide))).trans (by decide)
  have a17 : stackArg (withTable preState vs w) 17 = 0x10000 := (withTable_below _ _ _ (hA 17 (by decide))).trans (by decide)
  have a18 : stackArg (withTable preState vs w) 18 = 0x820 := (withTable_below _ _ _ (hA 18 (by decide))).trans (by decide)
  have a19 : stackArg (withTable preState vs w) 19 = 0x300000 := (withTable_below _ _ _ (hA 19 (by decide))).trans (by decide)
  have a20 : stackArg (withTable preState vs w) 20 = 0x300000 := (withTable_below _ _ _ (hA 20 (by decide))).trans (by decide)
  have a21 : stackArg (withTable preState vs w) 21 = 0x4800 := (withTable_below _ _ _ (hA 21 (by decide))).trans (by decide)
  have a22 : stackArg (withTable preState vs w) 22 = 24 := (withTable_below _ _ _ (hA 22 (by decide))).trans (by decide)
  have e : stackArgAddr (withTable preState vs w) 0 = 0x8000 := show stackArgAddr preState 0 = _ by decide
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables,
    Sig.wordIndex, abi, argRegs, reduceClassify, Loc.val]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, e]
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables,
    Sig.wordIndex, abi, argRegs, reduceClassify, Loc.val]
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

theorem wordVals_eq (s : State) : wordVals 25 s = [Loc.val s (locAt 0), Loc.val s (locAt 1), Loc.val s (locAt 2), Loc.val s (locAt 3), Loc.val s (locAt 4), Loc.val s (locAt 5), Loc.val s (locAt 6), Loc.val s (locAt 7), Loc.val s (locAt 8), Loc.val s (locAt 9), Loc.val s (locAt 10), Loc.val s (locAt 11), Loc.val s (locAt 12), Loc.val s (locAt 13), Loc.val s (locAt 14), Loc.val s (locAt 15), Loc.val s (locAt 16), Loc.val s (locAt 17), Loc.val s (locAt 18), Loc.val s (locAt 19), Loc.val s (locAt 20), Loc.val s (locAt 21), Loc.val s (locAt 22), Loc.val s (locAt 23), Loc.val s (locAt 24)] := rfl

/-- `Spec.RsaOaep.decryptMdTablesSig.words 32`. -/
abbrev sigWords : List ArgWord :=
  [.addr, .int 32, .addr, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .addr]

theorem decPrecomputed_verified {vs : List TVar} (hok : Proof.RsaOaep.Arm.OK vs) (c : Proof.Rsa.Arm.CrtImpl) :
    Verified target (decCode vs c) (pspec vs) := by
  refine verified_withSlice_tables (sig := Spec.RsaOaep.decryptMdTablesSig) (nm := "pre") (e := .u64)
    (ln := "pre_len")
    (fun u hu => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> exact ⟨_, rfl, by decide⟩)
    (by decide) (by decide) (Proof.RsaOaep.Arm.dec_ok vs hok c) ?_ ?_ ?_
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
    change (Loc.val s₁ (locAt 4)).setWidth 32 = (Loc.val s₂ (locAt 4)).setWidth 32 at e4
    change (Loc.val s₁ (locAt 6)).setWidth 32 = (Loc.val s₂ (locAt 6)).setWidth 32 at e6
    dsimp only [sigWords, List.cons_append, List.nil_append, Curry.apply, ArgWord.ofRaw] at h ⊢
    refine List.append_inj_left h ?_
    simp only [List.length_map, List.length_append, Proof.Rsa.bytesAt_length', e4, e6]

end VG.Proof.RsaOaep.Arm.Dec
