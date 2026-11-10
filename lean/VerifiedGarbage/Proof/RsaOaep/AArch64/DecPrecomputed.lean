module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.Inst
public import VerifiedGarbage.Proof.Framework.AArch64.AppendSlice
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_rsa_oaep_decrypt_precomputed` on AArch64

`vg_rsa_oaep_decrypt`'s code, which ignores the key's precomputed values
`pre` (`Spec/Rsa/PrivatePrecompute.lean` lets an implementation ignore them),
proven against `vg_rsa_oaep_decrypt_precomputed`'s contract from its own
(`verified_withSlice_tables`), with a state that meets it (`preSat`): that of
`Inst.lean`'s `dec_sat`, with `p`, `q`, `dP`, `dQ` and `qInv` of 32 bytes and a
real key (`Proof/Rsa/PreKey.lean`).
-/

@[expose] public section
namespace VG.Proof.RsaOaep.AArch64
open VG VG.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.HashTable.AArch64 (tables fnsOf names tableOf)
open VG.Proof.HashTable (symsOf_distinct2 putWs add8_toNat)
open VG.Proof.MdHashTable.AArch64 (withTable held_twL twL twL_room)
open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)

/-- The contract, with the tables of `vs` and the callee `c`. -/
abbrev pspec (vs : List MdHash) (c : Proof.Rsa.AArch64.CrtImpl) : Contract isa :=
  Spec.RsaOaep.decryptPrecomputedMdTablesContract
    (AArch64.abi.withTables Spec.RsaOaep.decryptPrecomputedMdTablesSig [("hash", tables vs), ("mgf1", tables vs)])
    (Dec.decStack (RsaPkcs1Enc.AArch64.privOf c))

/-! ## A state that meets the contract -/

theorem putWs_byte {a : Addr} : ∀ {ws : List (BitVec 64)} {m : Mem} {p : Addr},
    a.toNat < p.toNat → p.toNat + 8 * ws.length < 2 ^ 64 → putWs m p ws a = m a
  | [], _, _, _, _ => rfl
  | w :: ws, m, p, ha, hp => by
    simp only [List.length_cons] at hp
    have e := add8_toNat (p := p) (by omega)
    simp only [putWs]
    rw [putWs_byte (by rw [e]; omega) (by rw [e]; omega)]
    simp only [Mem.writeW, Mem.write]
    split
    · rename_i hh
      rw [BitVec.toNat_sub] at hh
      omega
    · rfl

/-- The stack arguments of `preState`; the key (`keyMem`) has `n` at
`0x2000`, `p` at `0x4200`, `q` at `0x4300` and `pre` at `0x4800`. -/
def preArgs : List Nat := [32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0x4700, 0, 0x4100, 64, 0x20000, 0x820, 0x300000, 0x300000, 0x4800, 24]

/-- The memory of `preState`: the stack arguments from `0x10000`, and the
key. -/
def preMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x10000 i && Nat.blt i 0x10098 then
    BitVec.ofNat 8 (preArgs.getD ((i - 0x10000) / 8) 0 / 256 ^ ((i - 0x10000) % 8))
  else bif keyIn i then keyMem a else 0

/-- `decSatBase` with the key and its precomputed values. -/
def preState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x1800 | .x3 => 0x2000 | .x4 => 64 | .x5 => 0x3000 | .x6 => 1
    | .x7 => 0x4200 | _ => 0
  sp := 0x10000
  mem := preMem
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩, ⟨0x4600, 32⟩,
    ⟨0x4700, 0⟩, ⟨0x4100, 64⟩, ⟨0x4800, 192⟩, ⟨0x300000, 88⟩, ⟨0x300000, 88⟩, ⟨0x10000, 152⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 16640⟩]

theorem preState_key (vs : List MdHash) (w : MdHash) :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt (withTable preState vs w).mem 0x2000 64)
      (Spec.Rsa.bytesAt (withTable preState vs w).mem 0x4200 32)
      (Spec.Rsa.bytesAt (withTable preState vs w).mem 0x4300 32) =
        some (Spec.Rsa.wordsAt (withTable preState vs w).mem 0x4800 24) := by
  refine key_pre_of fun a ha => ?_
  have hlt : a.toNat < 0x10000 := by
    simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha; omega
  have hs : (Nat.ble 0x10000 a.toNat && Nat.blt a.toNat 0x10098) = false := by
    refine Bool.eq_false_iff.mpr fun h => ?_
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    omega
  show putWs preMem 0x300000 (twL vs w) a = _
  rw [putWs_byte (by simp; omega) (twL_room vs w)]
  show (bif _ then _ else _) = _
  rw [hs, Bool.cond_false, ha, Bool.cond_true]

theorem preSat {vs : List MdHash} {w : MdHash} (hw : w ∈ vs) (hl : (names vs).length < 2 ^ 32)
    (c : Proof.Rsa.AArch64.CrtImpl) : ∃ s, (pspec vs c).pre s := by
  refine ⟨withTable preState vs w, ?_⟩
  have hK := preState_key vs w
  have hA : ∀ j < 19, (stackArgAddr preState j).toNat + 8 ≤ 0x300000 := fun j hj => by
    have c0 : (0x10000 : Addr).toNat = 65536 := rfl
    simp only [stackArgAddr, preState, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  unfold pspec
  rw [show Dec.decStack (RsaPkcs1Enc.AArch64.privOf c) = 3536 from rfl]
  have a0 : stackArg (withTable preState vs w) 0 = 32 := (withTable_arg _ vs w (hA 0 (by decide))).trans (by decide)
  have a1 : stackArg (withTable preState vs w) 1 = 0x4300 := (withTable_arg _ vs w (hA 1 (by decide))).trans (by decide)
  have a2 : stackArg (withTable preState vs w) 2 = 32 := (withTable_arg _ vs w (hA 2 (by decide))).trans (by decide)
  have a3 : stackArg (withTable preState vs w) 3 = 0x4400 := (withTable_arg _ vs w (hA 3 (by decide))).trans (by decide)
  have a4 : stackArg (withTable preState vs w) 4 = 32 := (withTable_arg _ vs w (hA 4 (by decide))).trans (by decide)
  have a5 : stackArg (withTable preState vs w) 5 = 0x4500 := (withTable_arg _ vs w (hA 5 (by decide))).trans (by decide)
  have a6 : stackArg (withTable preState vs w) 6 = 32 := (withTable_arg _ vs w (hA 6 (by decide))).trans (by decide)
  have a7 : stackArg (withTable preState vs w) 7 = 0x4600 := (withTable_arg _ vs w (hA 7 (by decide))).trans (by decide)
  have a8 : stackArg (withTable preState vs w) 8 = 32 := (withTable_arg _ vs w (hA 8 (by decide))).trans (by decide)
  have a9 : stackArg (withTable preState vs w) 9 = 0x4700 := (withTable_arg _ vs w (hA 9 (by decide))).trans (by decide)
  have a10 : stackArg (withTable preState vs w) 10 = 0 := (withTable_arg _ vs w (hA 10 (by decide))).trans (by decide)
  have a11 : stackArg (withTable preState vs w) 11 = 0x4100 := (withTable_arg _ vs w (hA 11 (by decide))).trans (by decide)
  have a12 : stackArg (withTable preState vs w) 12 = 64 := (withTable_arg _ vs w (hA 12 (by decide))).trans (by decide)
  have a13 : stackArg (withTable preState vs w) 13 = 0x20000 := (withTable_arg _ vs w (hA 13 (by decide))).trans (by decide)
  have a14 : stackArg (withTable preState vs w) 14 = 0x820 := (withTable_arg _ vs w (hA 14 (by decide))).trans (by decide)
  have a15 : stackArg (withTable preState vs w) 15 = 0x300000 := (withTable_arg _ vs w (hA 15 (by decide))).trans (by decide)
  have a16 : stackArg (withTable preState vs w) 16 = 0x300000 := (withTable_arg _ vs w (hA 16 (by decide))).trans (by decide)
  have a17 : stackArg (withTable preState vs w) 17 = 0x4800 := (withTable_arg _ vs w (hA 17 (by decide))).trans (by decide)
  have a18 : stackArg (withTable preState vs w) 18 = 24 := (withTable_arg _ vs w (hA 18 (by decide))).trans (by decide)
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables,
    Sig.wordIndex, AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
  simp only [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', withTable_addr]
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables,
    Sig.wordIndex, AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
  sig_and_intros
  all_goals try (exact ⟨tableOf w, List.mem_map_of_mem hw, held_twL _ _ _ rfl⟩)
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (exact symsOf_distinct2 hl)
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  rw [show BitVec.toNat (64 : BitVec 64) = 64 from rfl, show BitVec.toNat (32 : BitVec 64) = 32 from rfl,
    show BitVec.toNat (24 : BitVec 64) = 24 from rfl]
  exact hK

/-! ## The code -/

theorem oaepWordVals_eq (s : State) : wordVals 25 s = [s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.gpr .x5, s.gpr .x6, s.gpr .x7, stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16] := rfl

/-- `Spec.RsaOaep.decryptMdTablesSig.words 64`. -/
abbrev oaepSigWords : List ArgWord :=
  [.addr, .int 64, .addr, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .addr]

theorem decPrecomputed_ok (vs : List MdHash) (h : OK vs) (c : Proof.Rsa.AArch64.CrtImpl) :
    Verified AArch64.target (Impl.RsaOaep.AArch64.decrypt (fnsOf vs) (RsaPkcs1Enc.AArch64.privOf c).name
        (RsaPkcs1Enc.AArch64.privOf c).code) (pspec vs c) := by
  refine verified_withSlice_tables (sig := Spec.RsaOaep.decryptMdTablesSig) (nm := "pre") (e := .u64)
    (ln := "pre_len")
    (fun u hu => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> exact ⟨_, rfl, by decide⟩)
    (by decide) (by decide) (dec_ok vs h c) ?_ ?_ ?_ (let ⟨_, hw⟩ := h.mem; preSat hw h.2.1 c)
  · intro s h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, -, -⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  · intro s m' v hp hq
    exact hq
  · intro s₁ s₂ _ _ hpo h
    have e4 := hpo 4 (by decide)
    have e6 := hpo 6 (by decide)
    have hl : (Spec.RsaOaep.decryptMdTablesSig.words 64).length = 25 := by decide
    simp only [hl, sliceVals, oaepWordVals_eq, List.cons_append, List.nil_append] at h e4 e6 ⊢
    change Curry.apply (α := Mem → List Nat) (oaepSigWords ++ [.addr, .int 64]) _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) (oaepSigWords ++ [.addr, .int 64]) _ _ s₂.mem at h
    change Curry.apply (α := Mem → List Nat) oaepSigWords _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) oaepSigWords _ _ s₂.mem
    change (s₁.gpr .x4).setWidth 64 = (s₂.gpr .x4).setWidth 64 at e4
    change (s₁.gpr .x6).setWidth 64 = (s₂.gpr .x6).setWidth 64 at e6
    dsimp only [oaepSigWords, List.cons_append, List.nil_append, Curry.apply, ArgWord.ofRaw] at h ⊢
    refine List.append_inj_left h ?_
    simp only [List.length_map, List.length_append, Proof.Rsa.bytesAt_length', e4, e6]

end VG.Proof.RsaOaep.AArch64
