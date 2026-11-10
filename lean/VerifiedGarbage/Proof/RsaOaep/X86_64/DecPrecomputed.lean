module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.Verified
public import VerifiedGarbage.Proof.Framework.X86_64.AppendSlice
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_rsa_oaep_decrypt_precomputed` on x86-64

`vg_rsa_oaep_decrypt`'s code, which ignores the key's precomputed values
`pre` (`Spec/Rsa/PrivatePrecompute.lean` lets an implementation ignore them),
proven against `vg_rsa_oaep_decrypt_precomputed`'s contract from its own
(`verified_withSlice_tables`), with a state that meets it (`preSat`): that of
`Verified.lean`'s `dec_sat`, with `p`, `q`, `dP`, `dQ` and `qInv` of 32 bytes
and a real key (`Proof/Rsa/PreKey.lean`); and what its registration's scrub
needs of the contract (`decPrecomputed_postOut`).
-/

@[expose] public section
namespace VG.Proof.RsaOaep.X86_64
open VG VG.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)
open VG.Proof.RsaPkcs1Enc.X86_64 (PrivImpl)
open VG.Proof.HashTable.X86_64 (tables fnsOf names tableOf)
open VG.Proof.HashTable (symsOf_distinct2 putWs add8_toNat)
open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)

/-- The contract, with the tables `ts`. -/
abbrev pspec (ts : List FnTable) : Contract isa :=
  Spec.RsaOaep.decryptPrecomputedMdTablesContract
    (abi.withTables Spec.RsaOaep.decryptPrecomputedMdTablesSig [("hash", ts), ("mgf1", ts)]) decStack

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
def preArgs : List Nat :=
  [1, 0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0x4700, 0, 0x4100, 64, 0x20000, 0x820, 0x300000,
    0x300000, 0x4800, 24]

/-- The memory of `preState`: the stack arguments from `0x10008`, and the
key. -/
def preMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x10008 i && Nat.blt i 0x100B0 then
    BitVec.ofNat 8 (preArgs.getD ((i - 0x10008) / 8) 0 / 256 ^ ((i - 0x10008) % 8))
  else bif keyIn i then keyMem a else 0

/-- `decSatBase` with the key and its precomputed values. -/
def preState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x1800 | .rcx => 0x2000 | .r8 => 64 | .r9 => 0x3000
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := preMem
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩, ⟨0x4600, 32⟩,
    ⟨0x4700, 0⟩, ⟨0x4100, 64⟩, ⟨0x4800, 192⟩, ⟨0x300000, 88⟩, ⟨0x300000, 88⟩, ⟨0x10008, 168⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 2080 * 8⟩]

theorem preState_key (vs : List MdHash) (w : MdHash) :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt (withTable preState vs w).mem 0x2000 64)
      (Spec.Rsa.bytesAt (withTable preState vs w).mem 0x4200 32)
      (Spec.Rsa.bytesAt (withTable preState vs w).mem 0x4300 32) =
        some (Spec.Rsa.wordsAt (withTable preState vs w).mem 0x4800 24) := by
  refine key_pre_of fun a ha => ?_
  have hlt : a.toNat < 0x10000 := by
    simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha; omega
  have hs : (Nat.ble 0x10008 a.toNat && Nat.blt a.toNat 0x100B0) = false := by
    refine Bool.eq_false_iff.mpr fun h => ?_
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    omega
  show putWs preMem 0x300000 (twL vs w) a = _
  rw [putWs_byte (by simp; omega) (twL_room vs w)]
  show (bif _ then _ else _) = _
  rw [hs, Bool.cond_false, ha, Bool.cond_true]

theorem stackArgs_twentyone (s : State) :
    List.map (stackArg s) (List.range 21) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16,
      stackArg s 17, stackArg s 18, stackArg s 19, stackArg s 20] := rfl

theorem pre_args : ∀ j < 21, stackArg preState j = BitVec.ofNat 64 (preArgs.getD j 0) := by decide

/-- The precondition, from the facts of a state. -/
theorem dec_pre_of {ts : List FnTable} {s : State} (hg : s.gpr = preState.gpr)
    (ha : ∀ j < 21, stackArg s j = BitVec.ofNat 64 (preArgs.getD j 0))
    (hrd : s.rd = preState.rd) (hwr : s.wr = preState.wr)
    (hH : ∃ T ∈ ts, Abi.tableHeld 64 s.mem 0x300000 (FnTable.words isa s T))
    (hsy : ((ts.map (·.fns)).flatten ++ (ts.map (·.fns)).flatten).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g)
    (hK : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem 0x2000 64) (Spec.Rsa.bytesAt s.mem 0x4200 32)
      (Spec.Rsa.bytesAt s.mem 0x4300 32) = some (Spec.Rsa.wordsAt s.mem 0x4800 24)) :
    (pspec ts).pre s := by
  have hsp : s.gpr .rsp = 0x10000 := by rw [hg]; rfl
  have hA : ∀ j, stackArgAddr s j = 0x10000 + BitVec.ofNat 64 (8 * (j + 1)) := fun j => by
    simp only [stackArgAddr, hsp]
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs, decStack, RsaPkcs1Enc.X86_64.privStack,
    Impl.RsaOaep.X86_64.frameBytes, stackArgs_twentyone, List.append_eq]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide),
    ha 11 (by decide), ha 12 (by decide), ha 13 (by decide), ha 14 (by decide), ha 15 (by decide),
    ha 16 (by decide), ha 17 (by decide), ha 18 (by decide), ha 19 (by decide), ha 20 (by decide), preArgs,
    List.getD_cons_succ, List.getD_cons_zero, hg, hrd, hwr, hA]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs, decStack, RsaPkcs1Enc.X86_64.privStack,
    Impl.RsaOaep.X86_64.frameBytes, stackArgs_twentyone, List.append_eq]
  sig_and_intros
  all_goals first
    | exact hK
    | exact hH
    | exact hsy
    | exact Region.disjoint_of_sep (by decide)
    | (simp only [Spec.Rsa.lenValid]; decide)
    | rfl
    | decide

theorem preSat {vs : List MdHash} {w : MdHash} (hw : w ∈ vs) (hl : (names vs).length < 2 ^ 32) :
    ∃ s, (pspec (tables vs)).pre s := by
  have hA : ∀ j < 21, (stackArgAddr preState j).toNat + 8 ≤ 0x300000 := fun j hj => by
    have c0 : (0x10000 : Addr).toNat = 65536 := rfl
    simp only [stackArgAddr, preState, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  exact ⟨withTable preState vs w, dec_pre_of rfl
    (fun j hj => (withTable_arg _ vs w (hA j hj)).trans (pre_args j hj)) rfl rfl
    ⟨tableOf w, List.mem_map_of_mem hw, withTable_held _ vs w⟩ (symsOf_distinct2 hl) (preState_key vs w)⟩

/-! ## The code -/

theorem oaepWordVals_eq (s : State) : wordVals 25 s = [s.gpr .rdi, s.gpr .rsi, s.gpr .rdx, s.gpr .rcx, s.gpr .r8, s.gpr .r9, stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16, stackArg s 17, stackArg s 18] := rfl

/-- `Spec.RsaOaep.decryptMdTablesSig.words 64`. -/
abbrev oaepSigWords : List ArgWord :=
  [.addr, .int 64, .addr, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .addr]

/-- `vg_rsa_oaep_decrypt_precomputed`, with the tables of `vs`:
`vg_rsa_oaep_decrypt`'s code. -/
theorem decPrecomputed_ok (vs : List MdHash) (h : OK vs) (v : PrivImpl) :
    Verified target (Impl.RsaOaep.X86_64.decrypt (fnsOf vs) v.name v.code) (pspec (tables vs)) := by
  refine verified_withSlice_tables (sig := Spec.RsaOaep.decryptMdTablesSig) (nm := "pre") (e := .u64)
    (ln := "pre_len")
    (fun u hu => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> exact ⟨_, rfl, by decide⟩)
    (by decide) (dec_ok vs h v) ?_ ?_ ?_ (let ⟨_, hw⟩ := h.mem; preSat hw h.2.1)
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
    change (s₁.gpr .r8).setWidth 64 = (s₂.gpr .r8).setWidth 64 at e4
    change (stackArg s₁ 0).setWidth 64 = (stackArg s₂ 0).setWidth 64 at e6
    dsimp only [oaepSigWords, List.cons_append, List.nil_append, Curry.apply, ArgWord.ofRaw] at h ⊢
    refine List.append_inj_left h ?_
    simp only [List.length_map, List.length_append, Proof.Rsa.bytesAt_length', e4, e6]

/-! ## Without secret residue -/

/-- `vg_rsa_oaep_decrypt_precomputed`'s postcondition reads the memory on
return only in `out` and `msg_len`. -/
theorem decPrecomputed_postOut (ts : List FnTable) :
    VG.X86_64.Scrub.PostOut (pspec ts) (Spec.RsaOaep.decryptPrecomputedMdTablesSig.retBits 64) :=
  VG.X86_64.Scrub.postOut_of_local_pre (leak := some _) (VG.X86_64.Scrub.ScrubAbi.plain.tables _ _)
    fun vs m m₁ m₂ r hlen hpre hb h => by
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 26) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨outLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨msgLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨nLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨e, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨eLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨p, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨pLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨q, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨qLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dp, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dpLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dq, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dqLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨qinv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨qinvLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨label, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨labelLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ct, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ctLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨scratch, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨scratchLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨hash, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨mgf1, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨pre, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨preLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    simp only [Spec.RsaOaep.decryptPrecomputedMdTablesSig, Spec.RsaOaep.decryptSig, List.cons_append,
      List.nil_append, Sig.bufs, List.mem_cons, forall_eq_or_imp] at hb
    have hol : outLen.toNat = nLen.toNat := hpre.2.1
    have hby : Spec.Rsa.bytesAt m₂ out nLen.toNat = Spec.Rsa.bytesAt m₁ out nLen.toNat :=
      VG.Proof.Rsa.X86_64.bytesAt_agree (by simp only [Elem.size]; omega)
        (by have := outLen.isLt; simp only [Elem.size]; omega) hb.1
    have hw : m₂.readW msgLen 64 = m₁.readW msgLen 64 := VG.Proof.Rsa.X86_64.readW_agree (by decide) (by decide) hb.2.1
    intro H G hH hG
    have h' : Spec.RsaOaep.writtenDecrypt m₁ out msgLen nLen.toNat r _ := h H G hH hG
    show Spec.RsaOaep.writtenDecrypt m₂ out msgLen nLen.toNat r _
    revert h'
    generalize Spec.RsaOaep.decrypt _ _ _ _ _ _ _ _ _ _ _ = o
    cases o <;> simp only [Spec.RsaOaep.writtenDecrypt, hby, hw] <;> exact id

end VG.Proof.RsaOaep.X86_64
