module

public import VerifiedGarbage.Proof.RsaPss.X86_64.Sat
public import VerifiedGarbage.Proof.Framework.X86_64.AppendSlice
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_rsa_pss_sign_precomputed` on x86-64

`vg_rsa_pss_sign`'s code, which ignores the key's precomputed values `pre`
(`Spec/Rsa/PrivatePrecompute.lean` lets an implementation ignore them),
proven against `vg_rsa_pss_sign_precomputed`'s contract from its own
(`verified_withSlice_tables`), with a state that meets it (`preSat`): that of
`Sat.lean`, with `p`, `q`, `dP`, `dQ` and `qInv` of 32 bytes and a real key
(`Proof/Rsa/PreKey.lean`); and what its registration's scrub needs of the
contract (`signPrecomputed_postOut`).
-/

@[expose] public section
namespace VG.Proof.RsaPss.X86_64
open VG VG.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)
open VG.Proof.HashTable (symsOf symsOf_distinct)
open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)

/-- The contract, with the tables `tsH` and `tsG`. -/
abbrev pspec (tsH tsG : List FnTable) : Contract isa :=
  Spec.RsaPss.signPrecomputedMdTableContract
    (abi.withTables Spec.RsaPss.signPrecomputedMdTableSig [("hash", tsH), ("mgf1", tsG)]) signStack

/-! ## A state that meets the contract -/

/-- The stack arguments of `preState D`; the key (`keyMem`) has `n` at
`0x2000`, `p` at `0x4200`, `q` at `0x4300` and `pre` at `0x4800`. -/
def preArgs (D : Nat) : List Nat :=
  [0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0x5000, D, 0x5100, 0, 0x20000, 2080, 0x300000,
    0x300100, 0x4800, 24]

/-- The memory of `preState D`: the stack arguments from `0x10008`, and the
key. -/
def preMem (D : Nat) (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x10008 i && Nat.blt i 0x100A8 then
    BitVec.ofNat 8 ((preArgs D).getD ((i - 0x10008) / 8) 0 / 256 ^ ((i - 0x10008) % 8))
  else bif keyIn i then keyMem a else 0

/-- `signSatBase D` with the key (`keyMem`) and its precomputed values. -/
def preState (D : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x3000 | .r9 => 1
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := preMem D
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩, ⟨0x4600, 32⟩,
    ⟨0x5000, D⟩, ⟨0x5100, 0⟩, ⟨0x4800, 192⟩, ⟨0x300000, 88⟩, ⟨0x300100, 88⟩, ⟨0x10008, 160⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 2080 * 8⟩]

/-- Its stack arguments. -/
def preArgW (D : Nat) (j : Nat) : BitVec 64 := BitVec.ofNat 64 ((preArgs D).getD j 0)

theorem preState_key (D : Nat) (a : Addr) (ha : keyIn a.toNat = true) : (preState D).mem a = keyMem a := by
  have hs : (Nat.ble 0x10008 a.toNat && Nat.blt a.toNat 0x100A8) = false := by
    simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha
    refine Bool.eq_false_iff.mpr fun h => ?_
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    omega
  show (bif _ then _ else _) = _
  rw [hs, Bool.cond_false, ha, Bool.cond_true]

theorem withTabs_key {vs : List MdHash} {w : MdHash} (s : State)
    (h : ∀ a : Addr, keyIn a.toNat = true → s.mem a = keyMem a) :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt (withTabs s vs w).mem 0x2000 64)
      (Spec.Rsa.bytesAt (withTabs s vs w).mem 0x4200 32)
      (Spec.Rsa.bytesAt (withTabs s vs w).mem 0x4300 32) =
        some (Spec.Rsa.wordsAt (withTabs s vs w).mem 0x4800 24) := by
  refine key_pre_of fun a ha => ?_
  have hlt : a.toNat < 0x300000 := by
    simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha; omega
  simp only [withTabs, tabMem, Nat.blt_eq.mpr hlt, Bool.cond_true]
  exact h a ha

theorem pre_args (D : Nat) : ∀ j < 20, (stackArgAddr (preState D) j).toNat + 8 ≤ 0x300000 := fun j hj => by
  have c0 : (0x10000 : Addr).toNat = 65536 := rfl
  simp only [stackArgAddr, preState, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem pre_b16 : ∀ j < 20, stackArg (preState 16) j = preArgW 16 j := by decide
theorem pre_b20 : ∀ j < 20, stackArg (preState 20) j = preArgW 20 j := by decide
theorem pre_b28 : ∀ j < 20, stackArg (preState 28) j = preArgW 28 j := by decide
theorem pre_b32 : ∀ j < 20, stackArg (preState 32) j = preArgW 32 j := by decide
theorem pre_b48 : ∀ j < 20, stackArg (preState 48) j = preArgW 48 j := by decide
theorem pre_b64 : ∀ j < 20, stackArg (preState 64) j = preArgW 64 j := by decide

theorem stackArgs_twenty (s : State) :
    List.map (stackArg s) (List.range 20) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16,
      stackArg s 17, stackArg s 18, stackArg s 19] := rfl

/-- The precondition, from the facts of a state. -/
theorem psign_pre_of {tsH tsG : List FnTable} {D : Nat} (hD : D ≤ 64) {s : State}
    (hg : s.gpr = (preState D).gpr) (ha : ∀ j < 20, stackArg s j = preArgW D j)
    (hrd : s.rd = (preState D).rd) (hwr : s.wr = (preState D).wr)
    (hH : ∃ T ∈ tsH, Abi.tableHeld 64 s.mem 0x300000 (FnTable.words isa s T))
    (hG : ∃ T ∈ tsG, Abi.tableHeld 64 s.mem 0x300100 (FnTable.words isa s T))
    (hsy : (tabFns tsH ++ tabFns tsG).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g)
    (hd : Spec.RsaPss.digestLenOk 64 s.mem 0x300000 (BitVec.ofNat 64 D))
    (hK : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem 0x2000 64) (Spec.Rsa.bytesAt s.mem 0x4200 32)
      (Spec.Rsa.bytesAt s.mem 0x4300 32) = some (Spec.Rsa.wordsAt s.mem 0x4800 24)) :
    (pspec tsH tsG).pre s := by
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, signStack, stackArgs_twenty, List.append_eq, Sig.tableRegion]
  have hsp : s.gpr .rsp = 0x10000 := by rw [hg]; rfl
  have hD' : (BitVec.ofNat 64 D).toNat = D := by rw [BitVec.toNat_ofNat]; omega
  have hA : ∀ j, stackArgAddr s j = 0x10000 + BitVec.ofNat 64 (8 * (j + 1)) := fun j => by
    simp only [stackArgAddr, hsp]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide),
    ha 11 (by decide), ha 12 (by decide), ha 13 (by decide), ha 14 (by decide), ha 15 (by decide),
    ha 16 (by decide), ha 17 (by decide), ha 18 (by decide), ha 19 (by decide), hg, hrd, hwr, hA, preArgW,
    preArgs, List.getD_cons_succ, List.getD_cons_zero]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, signStack, stackArgs_twenty, List.append_eq, Sig.tableRegion]
  sig_and_intros
  all_goals first
    | with_reducible exact hK
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact hH
    | exact hG
    | exact hsy
    | exact hd
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (rw [hD']; rfl)
    | (rw [hD']; apply Region.disjoint_of_sep; simp [Region.sep]; omega)
    | (rw [hD']; simp; omega)
    | (simp; omega)
    | skip

variable {vs : List MdHash}

theorem psign_sat_of {w : MdHash} (hw : w ∈ vs) (hl : (allNames vs).length < 2 ^ 32)
    {D : Nat} (hD : D ≤ 64) (hlen : w.mgf.G.len = D) (hb : ∀ j < 20, stackArg (preState D) j = preArgW D j) :
    (pspec (MdHashTable.X86_64.tables vs) (MdHashTable.X86_64.tables vs)).pre (withTabs (preState D) vs w) :=
  psign_pre_of hD rfl (fun j hj => (withTabs_arg _ vs w (pre_args D j hj)).trans (hb j hj)) rfl rfl
    ⟨_, List.mem_map_of_mem hw, withTabs_heldH _ vs w⟩ ⟨_, List.mem_map_of_mem hw, withTabs_heldG _ vs w⟩
    (symsOf_distinct hl) (fun H hH => by
      have hA := MdHashTable.X86_64.hashAt_tableOf
        (MdHashTable.X86_64.held_tableOf (withTabs_heldH (preState D) vs w)).2.2.2.1
      cases hH.symm.trans hA
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hlen])
    (withTabs_key _ (preState_key D))

theorem preSat (hok : OK vs) : ∃ s, (pspec (MdHashTable.X86_64.tables vs) (MdHashTable.X86_64.tables vs)).pre s := by
  obtain ⟨w, hw, -⟩ := hok.2.2.2.1 0 (by decide)
  have hl := hok.2.2.2.2
  have hm := w.mgf.mem
  simp only [Pbkdf2.Md.X86_64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e | e | e
  · exact ⟨_, psign_sat_of hw hl (by decide) (by rw [e]; rfl) pre_b16⟩
  · exact ⟨_, psign_sat_of hw hl (by decide) (by rw [e]; rfl) pre_b20⟩
  · exact ⟨_, psign_sat_of hw hl (by decide) (by rw [e]; rfl) pre_b28⟩
  · exact ⟨_, psign_sat_of hw hl (by decide) (by rw [e]; rfl) pre_b32⟩
  · exact ⟨_, psign_sat_of hw hl (by decide) (by rw [e]; rfl) pre_b48⟩
  · exact ⟨_, psign_sat_of hw hl (by decide) (by rw [e]; rfl) pre_b64⟩
  · exact ⟨_, psign_sat_of hw hl (by decide) (by rw [e]; rfl) pre_b28⟩
  · exact ⟨_, psign_sat_of hw hl (by decide) (by rw [e]; rfl) pre_b32⟩

/-! ## The code -/

theorem pssWordVals_eq (s : State) : wordVals 24 s = [s.gpr .rdi, s.gpr .rsi, s.gpr .rdx, s.gpr .rcx, s.gpr .r8, s.gpr .r9, stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16, stackArg s 17] := rfl

/-- `Spec.RsaPss.signMdTableSig.words 64`. -/
abbrev pssSigWords : List ArgWord :=
  [.addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .addr]

open VG.Proof.Rsa.X86_64 (chkContract)

/-- `vg_rsa_pss_sign_precomputed`, with the tables of `vs`, calling the
private-key operation `privC`: `vg_rsa_pss_sign`'s code. -/
theorem signPrecomputed_ok (hok : OK vs) {privN : String} {privC : Prog isa}
    (hv : ∀ s, chkContract.pre s → ∃ t s', Exec isa privC s t s' ∧ abiPreserved s s' ∧ chkContract.post s s')
    (hct : ConstantTime isa chkContract.pre chkContract.pub privC) (hspC : SpSafe privC)
    (hdC : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes) :
    Verified X86_64.target
      (Impl.RsaPss.X86_64.signC (MdHashTable.X86_64.fnsOf vs) (HashTable.X86_64.fnsOf vs) privN privC)
      (pspec (MdHashTable.X86_64.tables vs) (MdHashTable.X86_64.tables vs)) := by
  refine verified_withSlice_tables (sig := Spec.RsaPss.signMdTableSig) (nm := "pre") (e := .u64) (ln := "pre_len")
    (fun u hu => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> exact ⟨_, rfl, by decide⟩)
    (by decide) (sign_ok hok hv hct hspC hdC) ?_ ?_ ?_ (preSat hok)
  · intro s h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -, -, h13⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  · intro s m' v hp hq
    exact hq
  · intro s₁ s₂ _ _ hpo h
    have e3 := hpo 3 (by decide)
    have e5 := hpo 5 (by decide)
    have hl : (Spec.RsaPss.signMdTableSig.words 64).length = 24 := by decide
    simp only [hl, sliceVals, pssWordVals_eq, List.cons_append, List.nil_append] at h e3 e5 ⊢
    change Curry.apply (α := Mem → List Nat) (pssSigWords ++ [.addr, .int 64]) _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) (pssSigWords ++ [.addr, .int 64]) _ _ s₂.mem at h
    change Curry.apply (α := Mem → List Nat) pssSigWords _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) pssSigWords _ _ s₂.mem
    change (s₁.gpr .rcx).setWidth 64 = (s₂.gpr .rcx).setWidth 64 at e3
    change (s₁.gpr .r9).setWidth 64 = (s₂.gpr .r9).setWidth 64 at e5
    dsimp only [pssSigWords, List.cons_append, List.nil_append, Curry.apply, ArgWord.ofRaw] at h ⊢
    refine List.append_inj_left h ?_
    simp only [List.length_map, List.length_append, Proof.Rsa.bytesAt_length', e3, e5]

/-! ## Without secret residue -/

/-- `vg_rsa_pss_sign_precomputed`'s postcondition reads the memory on return
only in `out`. -/
theorem signPrecomputed_postOut (tsH tsG : List FnTable) :
    VG.X86_64.Scrub.PostOut (pspec tsH tsG) (Spec.RsaPss.signPrecomputedMdTableSig.retBits 64) :=
  VG.X86_64.Scrub.postOut_of_local_pre (leak := some _) (VG.X86_64.Scrub.ScrubAbi.plain.tables _ _)
    fun vs m m₁ m₂ r hlen hpre hb h => by
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 25) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨outLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
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
    obtain ⟨digest, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨digestLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨salt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨saltLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
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
    simp only [Spec.RsaPss.signPrecomputedMdTableSig, Sig.bufs, List.mem_cons, forall_eq_or_imp] at hb
    have hol : outLen.toNat = nLen.toNat := hpre.2.1
    have hby : Spec.Rsa.bytesAt m₂ out nLen.toNat = Spec.Rsa.bytesAt m₁ out nLen.toNat :=
      VG.Proof.Rsa.X86_64.bytesAt_agree (by simp only [Elem.size]; omega)
        (by have := outLen.isLt; simp only [Elem.size]; omega) hb.1
    intro H G hH hG
    have h' : Spec.Rsa.writtenOutcome m₁ out nLen.toNat r _ := h H G hH hG
    show Spec.Rsa.writtenOutcome m₂ out nLen.toNat r _
    revert h'
    generalize Spec.RsaPss.sign _ _ _ _ _ _ _ _ _ _ _ = o
    cases o <;> simp only [Spec.Rsa.writtenOutcome, hby] <;> exact id

end VG.Proof.RsaPss.X86_64
