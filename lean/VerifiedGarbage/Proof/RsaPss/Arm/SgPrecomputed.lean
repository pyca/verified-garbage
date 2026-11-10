module

public import VerifiedGarbage.Proof.RsaPss.Arm.Inst
public import VerifiedGarbage.Proof.Framework.Arm.AppendSlice
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_rsa_pss_sign_precomputed` on ARMv7

`vg_rsa_pss_sign`'s code, which ignores the key's precomputed values `pre`
(`Spec/Rsa/PrivatePrecompute.lean` lets an implementation ignore them),
proven against `vg_rsa_pss_sign_precomputed`'s contract from its own
(`verified_withSlice_tables`), with a state that meets it (`preSat`): that of
`SgSat.lean`, with `p`, `q`, `dP`, `dQ` and `qInv` of 32 bytes and a real key
(`Proof/Rsa/PreKey.lean`).
-/

@[expose] public section
namespace VG.Proof.RsaPss.Arm.Sg
open VG VG.Arm
open VG.Proof.HashTable (symsOf32 symsOf32_distinct)
open VG.Proof.HashTable.Arm (TVar)
open VG.Proof.MdHashTable.Arm (MVar)
open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)

/-- The contract, with the tables of `mvs` and `vs`. -/
abbrev pspec (mvs : List MVar) (vs : List TVar) : Contract isa :=
  Spec.RsaPss.signPrecomputedMdTableContract
    (abi.withTables Spec.RsaPss.signPrecomputedMdTableSig
      [("hash", MdHashTable.Arm.tables mvs), ("mgf1", HashTable.Arm.tables vs)]) stackBytes

/-! ## A state that meets the contract -/

/-- The stack arguments of `preState D`; the key (`keyMem`) has `n` at
`0x2000`, `p` at `0x4200`, `q` at `0x4300` and `pre` at `0x4800`. -/
def preArgs (D : Nat) : List Nat := [0x2100, 1, 0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0x3000, D, 0x3600, 0, 0x10000, 0x820, 0x300000, 0x300100, 0x4800, 24]

/-- The memory of `preState D`: the stack arguments from `0x8000`, and the
key. -/
def preMem (D : Nat) (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x8000 i && Nat.blt i 0x8058 then
    BitVec.ofNat 8 ((preArgs D).getD ((i - 0x8000) / 4) 0 / 256 ^ ((i - 0x8000) % 4))
  else bif keyIn i then keyMem a else 0

/-- `satState D` with the key (`keyMem`) and its precomputed values. -/
def preState (D : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x2000 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem := preMem D
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩, ⟨0x4600, 32⟩,
    ⟨0x3000, D⟩, ⟨0x3600, 0⟩, ⟨0x4800, 192⟩, ⟨0x300000, 44⟩, ⟨0x300100, 44⟩, ⟨0x8000, 88⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x10000, 2080 * 8⟩]

/-- Its stack arguments. -/
def preArgW (D : Nat) (j : Nat) : BitVec 32 := BitVec.ofNat 32 ((preArgs D).getD j 0)

theorem preState_key (D : Nat) (a : Addr) (ha : keyIn a.toNat = true) : (preState D).mem a = keyMem a := by
  have hs : (Nat.ble 0x8000 a.toNat && Nat.blt a.toNat 0x8058) = false := by
    simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha
    refine Bool.eq_false_iff.mpr fun h => ?_
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    omega
  show (bif _ then _ else _) = _
  rw [hs, Bool.cond_false, ha, Bool.cond_true]

theorem withTabs_key {mvs : List MVar} {vs : List TVar} {w : MVar} {wg : TVar} (s : State)
    (h : ∀ a : Addr, keyIn a.toNat = true → s.mem a = keyMem a) :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt (withTabs s mvs vs w wg).mem 0x2000 64)
      (Spec.Rsa.bytesAt (withTabs s mvs vs w wg).mem 0x4200 32)
      (Spec.Rsa.bytesAt (withTabs s mvs vs w wg).mem 0x4300 32) =
        some (Spec.Rsa.wordsAt (withTabs s mvs vs w wg).mem 0x4800 24) := by
  refine key_pre_of fun a ha => ?_
  have hlt : a.toNat < 0x300000 := by
    simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha; omega
  simp only [withTabs, tabMem, Nat.blt_eq.mpr hlt, Bool.cond_true]
  exact h a ha

theorem pre_args (D : Nat) : ∀ j < 22, (stackArgAddr (preState D) j).toNat + 4 ≤ 0x300000 := by
  intro j hj
  simp only [stackArgAddr, State.addr, show (preState D).sp = 0x8000 from rfl, BitVec.toNat_setWidth,
    BitVec.toNat_add, BitVec.toNat_ofNat, show BitVec.toNat (32768 : BitVec 32) = 32768 from rfl]
  omega

theorem pre_b16 : ∀ j < 22, stackArg (preState 16) j = preArgW 16 j := by decide
theorem pre_b20 : ∀ j < 22, stackArg (preState 20) j = preArgW 20 j := by decide
theorem pre_b28 : ∀ j < 22, stackArg (preState 28) j = preArgW 28 j := by decide
theorem pre_b32 : ∀ j < 22, stackArg (preState 32) j = preArgW 32 j := by decide
theorem pre_b48 : ∀ j < 22, stackArg (preState 48) j = preArgW 48 j := by decide
theorem pre_b64 : ∀ j < 22, stackArg (preState 64) j = preArgW 64 j := by decide

/-- The precondition, from the facts of a state. -/
theorem psign_pre_of {hs ts : List FnTable} {D : Nat} (hD : D ≤ 64) {s : State}
    (hg : s.gpr = (preState D).gpr) (hsp : s.sp = (preState D).sp) (ha : ∀ j < 22, stackArg s j = preArgW D j)
    (hrd : s.rd = (preState D).rd) (hwr : s.wr = (preState D).wr)
    (hH : ∃ T ∈ hs, Abi.tableHeld 32 s.mem 0x300000 (FnTable.words isa s T))
    (hG : ∃ T ∈ ts, Abi.tableHeld 32 s.mem 0x300100 (FnTable.words isa s T))
    (hsy : ((hs.map (fun T : FnTable => T.fns)).flatten ++ ((ts.map (fun T : FnTable => T.fns)).flatten ++ [])).Pairwise
      fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64)
    (hd : Spec.RsaPss.digestLenOk 32 s.mem 0x300000 (BitVec.ofNat 32 D))
    (hK : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem 0x2000 64) (Spec.Rsa.bytesAt s.mem 0x4200 32)
      (Spec.Rsa.bytesAt s.mem 0x4300 32) = some (Spec.Rsa.wordsAt s.mem 0x4800 24)) :
    (Spec.RsaPss.signPrecomputedMdTableContract
      (abi.withTables Spec.RsaPss.signPrecomputedMdTableSig [("hash", hs), ("mgf1", ts)]) stackBytes).pre s := by
  have g0 : s.gpr .r0 = 0x1000 := by rw [hg]; rfl
  have g1 : s.gpr .r1 = 64 := by rw [hg]; rfl
  have g2 : s.gpr .r2 = 0x2000 := by rw [hg]; rfl
  have g3 : s.gpr .r3 = 64 := by rw [hg]; rfl
  have sp0 : s.sp = 0x8000 := hsp
  have e0 : stackArgAddr s 0 = 0x8000 := by simp only [stackArgAddr, sp0]; decide
  have hD' : (BitVec.ofNat 32 D).toNat = D := by rw [BitVec.toNat_ofNat]; omega
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, reduceClassify, Loc.val]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide), ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide), ha 11 (by decide), ha 12 (by decide), ha 13 (by decide), ha 14 (by decide), ha 15 (by decide), ha 16 (by decide), ha 17 (by decide), ha 18 (by decide), ha 19 (by decide), ha 20 (by decide), ha 21 (by decide), g0, g1, g2, g3, e0, sp0, hrd, hwr, preArgW, preArgs, List.getD_cons_succ, List.getD_cons_zero]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, reduceClassify, Loc.val]
  sig_and_intros
  all_goals first
    | with_reducible exact hK
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | with_reducible assumption
    | exact hH
    | exact hG
    | exact hsy
    | exact hd
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (rw [hD']; rfl)
    | (rw [hD']; exact dig_disj hD (Region.disjoint_of_sep (by decide)))
    | (rw [hD']; exact (dig_disj hD (Region.disjoint_of_sep (by decide))).symm)
    | (rw [hD']; apply Region.disjoint_of_sep; simp [Region.sep]; omega)
    | (rw [hD']; simp; omega)
    | (rw [show BitVec.setWidth 64 (8192 : BitVec 32) = (0x2000 : Addr) by decide,
        show BitVec.setWidth 64 16896#32 = (0x4200 : Addr) by decide,
        show BitVec.setWidth 64 17152#32 = (0x4300 : Addr) by decide,
        show BitVec.setWidth 64 18432#32 = (0x4800 : Addr) by decide,
        show BitVec.toNat (64 : BitVec 32) = 64 by decide, show (32#32).toNat = 32 by decide,
        show (24#32).toNat = 24 by decide]
       exact hK)

theorem psign_sat_of {mvs : List MVar} {vs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ mvs) (hwg : wg ∈ vs)
    (hl : (allNames mvs vs).length < 2 ^ 24) {D : Nat} (hD : D ≤ 64) (hlen : w.h.G.len = D)
    (hb : ∀ j < 22, stackArg (preState D) j = preArgW D j) :
    (pspec mvs vs).pre (withTabs (preState D) mvs vs w wg) :=
  psign_pre_of hD rfl rfl (fun j hj => (withTabs_arg _ (pre_args D j hj)).trans (hb j hj)) rfl rfl
    ⟨_, List.mem_map_of_mem hw, withTabs_heldH _⟩ ⟨_, List.mem_map_of_mem hwg, withTabs_heldG _⟩
    (by rw [List.append_nil]; exact symsOf32_distinct hl) (fun H hH => by
      have e3 : State.addr (0x300000 : BitVec 32) = (0x300000 : Addr) := by decide
      have hheld := withTabs_heldH (preState D) (mvs := mvs) (vs := vs) (w := w) (wg := wg)
      rw [← e3] at hheld
      have hA := MdHashTable.Arm.hashAt_tableOf (p := 0x300000) (by decide)
        (MdHashTable.Arm.held_tableOf (by decide) hheld).2.2.2
      rw [e3] at hA
      rw [hA, Option.some.injEq] at hH
      subst hH
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hlen])
    (withTabs_key _ (preState_key D))

theorem preSat {mvs : List MVar} {vs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ mvs) (hwg : wg ∈ vs)
    (hl : (allNames mvs vs).length < 2 ^ 24) : ∃ s, (pspec mvs vs).pre s := by
  have hG : w.h.G ∈ Spec.Mgf1.hashes := List.mem_of_getElem? w.idx
  have hlen : w.h.G.len = 16 ∨ w.h.G.len = 20 ∨ w.h.G.len = 28 ∨ w.h.G.len = 32 ∨ w.h.G.len = 48 ∨
      w.h.G.len = 64 := by
    simp only [Spec.Mgf1.hashes, List.mem_cons, List.not_mem_nil, or_false] at hG
    rcases hG with e | e | e | e | e | e | e | e | e | e | e | e | e | e <;> rw [e] <;> decide
  rcases hlen with e | e | e | e | e | e
  · exact ⟨_, psign_sat_of hw hwg hl (by decide) e pre_b16⟩
  · exact ⟨_, psign_sat_of hw hwg hl (by decide) e pre_b20⟩
  · exact ⟨_, psign_sat_of hw hwg hl (by decide) e pre_b28⟩
  · exact ⟨_, psign_sat_of hw hwg hl (by decide) e pre_b32⟩
  · exact ⟨_, psign_sat_of hw hwg hl (by decide) e pre_b48⟩
  · exact ⟨_, psign_sat_of hw hwg hl (by decide) e pre_b64⟩

/-! ## The code -/

theorem wordVals_eq (s : State) : wordVals 24 s = [Loc.val s (locAt 0), Loc.val s (locAt 1), Loc.val s (locAt 2), Loc.val s (locAt 3), Loc.val s (locAt 4), Loc.val s (locAt 5), Loc.val s (locAt 6), Loc.val s (locAt 7), Loc.val s (locAt 8), Loc.val s (locAt 9), Loc.val s (locAt 10), Loc.val s (locAt 11), Loc.val s (locAt 12), Loc.val s (locAt 13), Loc.val s (locAt 14), Loc.val s (locAt 15), Loc.val s (locAt 16), Loc.val s (locAt 17), Loc.val s (locAt 18), Loc.val s (locAt 19), Loc.val s (locAt 20), Loc.val s (locAt 21), Loc.val s (locAt 22), Loc.val s (locAt 23)] := rfl

/-- `Spec.RsaPss.signMdTableSig.words 32`. -/
abbrev sigWords : List ArgWord :=
  [.addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .int 32, .addr, .addr]

theorem signPrecomputed_verified {mvs : List MVar} {vs : List TVar} (hok : OK mvs vs)
    (v : Proof.Rsa.Arm.CrtImpl) : Verified target (signCode mvs vs v) (pspec mvs vs) := by
  refine verified_withSlice_tables (sig := Spec.RsaPss.signMdTableSig) (nm := "pre") (e := .u64) (ln := "pre_len")
    (fun u hu => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> exact ⟨_, rfl, by decide⟩)
    (by decide) (by decide) (Proof.RsaPss.Arm.sign_ok hok v) ?_ ?_ ?_
    (let ⟨_, hw⟩ := List.exists_mem_of_ne_nil _ hok.2.2.2.1
     let ⟨_, hwg⟩ := List.exists_mem_of_ne_nil _ hok.2.2.2.2; preSat hw hwg hok.2.2.1)
  · intro s h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -, -, h13⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  · intro s m' v hp hq
    exact hq
  · intro s₁ s₂ _ _ hpo h
    have e3 := hpo 3 (by decide)
    have e5 := hpo 5 (by decide)
    have hl : (Spec.RsaPss.signMdTableSig.words 32).length = 24 := by decide
    simp only [hl, sliceVals, wordVals_eq, List.cons_append, List.nil_append] at h e3 e5 ⊢
    change Curry.apply (α := Mem → List Nat) (sigWords ++ [.addr, .int 32]) _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) (sigWords ++ [.addr, .int 32]) _ _ s₂.mem at h
    change Curry.apply (α := Mem → List Nat) sigWords _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) sigWords _ _ s₂.mem
    change (Loc.val s₁ (locAt 3)).setWidth 32 = (Loc.val s₂ (locAt 3)).setWidth 32 at e3
    change (Loc.val s₁ (locAt 5)).setWidth 32 = (Loc.val s₂ (locAt 5)).setWidth 32 at e5
    dsimp only [sigWords, List.cons_append, List.nil_append, Curry.apply, ArgWord.ofRaw] at h ⊢
    refine List.append_inj_left h ?_
    simp only [List.length_map, List.length_append, Proof.Rsa.bytesAt_length', e3, e5]

end VG.Proof.RsaPss.Arm.Sg
