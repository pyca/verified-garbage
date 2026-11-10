module

public import VerifiedGarbage.Proof.RsaPss.RISCV64.Sat
public import VerifiedGarbage.Proof.Framework.RISCV64.AppendSlice
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_rsa_pss_sign_precomputed` on RISC-V

`vg_rsa_pss_sign`'s code, which ignores the key's precomputed values `pre`
(`Spec/Rsa/PrivatePrecompute.lean` lets an implementation ignore them),
proven against `vg_rsa_pss_sign_precomputed`'s contract from its own
(`verified_withSlice_tables`), with a state that meets it for each digest
size (`preSat`): that of `Sat.lean`, with `p`, `q`, `dP`, `dQ` and `qInv` of
32 bytes and a real key (`Proof/Rsa/PreKey.lean`).
-/

@[expose] public section
namespace VG.Proof.RsaPss.RISCV64
open VG VG.RISCV64
open VG.Proof.HashTable (symsOf symsOf_distinct)
open VG.Proof.MdHashTable.RISCV64 (MVar)
open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)

/-- The contract, with the tables `tsH` and `tsG`. -/
abbrev pSignSpec (tsH tsG : List FnTable) : Contract isa :=
  Spec.RsaPss.signPrecomputedMdTableContract
    (abi.withTables Spec.RsaPss.signPrecomputedMdTableSig [("hash", tsH), ("mgf1", tsG)]) Sg.stackBytes

/-! ## A state that meets the contract -/

/-- The stack arguments of `pSatBase dl`: `q` at `0x4300`, `dp`, `dq` and
`qinv` at `0x4400`, `0x4500` and `0x4600`, a digest of `dl` bytes at
`0x4100`, an empty salt, `scratch` at `0x20000`, the tables at `0x300000` and
`0x300100`, `pre` at `0x4800`. -/
def pArgs (dl : Nat) : Nat → BitVec 64
  | 0 => 0x4300 | 1 => 32 | 2 => 0x4400 | 3 => 32 | 4 => 0x4500 | 5 => 32 | 6 => 0x4600 | 7 => 32
  | 8 => 0x4100 | 9 => BitVec.ofNat 64 dl | 10 => 0x4700 | 11 => 0 | 12 => 0x20000 | 13 => 2080
  | 14 => 0x300000 | 15 => 0x300100 | 16 => 0x4800 | _ => 24

/-- The memory of `pSatBase dl`: the stack arguments at `0x10000`, and the
key (`keyMem`: `n` at `0x2000`, `p` at `0x4200`, `q` and `pre`). -/
def pMem (dl : Nat) (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x10000 i && Nat.blt i 0x10090 then
    BitVec.ofNat 8 ((pArgs dl ((i - 0x10000) / 8)).toNat / 256 ^ ((i - 0x10000) % 8))
  else bif keyIn i then keyMem a else 0

/-- A state meeting signing's precondition but for the tables: `out` at
`0x1000`, `n` (64 bytes) at `0x2000`, `e` at `0x3000`, `p` at `0x4200`, the
stack arguments at `sp = 0x10000`. -/
def pSatBase (dl : Nat) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x2000 | .a3 => 64 | .a4 => 0x3000 | .a5 => 1 | .a6 => 0x4200
    | .a7 => 32 | _ => 0
  sp := 0x10000
  mem := pMem dl
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩, ⟨0x4600, 32⟩,
    ⟨0x4100, dl⟩, ⟨0x4700, 0⟩, ⟨0x4800, 192⟩, ⟨0x300000, 88⟩, ⟨0x300100, 88⟩, ⟨0x10000, 144⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 2080 * 8⟩]

theorem pSat_args (dl : Nat) : ∀ j < 18, (stackArgAddr (pSatBase dl) j).toNat + 8 ≤ 0x300000 :=
  fun j hj => by
    have c0 : (65536 : Addr).toNat = 65536 := rfl
    simp only [stackArgAddr, pSatBase, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

theorem stackArgs_eighteen (s : State) :
    List.map (stackArg s) (List.range 18) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16,
      stackArg s 17] := rfl

/-- The key, below the tables. -/
theorem pSat_key {vs gs : List MVar} {v w : MVar} (dl : Nat) :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt (withTabs (pSatBase dl) vs gs v w).mem 0x2000 64)
      (Spec.Rsa.bytesAt (withTabs (pSatBase dl) vs gs v w).mem 0x4200 32)
      (Spec.Rsa.bytesAt (withTabs (pSatBase dl) vs gs v w).mem 0x4300 32) =
        some (Spec.Rsa.wordsAt (withTabs (pSatBase dl) vs gs v w).mem 0x4800 24) := by
  refine key_pre_of fun a ha => ?_
  have hlt : a.toNat < 0x10000 := by
    simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha; omega
  have hb : Nat.blt a.toNat 0x300000 = true := Nat.blt_eq.mpr (by omega)
  have hs : (Nat.ble 0x10000 a.toNat && Nat.blt a.toNat 0x10090) = false := by
    refine Bool.eq_false_iff.mpr fun h => ?_
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    omega
  show (bif Nat.blt a.toNat 0x300000 then pMem dl a else _) = _
  rw [hb, Bool.cond_true]
  show (bif _ then _ else _) = _
  rw [hs, Bool.cond_false, ha, Bool.cond_true]

/-- Signing's precondition, from the facts of a state. -/
theorem pSign_pre_of {tsH tsG : List FnTable} {dl : Nat} (hdl : dl ≤ 64) {s : State}
    (hg : s.gpr = (pSatBase dl).gpr) (hsp : s.sp = 0x10000) (ha : ∀ j < 18, stackArg s j = pArgs dl j)
    (hrd : s.rd = (pSatBase dl).rd) (hwr : s.wr = (pSatBase dl).wr)
    (hH : ∃ T ∈ tsH, Abi.tableHeld 64 s.mem 0x300000 (FnTable.words isa s T))
    (hG : ∃ T ∈ tsG, Abi.tableHeld 64 s.mem 0x300100 (FnTable.words isa s T))
    (hsy : (tabFns tsH ++ tabFns tsG).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g)
    (hd : Spec.RsaPss.digestLenOk 64 s.mem 0x300000 (BitVec.ofNat 64 dl))
    (hK : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem 0x2000 64) (Spec.Rsa.bytesAt s.mem 0x4200 32)
      (Spec.Rsa.bytesAt s.mem 0x4300 32) = some (Spec.Rsa.wordsAt s.mem 0x4800 24)) :
    (pSignSpec tsH tsG).pre s := by
  have e : Sg.stackBytes = 3471 + 1 := rfl
  unfold pSignSpec
  rw [e]
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.RsaPss.signMdTableSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs, stackArgs_eighteen, List.append_eq,
    Sig.tableRegion]
  have hdl' : (BitVec.ofNat 64 dl).toNat = dl := by rw [BitVec.toNat_ofNat]; omega
  have hA : ∀ j, stackArgAddr s j = 0x10000 + BitVec.ofNat 64 (8 * j) := fun j => by
    simp only [stackArgAddr, hsp]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide),
    ha 11 (by decide), ha 12 (by decide), ha 13 (by decide), ha 14 (by decide), ha 15 (by decide),
    ha 16 (by decide), ha 17 (by decide), hg, hsp, hrd, hwr, hA, pArgs, pSatBase]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.RsaPss.signMdTableSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs, stackArgs_eighteen, List.append_eq,
    Sig.tableRegion]
  sig_and_intros
  rotate_right 6
  · exact hK
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | with_reducible assumption
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (rw [hdl']; rfl)
    | (rw [hdl']; apply Region.disjoint_of_sep; simp [Region.sep]; omega)
    | (rw [hdl']; simp; omega)
    | skip

variable {vs : List MVar} {gs : List MVar}

theorem pSign_sat_of {v : MVar} (hv : v ∈ vs) {w : MVar} (hw : w ∈ gs) (hl : (allNames vs gs).length < 2 ^ 32)
    {dl : Nat} (hdl : dl ≤ 64) (hlen : v.w.l.G.len = dl)
    (hb : ∀ j < 18, stackArg (pSatBase dl) j = pArgs dl j) :
    (pSignSpec (MdHashTable.RISCV64.tables vs) (MdHashTable.RISCV64.tables gs)).pre
      (withTabs (pSatBase dl) vs gs v w) :=
  pSign_pre_of hdl rfl rfl (fun j hj => (withTabs_arg _ (pSat_args dl j hj)).trans (hb j hj)) rfl rfl
    ⟨_, List.mem_map_of_mem hv, withTabs_heldH _⟩ ⟨_, List.mem_map_of_mem hw, withTabs_heldG _⟩
    (symsOf_distinct hl) (fun H hH => by
      have hA := MdHashTable.RISCV64.hashAt_tableOf
        (MdHashTable.RISCV64.held_tableOf (withTabs_heldH (vs := vs) (gs := gs) (v := v) (w := w)
          (pSatBase dl))).2
      cases hH.symm.trans hA
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hlen]) (pSat_key dl)

theorem pSat_b : ∀ dl ∈ [16, 20, 28, 32, 48, 64], ∀ j < 18, stackArg (pSatBase dl) j = pArgs dl j := by
  decide

theorem pSign_sat (hok : OK vs gs) :
    ∃ s, (pSignSpec (MdHashTable.RISCV64.tables vs) (MdHashTable.RISCV64.tables gs)).pre s := by
  obtain ⟨-, -, -, hl, hv, hw⟩ := hok
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil vs hv
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil gs hw
  have hL := lens_of v
  exact ⟨_, pSign_sat_of hv hw hl (by revert hL; generalize v.w.l.G.len = d; decide +revert) rfl
    (pSat_b _ hL)⟩

/-! ## The code -/

theorem stackVals_sign (s : State) : stackVals 24 s = [s.gpr .a0, s.gpr .a1, s.gpr .a2, s.gpr .a3, s.gpr .a4,
    s.gpr .a5, s.gpr .a6, s.gpr .a7, stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4,
    stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11,
    stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15] := rfl

theorem stackVals_signP (s : State) : stackVals (24 + 2) s = stackVals 24 s ++ [stackArg s 16, stackArg s 17] :=
  rfl

/-- `Spec.RsaPss.signMdTableSig.words 64`. -/
abbrev sigWords : List ArgWord :=
  [.addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr,
    .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .addr]

theorem signPrecomputed_ok (hok : OK vs gs) :
    Verified target (Impl.RsaPss.RISCV64.Sign.sign (MdHashTable.RISCV64.fnsOf vs) (MdHashTable.RISCV64.fns3 gs))
      (pSignSpec (MdHashTable.RISCV64.tables vs) (MdHashTable.RISCV64.tables gs)) := by
  refine verified_withSlice_tables (sig := Spec.RsaPss.signMdTableSig) (nm := "pre") (e := .u64)
    (ln := "pre_len")
    (fun u hu => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> exact ⟨_, rfl, by decide⟩)
    (by decide) (by decide) (sign_ok hok) ?_ ?_ ?_ (pSign_sat hok)
  · intro s h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -, -, h15⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h15⟩
  · intro s m' v hp hq
    exact hq
  · intro s₁ s₂ _ _ hpo h
    have e3 := hpo 3 (by decide)
    have e5 := hpo 5 (by decide)
    have hl : (Spec.RsaPss.signMdTableSig.words 64).length = 24 := by decide
    simp only [hl, stackVals_signP, stackVals_sign, List.cons_append, List.nil_append] at h e3 e5 ⊢
    change Curry.apply (α := Mem → List Nat) (sigWords ++ [.addr, .int 64]) _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) (sigWords ++ [.addr, .int 64]) _ _ s₂.mem at h
    change Curry.apply (α := Mem → List Nat) sigWords _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) sigWords _ _ s₂.mem
    change (s₁.gpr .a3).setWidth 64 = (s₂.gpr .a3).setWidth 64 at e3
    change (s₁.gpr .a5).setWidth 64 = (s₂.gpr .a5).setWidth 64 at e5
    dsimp only [sigWords, List.cons_append, List.nil_append, Curry.apply, ArgWord.ofRaw] at h ⊢
    refine List.append_inj_left h ?_
    simp only [List.length_map, List.length_append, Proof.Rsa.bytesAt_length', e3, e5]

end VG.Proof.RsaPss.RISCV64
