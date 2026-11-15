module

public import VerifiedGarbage.Proof.RsaPss.RISCV64.Inst
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Sg.Inst
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem

/-! ### `RsaPss.RISCV64.Sat`, which only this module used -/

section

/-!
# RSASSA-PSS on RISC-V with the tables of `vs` and `gs`: `Verified`

As on x86-64 (`Proof/RsaPss/X86_64/Sat.lean`): the contracts are satisfiable,
by the states of the contracts with the hash functions fixed, with the table
of `MdHash` of a hash function `v` of `vs` at `0x300000`, the table of
`Hash` of a hash function `w` of `gs` at `0x300100` (the stack arguments'
values), and the tables' functions at distinct addresses (`symsOf`):
`verify_sat`, `sign_sat`; with correctness and constant time, verification
(`verify_ok`) and signing (`sign_ok`), which the registration file binds.
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64
open VG.Proof.HashTable (symsOf symsOf_distinct readW_sep64 putWs putWs_out putWs_held)
open VG.Proof.MdHashTable.RISCV64 (MVar)

/-- The words of a table, its functions at the addresses `symsOf ns`. -/
def tw (ns : List String) (T : FnTable) : List (BitVec 64) := T.fns.map (symsOf ns) ++ T.data

/-- The names of the tables' functions. -/
def allNames (vs : List MVar) (gs : List MVar) : List String :=
  MdHashTable.RISCV64.names vs ++ MdHashTable.RISCV64.names gs

/-- The memory `m` with the tables of `v` at `0x300000` and of `w` at
`0x300100`, and `m` itself below `0x300000`. -/
def tabMem (m : Mem) (vs : List MVar) (gs : List MVar) (v : MVar) (w : MVar) : Mem := fun a =>
  bif Nat.blt a.toNat 0x300000 then m a
  else putWs (putWs m 0x300000 (tw (allNames vs gs) (MdHashTable.RISCV64.tableOf v))) 0x300100
    (tw (allNames vs gs) (MdHashTable.RISCV64.tableOf w)) a

/-- A state with `s`'s registers and regions, the tables of `v` at `0x300000`
and of `w` at `0x300100`, and the tables' functions at distinct addresses. -/
def withTabs (s : State) (vs : List MVar) (gs : List MVar) (v : MVar) (w : MVar) : State :=
  { s with mem := tabMem s.mem vs gs v w, syms := symsOf (allNames vs gs) }

section
variable {vs : List MVar} {gs : List MVar} {v : MVar} {w : MVar}

theorem withTabs_arg (s : State) {j : Nat} (hj : (stackArgAddr s j).toNat + 8 ≤ 0x300000) :
    stackArg (withTabs s vs gs v w) j = stackArg s j := by
  show (tabMem s.mem vs gs v w).readW (stackArgAddr s j) 64 = s.mem.readW (stackArgAddr s j) 64
  refine Mem.readW_congr fun i hi => ?_
  have : (stackArgAddr s j + BitVec.ofNat 64 i).toNat < 0x300000 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hj, hi]
  simp only [tabMem, Nat.blt_eq.mpr this, Bool.cond_true]

/-- Above `0x300000`, the tables' memory. -/
theorem tabMem_above {m : Mem} {p : Addr} {ws : List (BitVec 64)}
    (hp : 0x300000 ≤ p.toNat) (hl : p.toNat + 8 * ws.length < 2 ^ 64)
    (h : Abi.tableHeld 64 (putWs (putWs m 0x300000 (tw (allNames vs gs) (MdHashTable.RISCV64.tableOf v))) 0x300100
      (tw (allNames vs gs) (MdHashTable.RISCV64.tableOf w))) p ws) :
    Abi.tableHeld 64 (tabMem m vs gs v w) p ws := by
  intro i hi
  rw [← h i hi]
  refine Mem.readW_congr fun k hk => ?_
  have : ¬ (p + BitVec.ofNat 64 (64 / 8 * i) + BitVec.ofNat 64 k).toNat < 0x300000 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hp, hl, hi, hk]
  have hb : Nat.blt (p + BitVec.ofNat 64 (64 / 8 * i) + BitVec.ofNat 64 k).toNat 0x300000 = false := by
    rw [Bool.eq_false_iff]; intro hc; exact this (Nat.blt_eq.mp hc)
  simp only [tabMem, hb, Bool.cond_false]

theorem withTabs_heldH (s : State) :
    Abi.tableHeld 64 (withTabs s vs gs v w).mem 0x300000
      (FnTable.words isa (withTabs s vs gs v w) (MdHashTable.RISCV64.tableOf v)) := by
  have hl : (tw (allNames vs gs) (MdHashTable.RISCV64.tableOf v)).length = 11 := by
    simp [tw, MdHashTable.RISCV64.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf]
  have c1 : (0x300000 : Addr).toNat = 0x300000 := rfl
  have c2 : (0x300100 : Addr).toNat = 0x300100 := rfl
  refine tabMem_above (by rw [c1]) (by simp [FnTable.words, MdHashTable.RISCV64.tableOf, Spec.MdHashTable.dataOf,
    Spec.MdHashTable.dataOf, Spec.HashTable.dataOf]) fun i hi => ?_
  have hi' : i < 11 := by
    simp [FnTable.words, MdHashTable.RISCV64.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf] at hi; omega_using [hi]
  rw [putWs_out (.inl (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))
    (by simp [tw, MdHashTable.RISCV64.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf])
    (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]
  exact putWs_held (by rw [hl]; decide) i (by rw [hl]; exact hi')

theorem withTabs_heldG (s : State) :
    Abi.tableHeld 64 (withTabs s vs gs v w).mem 0x300100
      (FnTable.words isa (withTabs s vs gs v w) (MdHashTable.RISCV64.tableOf w)) :=
  tabMem_above (by decide) (by simp [FnTable.words, MdHashTable.RISCV64.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf])
    (putWs_held (by simp [tw, MdHashTable.RISCV64.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf]))

end

/-- The functions of the tables. -/
abbrev tabFns (ts : List FnTable) : List String := (ts.map (·.fns)).flatten

/-! ## Verification with a precomputed key -/

/-- A state meeting verification's precondition but for the tables: a 512-bit
modulus, one-byte `e`, a digest of `dl` bytes, 16 words of `pre` at
`0x5000`, the stack arguments at `sp`, and the tables' addresses `0x300000`
and `0x300100`. -/
def verifySatBase (dl : Nat) : State where
  gpr r := match r with
    | .a0 => 0x2000 | .a1 => 64 | .a2 => 0x3000 | .a3 => 1 | .a4 => 0x4600 | .a5 => BitVec.ofNat 64 dl
    | .a6 => 0x4000 | .a7 => 64 | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10012 then 0x02 else bif Nat.beq a.toNat 0x10018 then 0x20
    else bif Nat.beq a.toNat 0x10019 then 0x08 else bif Nat.beq a.toNat 0x10021 then 0x50
    else bif Nat.beq a.toNat 0x10028 then 16 else bif Nat.beq a.toNat 0x10032 then 0x30
    else bif Nat.beq a.toNat 0x10039 then 0x01 else bif Nat.beq a.toNat 0x1003A then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4600, dl⟩, ⟨0x4000, 64⟩, ⟨0x5000, 128⟩, ⟨0x300000, 88⟩, ⟨0x300100, 88⟩,
    ⟨0x10000, 64⟩]
  wr := [⟨0x20000, 2080 * 8⟩]

/-- The stack arguments of `verifySatBase dl`. -/
def verifyArgs : Nat → BitVec 64
  | 0 => 0 | 1 => 0 | 2 => 0x20000 | 3 => 2080 | 4 => 0x5000 | 5 => 16 | 6 => 0x300000 | _ => 0x300100

theorem verifySat_args (dl : Nat) : ∀ j < 8, (stackArgAddr (verifySatBase dl) j).toNat + 8 ≤ 0x300000 :=
  fun j hj => by
    have c0 : (65536 : Addr).toNat = 65536 := rfl
    simp only [stackArgAddr, verifySatBase, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

/-- Verification's precondition, from the facts of a state. -/
theorem verify_pre_of {tsH tsG : List FnTable} {dl : Nat} (hdl : dl ≤ 64) {s : State}
    (hg : s.gpr = (verifySatBase dl).gpr) (hsp : s.sp = 0x10000) (ha : ∀ j < 8, stackArg s j = verifyArgs j)
    (hrd : s.rd = (verifySatBase dl).rd) (hwr : s.wr = (verifySatBase dl).wr)
    (hH : ∃ T ∈ tsH, Abi.tableHeld 64 s.mem 0x300000 (FnTable.words isa s T))
    (hG : ∃ T ∈ tsG, Abi.tableHeld 64 s.mem 0x300100 (FnTable.words isa s T))
    (hsy : (tabFns tsH ++ tabFns tsG).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g)
    (hd : Spec.RsaPss.digestLenOk 64 s.mem 0x300000 (BitVec.ofNat 64 dl)) :
    (verSpec tsH tsG).pre s := by
  have e : Proof.RsaOaep.RISCV64.stackBytes = 335 + 1 := rfl
  unfold verSpec
  rw [e]
  sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, List.append_eq, Sig.tableRegion, List.range, List.range.loop]
  have hdl' : (BitVec.ofNat 64 dl).toNat = dl := by rw [BitVec.toNat_ofNat]; omega_using [hdl]
  have hA : ∀ j, stackArgAddr s j = 0x10000 + BitVec.ofNat 64 (8 * j) := fun j => by
    simp only [stackArgAddr, hsp]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), hg, hsp, hrd, hwr, hA, verifyArgs, verifySatBase]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, List.append_eq, Sig.tableRegion, List.range, List.range.loop]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | with_reducible assumption
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (rw [hdl']; rfl)
    | (rw [hdl']; apply Region.disjoint_of_sep; simp [Region.sep]; omega_using [hdl])
    | (rw [hdl']; simp; omega_using [hdl])
    | skip

variable {vs : List MVar} {gs : List MVar}

theorem verify_sat_of {v : MVar} (hv : v ∈ vs) {w : MVar} (hw : w ∈ gs) (hl : (allNames vs gs).length < 2 ^ 32)
    {dl : Nat} (hdl : dl ≤ 64) (hlen : v.w.l.G.len = dl)
    (hb : ∀ j < 8, stackArg (verifySatBase dl) j = verifyArgs j) :
    (verSpec (MdHashTable.RISCV64.tables vs) (MdHashTable.RISCV64.tables gs)).pre (withTabs (verifySatBase dl) vs gs v w) :=
  verify_pre_of hdl rfl rfl (fun j hj => (withTabs_arg _ (verifySat_args dl j hj)).trans (hb j hj)) rfl rfl
    ⟨_, List.mem_map_of_mem hv, withTabs_heldH _⟩ ⟨_, List.mem_map_of_mem hw, withTabs_heldG _⟩
    (symsOf_distinct hl) fun H hH => by
      have hA := MdHashTable.RISCV64.hashAt_tableOf
        (MdHashTable.RISCV64.held_tableOf (withTabs_heldH (vs := vs) (gs := gs) (v := v) (w := w)
          (verifySatBase dl))).2
      cases hH.symm.trans hA
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hdl]), hlen]

theorem verifySat_b : ∀ dl ∈ [16, 20, 28, 32, 48, 64], ∀ j < 8, stackArg (verifySatBase dl) j = verifyArgs j := by
  decide

theorem lens_of (v : MVar) : v.w.l.G.len ∈ [16, 20, 28, 32, 48, 64] := by
  have hm := v.w.l.mem
  simp only [Proof.RsaOaep.RISCV64.labelHashes, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e | e | e <;> rw [e] <;> decide

theorem verify_sat (hok : OK vs gs) :
    ∃ s, (verSpec (MdHashTable.RISCV64.tables vs) (MdHashTable.RISCV64.tables gs)).pre s := by
  obtain ⟨-, -, -, hl, hv, hw⟩ := hok
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil vs hv
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil gs hw
  have hL := lens_of v
  exact ⟨_, verify_sat_of hv hw hl (by revert hL; generalize v.w.l.G.len = d; decide +revert) rfl
    (verifySat_b _ hL)⟩

/-- `vg_rsa_pss_verify_precomputed`, with the tables of `vs` and `gs`. -/
theorem verify_ok (hok : OK vs gs) :
    Verified RISCV64.target (Impl.RsaPss.RISCV64.verifyPrecomputed (MdHashTable.RISCV64.fnsOf vs)
      (MdHashTable.RISCV64.fns3 gs)) (verSpec (MdHashTable.RISCV64.tables vs) (MdHashTable.RISCV64.tables gs)) :=
  ⟨code_correct hok, code_constantTime hok, verify_sat hok⟩

/-! ## Signing -/

/-- A state meeting signing's precondition but for the tables: a 512-bit
modulus, one-byte `e`, primes, exponents and `qInv`, a digest of `dl` bytes,
an empty salt, a working space of 2080 words, the stack arguments at `sp`,
and the tables' addresses `0x300000` and `0x300100`. -/
def signSatBase (dl : Nat) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x2000 | .a3 => 64 | .a4 => 0x3000 | .a5 => 1 | .a6 => 0x4200
    | .a7 => 1 | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10001 then 0x43
    else bif Nat.beq a.toNat 0x10008 then 1 else bif Nat.beq a.toNat 0x10011 then 0x44
    else bif Nat.beq a.toNat 0x10018 then 1 else bif Nat.beq a.toNat 0x10021 then 0x45
    else bif Nat.beq a.toNat 0x10028 then 1 else bif Nat.beq a.toNat 0x10031 then 0x46
    else bif Nat.beq a.toNat 0x10038 then 1 else bif Nat.beq a.toNat 0x10041 then 0x41
    else bif Nat.beq a.toNat 0x10048 then BitVec.ofNat 8 dl else bif Nat.beq a.toNat 0x10051 then 0x47
    else bif Nat.beq a.toNat 0x10062 then 0x02 else bif Nat.beq a.toNat 0x10068 then 0x20
    else bif Nat.beq a.toNat 0x10069 then 0x08 else bif Nat.beq a.toNat 0x10072 then 0x30
    else bif Nat.beq a.toNat 0x10079 then 0x01 else bif Nat.beq a.toNat 0x1007A then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩, ⟨0x4500, 1⟩, ⟨0x4600, 1⟩,
    ⟨0x4100, dl⟩, ⟨0x4700, 0⟩, ⟨0x300000, 88⟩, ⟨0x300100, 88⟩, ⟨0x10000, 128⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 2080 * 8⟩]

/-- The stack arguments of `signSatBase dl`. -/
def signArgs (dl : Nat) : Nat → BitVec 64
  | 0 => 0x4300 | 1 => 1 | 2 => 0x4400 | 3 => 1 | 4 => 0x4500 | 5 => 1 | 6 => 0x4600 | 7 => 1
  | 8 => 0x4100 | 9 => BitVec.ofNat 64 dl | 10 => 0x4700 | 11 => 0 | 12 => 0x20000 | 13 => 2080
  | 14 => 0x300000 | _ => 0x300100

theorem signSat_args (dl : Nat) : ∀ j < 16, (stackArgAddr (signSatBase dl) j).toNat + 8 ≤ 0x300000 :=
  fun j hj => by
    have c0 : (65536 : Addr).toNat = 65536 := rfl
    simp only [stackArgAddr, signSatBase, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

/-- Signing's precondition, from the facts of a state. -/
theorem sign_pre_of {tsH tsG : List FnTable} {dl : Nat} (hdl : dl ≤ 64) {s : State}
    (hg : s.gpr = (signSatBase dl).gpr) (hsp : s.sp = 0x10000) (ha : ∀ j < 16, stackArg s j = signArgs dl j)
    (hrd : s.rd = (signSatBase dl).rd) (hwr : s.wr = (signSatBase dl).wr)
    (hH : ∃ T ∈ tsH, Abi.tableHeld 64 s.mem 0x300000 (FnTable.words isa s T))
    (hG : ∃ T ∈ tsG, Abi.tableHeld 64 s.mem 0x300100 (FnTable.words isa s T))
    (hsy : (tabFns tsH ++ tabFns tsG).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g)
    (hd : Spec.RsaPss.digestLenOk 64 s.mem 0x300000 (BitVec.ofNat 64 dl)) :
    (Sg.signSpec tsH tsG).pre s := by
  have e : Sg.stackBytes false = 3471 + 1 := rfl
  unfold Sg.signSpec
  rw [e]
  sig_pre [Spec.RsaPss.signMdTableContract, Spec.RsaPss.signMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, List.append_eq, Sig.tableRegion, List.range, List.range.loop]
  have hdl' : (BitVec.ofNat 64 dl).toNat = dl := by rw [BitVec.toNat_ofNat]; omega_using [hdl]
  have hA : ∀ j, stackArgAddr s j = 0x10000 + BitVec.ofNat 64 (8 * j) := fun j => by
    simp only [stackArgAddr, hsp]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide),
    ha 11 (by decide), ha 12 (by decide), ha 13 (by decide), ha 14 (by decide), ha 15 (by decide), hg, hsp, hrd,
    hwr, hA, signArgs, signSatBase]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaPss.signMdTableContract, Spec.RsaPss.signMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, List.append_eq, Sig.tableRegion, List.range, List.range.loop]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | with_reducible assumption
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (rw [hdl']; rfl)
    | (rw [hdl']; apply Region.disjoint_of_sep; simp [Region.sep]; omega_using [hdl])
    | (rw [hdl']; simp; omega_using [hdl])
    | skip

theorem sign_sat_of {v : MVar} (hv : v ∈ vs) {w : MVar} (hw : w ∈ gs) (hl : (allNames vs gs).length < 2 ^ 32)
    {dl : Nat} (hdl : dl ≤ 64) (hlen : v.w.l.G.len = dl)
    (hb : ∀ j < 16, stackArg (signSatBase dl) j = signArgs dl j) :
    (Sg.signSpec (MdHashTable.RISCV64.tables vs) (MdHashTable.RISCV64.tables gs)).pre
      (withTabs (signSatBase dl) vs gs v w) :=
  sign_pre_of hdl rfl rfl (fun j hj => (withTabs_arg _ (signSat_args dl j hj)).trans (hb j hj)) rfl rfl
    ⟨_, List.mem_map_of_mem hv, withTabs_heldH _⟩ ⟨_, List.mem_map_of_mem hw, withTabs_heldG _⟩
    (symsOf_distinct hl) fun H hH => by
      have hA := MdHashTable.RISCV64.hashAt_tableOf
        (MdHashTable.RISCV64.held_tableOf (withTabs_heldH (vs := vs) (gs := gs) (v := v) (w := w)
          (signSatBase dl))).2
      cases hH.symm.trans hA
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hdl]), hlen]

theorem signSat_b : ∀ dl ∈ [16, 20, 28, 32, 48, 64], ∀ j < 16, stackArg (signSatBase dl) j = signArgs dl j := by
  decide

theorem sign_sat (hok : OK vs gs) :
    ∃ s, (Sg.signSpec (MdHashTable.RISCV64.tables vs) (MdHashTable.RISCV64.tables gs)).pre s := by
  obtain ⟨-, -, -, hl, hv, hw⟩ := hok
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil vs hv
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil gs hw
  have hL := lens_of v
  exact ⟨_, sign_sat_of hv hw hl (by revert hL; generalize v.w.l.G.len = d; decide +revert) rfl
    (signSat_b _ hL)⟩

/-- `vg_rsa_pss_sign`, with the tables of `vs` and `gs`. -/
theorem sign_ok (hok : OK vs gs) :
    Verified RISCV64.target (Impl.RsaPss.RISCV64.Sign.sign (MdHashTable.RISCV64.fnsOf vs)
      (MdHashTable.RISCV64.fns3 gs)) (Sg.signSpec (MdHashTable.RISCV64.tables vs) (MdHashTable.RISCV64.tables gs)) :=
  ⟨Sg.code_correct hok, Sg.code_constantTime hok, sign_sat hok⟩

end VG.Proof.RsaPss.RISCV64

end

end


/-!
# `vg_rsa_pss_sign_precomputed` on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/SignP.lean`): `signP`, the code of `vg_rsa_pss_sign`
calling `vg_rsa_private_checked_precomputed` (`signG … true`), against
`Spec.RsaPss.signPrecomputedMdTableContract`: its precondition gives
`PreS true`, with `pre`'s facts (`preS_ofP`), and the tables (`spec_tabSP`),
its public data `PubS true` (`pubS_ofP`), and the proofs shared with
`vg_rsa_pss_sign` (`signG_wp`, `code_constantTimeG`) the rest. A state
meeting the precondition holds a real key (`signP_sat`, `Rsa.PreKey`), and
`signP_ok`, which the registration binds.
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64.Sg

open VG VG.RISCV64

theorem stackArgs_eighteen (s : State) :
    List.map (stackArg s) (List.range 18) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16, stackArg s 17] := rfl

/-- The variant's contract, with the hash function one of the tables `tsH`
and MGF1's one of `tsG`, and the stack of the frames and of
`vg_rsa_private_checked_precomputed`. -/
abbrev signPSpec (tsH tsG : List FnTable) : Contract isa :=
  Spec.RsaPss.signPrecomputedMdTableContract
    (abi.withTables Spec.RsaPss.signPrecomputedMdTableSig [("hash", tsH), ("mgf1", tsG)]) (stackBytes true)

/-- Unfolds the variant's precondition at `h`. -/
macro "signP_pre" " at " h:ident : tactic => `(tactic| (
  have e : stackBytes true = 3487 + 1 := rfl
  unfold signPSpec at $h:ident
  rw [e] at $h:ident
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.RsaPss.digestLenOk, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs, List.append_eq,
    List.range, List.range.loop, Spec.Rsa.lenValid] at $h:ident
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.RsaPss.digestLenOk, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs, List.append_eq,
    List.range, List.range.loop, Spec.Rsa.lenValid] at $h:ident
  simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq,
    exists_eq_left'] at $h:ident))

/-- The variant's precondition gives `PreS true` (`pre`'s facts in `px`). -/
theorem preS_ofP {tsH tsG : List FnTable} {s : State} (h : (signPSpec tsH tsG).pre s) {H : Spec.Mgf1.Hash}
    (hH : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 14) = some H) : PreS true H.len s := by
  signP_pre at h
  sig_split h
  rename_i spal sp1 sp2 _ _ _ hrd hwr on oe op oq odp odq oqi odg osl os oP oth otg oa ns es ps qs dps dqs qis
    dgs sls sP sth stg sa ko kn ke kp kq kdp kdq kqi kdg ksl ks kP kth ktg ka wo wn we wp wq wdp wdq wqi wdg wsl
    wsc wP wth wtg k1 k2 ok e1 e2 p1 p2 q1 q2 h3 h7 h5 hs hpl hk hl als al14 al15
  have hl := hl H hH
  rw [hl] at hrd odg dgs kdg wdg
  exact ⟨spal, sp1, sp2, hrd, hwr, on, oe, op, oq, odp, odq, oqi, odg, osl, os, oth, otg, oa, ns, es, ps, qs, dps,
    dqs, qis, dgs, sls, sth, stg, sa, ko, kn, ke, kp, kq, kdp, kdq, kqi, kdg, ksl, ks, kth, ktg, ka, wo, wn, we, wp,
    wq, wdp, wdq, wqi, wdg, wsl, wsc, wth, wtg, k1, k2, ok, e1, e2, p1, p2, q1, q2, h3, h7, h5, hs, als, al14, al15,
    fun _ => ⟨oP, sP, kP, wP, hpl, sp2, h, fun _ => hk⟩⟩

/-- The tables, as the variant's contract gives them. -/
theorem spec_tabSP {tsH tsG : List FnTable} {s : State} (h : (signPSpec tsH tsG).pre s) :
    (∃ T ∈ tsH, Abi.tableHeld 64 s.mem (stackArg s 14) (FnTable.words isa s T)) ∧
      (∃ T ∈ tsG, Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s T)) ∧
      ((tsH.map (fun T : FnTable => T.fns)).flatten ++ (tsG.map (fun T : FnTable => T.fns)).flatten).Pairwise
        (fun f g => f ≠ g → s.syms f ≠ s.syms g) := by
  signP_pre at h
  exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-- The variant's public data: `PubS true`, the tables' functions at the same
addresses, and the same tables held. -/
theorem pubS_ofP {tsH tsG : List FnTable} {s₁ s₂ : State} (h : (signPSpec tsH tsG).pub s₁ s₂) :
    PubS true s₁ s₂ ∧
      (∀ f ∈ (tsH.map (fun T : FnTable => T.fns)).flatten ++ (tsG.map (fun T : FnTable => T.fns)).flatten,
        s₁.syms f = s₂.syms f) ∧
      (∀ T ∈ tsH, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 14) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 14) (FnTable.words isa s₂ T))) ∧
      ∀ T ∈ tsG, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 15) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 15) (FnTable.words isa s₂ T)) := by
  have e : stackBytes true = 3487 + 1 := rfl
  unfold signPSpec at h
  rw [e] at h
  sig_pub [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argRegs, List.append_eq, List.range, List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at h
  obtain ⟨hsp, hsy, htabH, htabG, hl, g0, g1, g2, g3, g4, g5, g6, g7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15, a16, a17⟩ := h
  obtain ⟨hne, hw⟩ := List.append_inj hl (by simp [VG.Proof.RsaPkcs1Sig.bytesAt_length, g3, g5])
  simp only [List.map_append] at hne
  obtain ⟨hn, he⟩ := List.append_inj hne (by simp [VG.Proof.RsaPkcs1Sig.bytesAt_length, g3])
  have inj := fun {w : Nat} {x y : List (BitVec w)} (h : x.map (·.toNat) = y.map (·.toNat)) =>
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
  refine ⟨⟨hsp.symm, fun r hr => ?_, fun i hi => ?_, (inj hn).symm, (inj he).symm,
    fun _ => ⟨a16.symm, a17.symm⟩, fun _ => ?_⟩, hsy, fun T hT => htabH _ _ rfl rfl T hT,
    fun T hT => htabG _ _ rfl rfl T hT⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [g0.symm, g1.symm, g2.symm, g3.symm, g4.symm, g5.symm, g6.symm, g7.symm]
  · rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm, a8.symm, a9.symm, a10.symm,
      a11.symm, a12.symm, a13.symm, a14.symm, a15.symm]
  · exact hw.symm

section
variable {vs : List MdHashTable.RISCV64.MVar} {gs : List MdHashTable.RISCV64.MVar}

/-- The correctness of `vg_rsa_pss_sign_precomputed`, against its contract,
for the tables of `vs` and `gs`. -/
theorem codeP_correct (hok : OK vs gs) (s : State)
    (h : (signPSpec (MdHashTable.RISCV64.tables vs) (MdHashTable.RISCV64.tables gs)).pre s) :
    ∃ t s', Exec isa (Impl.RsaPss.RISCV64.Sign.signP (MdHashTable.RISCV64.fnsOf vs) (MdHashTable.RISCV64.fns3 gs))
        s t s' ∧
      abiPreserved s s' ∧ (signPSpec (MdHashTable.RISCV64.tables vs) (MdHashTable.RISCV64.tables gs)).post s s' := by
  obtain ⟨Hs, Gs, hH, hG, key⟩ := signG_wp (pc := true) hok spec_tabSP (fun h hH => preS_ofP h hH) s h
  obtain ⟨t, s', he, habi, hr⟩ := key
  refine ⟨t, s', he, habi, ?_⟩
  have e : stackBytes true = 3487 + 1 := rfl
  unfold signPSpec
  rw [e]
  sig_post [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.param, Abi.withTables, abi, argRegs, stackArgs_eighteen,
    List.append_eq]
  intro H' G' hH' hG'
  rw [hH] at hH'
  rw [hG] at hG'
  cases hH'
  cases hG'
  exact hr

/-- Constant time: `code_constantTimeG` with the variant's contract's facts. -/
theorem codeP_constantTime (hok : OK vs gs) :
    ConstantTime isa (signPSpec (MdHashTable.RISCV64.tables vs) (MdHashTable.RISCV64.tables gs)).pre
      (signPSpec (MdHashTable.RISCV64.tables vs) (MdHashTable.RISCV64.tables gs)).pub
      (Impl.RsaPss.RISCV64.Sign.signP (MdHashTable.RISCV64.fnsOf vs) (MdHashTable.RISCV64.fns3 gs)) :=
  code_constantTimeG (pc := true) hok spec_tabSP (fun h hH => preS_ofP h hH) pubS_ofP

end

end VG.Proof.RsaPss.RISCV64.Sg

namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64
open VG.Proof.HashTable (symsOf_distinct)
open VG.Proof.MdHashTable.RISCV64 (MVar)
open VG.Proof.Rsa.PreKey

section
variable {vs : List MVar} {gs : List MVar}

/-- The memory of `signPSatBase dl`: the key, the stack arguments that
differ, and `signSatBase dl`'s. -/
def pMem (dl : Nat) (a : Addr) : Byte :=
  bif keyIn a.toNat then keyMem a
  else bif Nat.beq a.toNat 0x10008 then 32 else bif Nat.beq a.toNat 0x10018 then 32
  else bif Nat.beq a.toNat 0x10028 then 32 else bif Nat.beq a.toNat 0x10038 then 32
  else bif Nat.beq a.toNat 0x10081 then 0x48 else bif Nat.beq a.toNat 0x10088 then 24
  else (signSatBase dl).mem a

/-- `signSatBase dl` with the key (`keyMem`) and its precomputed values:
`p`, `q`, `dp`, `dq` and `qinv` of 32 octets, `pre_len` 24 words at
`0x4800`. -/
def signPSatBase (dl : Nat) : State :=
  { signSatBase dl with
    gpr := fun r => bif r == .a7 then 32 else (signSatBase dl).gpr r
    mem := pMem dl
    rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩, ⟨0x4600, 32⟩,
      ⟨0x4100, dl⟩, ⟨0x4700, 0⟩, ⟨0x4800, 192⟩, ⟨0x300000, 88⟩, ⟨0x300100, 88⟩, ⟨0x10000, 144⟩] }

/-- The stack arguments of `signPSatBase dl`. -/
def signPArgs (dl : Nat) (j : Nat) : BitVec 64 :=
  if j = 16 then 0x4800 else if j = 17 then 24 else if j = 1 ∨ j = 3 ∨ j = 5 ∨ j = 7 then 32 else signArgs dl j

theorem signPSat_args (dl : Nat) : ∀ j < 18, (stackArgAddr (signPSatBase dl) j).toNat + 8 ≤ 0x300000 :=
  fun j hj => by
    have c0 : (65536 : Addr).toNat = 65536 := rfl
    simp only [stackArgAddr, signPSatBase, signSatBase, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

/-- The variant's precondition, from the facts of a state. -/
theorem signP_pre_of {tsH tsG : List FnTable} {dl : Nat} (hdl : dl ≤ 64) {s : State}
    (hg : s.gpr = (signPSatBase dl).gpr) (hsp : s.sp = 0x10000) (ha : ∀ j < 18, stackArg s j = signPArgs dl j)
    (hrd : s.rd = (signPSatBase dl).rd) (hwr : s.wr = (signPSatBase dl).wr)
    (hH : ∃ T ∈ tsH, Abi.tableHeld 64 s.mem 0x300000 (FnTable.words isa s T))
    (hG : ∃ T ∈ tsG, Abi.tableHeld 64 s.mem 0x300100 (FnTable.words isa s T))
    (hsy : (tabFns tsH ++ tabFns tsG).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g)
    (hd : Spec.RsaPss.digestLenOk 64 s.mem 0x300000 (BitVec.ofNat 64 dl))
    (hk : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem 0x2000 64) (Spec.Rsa.bytesAt s.mem 0x4200 32)
      (Spec.Rsa.bytesAt s.mem 0x4300 32) = some (Spec.Rsa.wordsAt s.mem 0x4800 24)) :
    (Sg.signPSpec tsH tsG).pre s := by
  have e : Sg.stackBytes true = 3487 + 1 := rfl
  unfold Sg.signPSpec
  rw [e]
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argRegs, List.append_eq, Sig.tableRegion, List.range,
    List.range.loop]
  have hdl' : (BitVec.ofNat 64 dl).toNat = dl := by rw [BitVec.toNat_ofNat]; omega_using [hdl]
  have hA : ∀ j, stackArgAddr s j = 0x10000 + BitVec.ofNat 64 (8 * j) := fun j => by
    simp only [stackArgAddr, hsp]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide),
    ha 11 (by decide), ha 12 (by decide), ha 13 (by decide), ha 14 (by decide), ha 15 (by decide),
    ha 16 (by decide), ha 17 (by decide), hg, hsp, hrd, hwr, hA, signPArgs, signArgs, signPSatBase, signSatBase]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', Nat.reduceEqDiff]
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argRegs, List.append_eq, Sig.tableRegion, List.range,
    List.range.loop]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | with_reducible assumption
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (rw [hdl']; rfl)
    | (rw [hdl']; apply Region.disjoint_of_sep; simp [Region.sep]; omega_using [hdl])
    | (rw [hdl']; simp; omega_using [hdl])
    | exact hk
    | skip

theorem tabMem_lt {m : Mem} {v : MVar} {w : MVar} {a : Addr}
    (h : a.toNat < 0x300000) : tabMem m vs gs v w a = m a := by
  simp only [tabMem, Nat.blt_eq.mpr h, Bool.cond_true]

theorem signPSatBase_key (dl : Nat) {a : Addr} (h : keyIn a.toNat = true) : (signPSatBase dl).mem a = keyMem a := by
  show pMem dl a = keyMem a
  unfold pMem
  rw [h]
  exact Bool.cond_true

theorem signP_sat_of {v : MVar} (hv : v ∈ vs) {w : MVar} (hw : w ∈ gs) (hl : (allNames vs gs).length < 2 ^ 32)
    {dl : Nat} (hdl : dl ≤ 64) (hlen : v.w.l.G.len = dl)
    (hb : ∀ j < 18, stackArg (signPSatBase dl) j = signPArgs dl j) :
    (Sg.signPSpec (MdHashTable.RISCV64.tables vs) (MdHashTable.RISCV64.tables gs)).pre
      (withTabs (signPSatBase dl) vs gs v w) :=
  signP_pre_of hdl rfl rfl (fun j hj => (withTabs_arg _ (signPSat_args dl j hj)).trans (hb j hj)) rfl rfl
    ⟨_, List.mem_map_of_mem hv, withTabs_heldH _⟩ ⟨_, List.mem_map_of_mem hw, withTabs_heldG _⟩
    (symsOf_distinct hl) (fun H hH => by
      have hA := MdHashTable.RISCV64.hashAt_tableOf
        (MdHashTable.RISCV64.held_tableOf (withTabs_heldH (vs := vs) (gs := gs) (v := v) (w := w)
          (signPSatBase dl))).2
      cases hH.symm.trans hA
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hdl]), hlen])
    (key_pre_of fun a ha => by
      have h3 : a.toNat < 0x300000 := by
        simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha; omega
      exact (tabMem_lt h3).trans (signPSatBase_key dl ha))

theorem signPSat_b : ∀ dl ∈ [16, 20, 28, 32, 48, 64], ∀ j < 18,
    stackArg (signPSatBase dl) j = signPArgs dl j := by
  decide

theorem signP_sat (hok : OK vs gs) :
    ∃ s, (Sg.signPSpec (MdHashTable.RISCV64.tables vs) (MdHashTable.RISCV64.tables gs)).pre s := by
  obtain ⟨-, -, -, hl, hv, hw⟩ := hok
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil vs hv
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil gs hw
  have hL := lens_of v
  exact ⟨_, signP_sat_of hv hw hl (by revert hL; generalize v.w.l.G.len = d; decide +revert) rfl
    (signPSat_b _ hL)⟩

/-- `vg_rsa_pss_sign_precomputed`, with the tables of `vs` and `gs`. -/
theorem signP_ok (hok : OK vs gs) :
    Verified RISCV64.target (Impl.RsaPss.RISCV64.Sign.signP (MdHashTable.RISCV64.fnsOf vs)
      (MdHashTable.RISCV64.fns3 gs)) (Sg.signPSpec (MdHashTable.RISCV64.tables vs) (MdHashTable.RISCV64.tables gs)) :=
  ⟨Sg.codeP_correct hok, Sg.codeP_constantTime hok, signP_sat hok⟩

end

end VG.Proof.RsaPss.RISCV64
