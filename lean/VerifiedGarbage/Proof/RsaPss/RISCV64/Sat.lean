module

public import VerifiedGarbage.Proof.RsaPss.RISCV64.Inst
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Sg.Inst
import VerifiedGarbage.Proof.Framework.Contract

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
open VG.Proof.HashTable (symsOf symsOf_distinct readW_sep64)
open VG.Proof.MdHashTable.RISCV64 (MVar)
open VG.Proof.HashTable.RISCV64 (TVar)

/-- The words `ws` written from `p`. -/
def putWs (m : Mem) (p : Addr) : List (BitVec 64) → Mem
  | [] => m
  | w :: ws => putWs (m.writeW p w) (p + 8) ws

theorem add8_toNat {p : Addr} (h : p.toNat + 8 < 2 ^ 64) : (p + 8).toNat = p.toNat + 8 := by
  rw [BitVec.toNat_add, show (8 : Addr).toNat = 8 from rfl, Nat.mod_eq_of_lt h]

/-- A word apart from the words `putWs` writes. -/
theorem putWs_out {m : Mem} {a : Addr} : ∀ {p : Addr} {ws : List (BitVec 64)},
    (a.toNat + 8 ≤ p.toNat ∨ p.toNat + 8 * ws.length ≤ a.toNat) → p.toNat + 8 * ws.length < 2 ^ 64 →
    a.toNat + 8 ≤ 2 ^ 64 → (putWs m p ws).readW a 64 = m.readW a 64
  | _, [], _, _, _ => rfl
  | p, w :: ws, h, hp, ha => by
    simp only [List.length_cons] at h hp
    have h8 := add8_toNat (p := p) (by omega)
    simp only [putWs]
    rw [putWs_out (by rw [h8]; omega) (by rw [h8]; omega) ha, readW_sep64 (by omega) ha (by omega)]

/-- The words `putWs` writes. -/
theorem putWs_held {m : Mem} : ∀ {p : Addr} {ws : List (BitVec 64)}, p.toNat + 8 * ws.length < 2 ^ 64 →
    Abi.tableHeld 64 (putWs m p ws) p ws
  | _, [], _ => fun i hi => absurd hi (Nat.not_lt_zero _)
  | p, w :: ws, hp => by
    simp only [List.length_cons] at hp
    have h8 := add8_toNat (p := p) (by omega)
    intro i hi
    simp only [putWs]
    cases i with
    | zero =>
      rw [show p + BitVec.ofNat 64 (64 / 8 * 0) = p from BitVec.add_zero p,
        putWs_out (.inl (by rw [h8])) (by rw [h8]; omega) (by omega), Mem.readW_writeW_self64]
      simp
    | succ i =>
      have := putWs_held (m := m.writeW p w) (p := p + 8) (ws := ws) (by rw [h8]; omega) i
        (by simp at hi; omega)
      rw [show p + BitVec.ofNat 64 (64 / 8 * (i + 1)) = p + 8 + BitVec.ofNat 64 (64 / 8 * i) by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega]
      simpa using this

/-- The words of a table, its functions at the addresses `symsOf ns`. -/
def tw (ns : List String) (T : FnTable) : List (BitVec 64) := T.fns.map (symsOf ns) ++ T.data

/-- The names of the tables' functions. -/
def allNames (vs : List MVar) (gs : List TVar) : List String :=
  MdHashTable.RISCV64.names vs ++ HashTable.RISCV64.names gs

/-- The memory `m` with the tables of `v` at `0x300000` and of `w` at
`0x300100`, and `m` itself below `0x300000`. -/
def tabMem (m : Mem) (vs : List MVar) (gs : List TVar) (v : MVar) (w : TVar) : Mem := fun a =>
  bif Nat.blt a.toNat 0x300000 then m a
  else putWs (putWs m 0x300000 (tw (allNames vs gs) (MdHashTable.RISCV64.tableOf v))) 0x300100
    (tw (allNames vs gs) (HashTable.RISCV64.tableOf w)) a

/-- A state with `s`'s registers and regions, the tables of `v` at `0x300000`
and of `w` at `0x300100`, and the tables' functions at distinct addresses. -/
def withTabs (s : State) (vs : List MVar) (gs : List TVar) (v : MVar) (w : TVar) : State :=
  { s with mem := tabMem s.mem vs gs v w, syms := symsOf (allNames vs gs) }

section
variable {vs : List MVar} {gs : List TVar} {v : MVar} {w : TVar}

theorem withTabs_arg (s : State) {j : Nat} (hj : (stackArgAddr s j).toNat + 8 ≤ 0x300000) :
    stackArg (withTabs s vs gs v w) j = stackArg s j := by
  show (tabMem s.mem vs gs v w).readW (stackArgAddr s j) 64 = s.mem.readW (stackArgAddr s j) 64
  refine Mem.readW_congr fun i hi => ?_
  have : (stackArgAddr s j + BitVec.ofNat 64 i).toNat < 0x300000 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  simp only [tabMem, Nat.blt_eq.mpr this, Bool.cond_true]

/-- Above `0x300000`, the tables' memory. -/
theorem tabMem_above {m : Mem} {p : Addr} {ws : List (BitVec 64)}
    (hp : 0x300000 ≤ p.toNat) (hl : p.toNat + 8 * ws.length < 2 ^ 64)
    (h : Abi.tableHeld 64 (putWs (putWs m 0x300000 (tw (allNames vs gs) (MdHashTable.RISCV64.tableOf v))) 0x300100
      (tw (allNames vs gs) (HashTable.RISCV64.tableOf w))) p ws) :
    Abi.tableHeld 64 (tabMem m vs gs v w) p ws := by
  intro i hi
  rw [← h i hi]
  refine Mem.readW_congr fun k hk => ?_
  have : ¬ (p + BitVec.ofNat 64 (64 / 8 * i) + BitVec.ofNat 64 k).toNat < 0x300000 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
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
    Spec.HashTable.dataOf]) fun i hi => ?_
  have hi' : i < 11 := by
    simp [FnTable.words, MdHashTable.RISCV64.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf] at hi; omega
  rw [putWs_out (.inl (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))
    (by simp [tw, HashTable.RISCV64.tableOf, Spec.HashTable.dataOf])
    (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]
  exact putWs_held (by rw [hl]; decide) i (by rw [hl]; exact hi')

theorem withTabs_heldG (s : State) :
    Abi.tableHeld 64 (withTabs s vs gs v w).mem 0x300100
      (FnTable.words isa (withTabs s vs gs v w) (HashTable.RISCV64.tableOf w)) :=
  tabMem_above (by decide) (by simp [FnTable.words, HashTable.RISCV64.tableOf, Spec.HashTable.dataOf])
    (putWs_held (by simp [tw, HashTable.RISCV64.tableOf, Spec.HashTable.dataOf]))

end

/-- The functions of the tables. -/
def tabFns (ts : List FnTable) : List String := (ts.map (·.fns)).flatten

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
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4600, dl⟩, ⟨0x4000, 64⟩, ⟨0x5000, 128⟩, ⟨0x300000, 88⟩, ⟨0x300100, 40⟩,
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
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argRegs, stackArgs_eight, List.append_eq, Sig.tableRegion]
  have hdl' : (BitVec.ofNat 64 dl).toNat = dl := by rw [BitVec.toNat_ofNat]; omega
  have hA : ∀ j, stackArgAddr s j = 0x10000 + BitVec.ofNat 64 (8 * j) := fun j => by
    simp only [stackArgAddr, hsp]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), hg, hsp, hrd, hwr, hA, verifyArgs, verifySatBase]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argRegs, stackArgs_eight, List.append_eq, Sig.tableRegion]
  sig_and_intros
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

variable {vs : List MVar} {gs : List TVar}

theorem verify_sat_of {v : MVar} (hv : v ∈ vs) {w : TVar} (hw : w ∈ gs) (hl : (allNames vs gs).length < 2 ^ 32)
    {dl : Nat} (hdl : dl ≤ 64) (hlen : v.w.l.G.len = dl)
    (hb : ∀ j < 8, stackArg (verifySatBase dl) j = verifyArgs j) :
    (verSpec (MdHashTable.RISCV64.tables vs) (HashTable.RISCV64.tables gs)).pre (withTabs (verifySatBase dl) vs gs v w) :=
  verify_pre_of hdl rfl rfl (fun j hj => (withTabs_arg _ (verifySat_args dl j hj)).trans (hb j hj)) rfl rfl
    ⟨_, List.mem_map_of_mem hv, withTabs_heldH _⟩ ⟨_, List.mem_map_of_mem hw, withTabs_heldG _⟩
    (symsOf_distinct hl) fun H hH => by
      have hA := MdHashTable.RISCV64.hashAt_tableOf
        (MdHashTable.RISCV64.held_tableOf (withTabs_heldH (vs := vs) (gs := gs) (v := v) (w := w)
          (verifySatBase dl))).2
      cases hH.symm.trans hA
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hlen]

theorem verifySat_b : ∀ dl ∈ [16, 20, 28, 32, 48, 64], ∀ j < 8, stackArg (verifySatBase dl) j = verifyArgs j := by
  decide

theorem lens_of (v : MVar) : v.w.l.G.len ∈ [16, 20, 28, 32, 48, 64] := by
  have hm := v.w.l.mem
  simp only [Proof.RsaOaep.RISCV64.labelHashes, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e | e | e <;> rw [e] <;> decide

theorem verify_sat (hok : OK vs gs) :
    ∃ s, (verSpec (MdHashTable.RISCV64.tables vs) (HashTable.RISCV64.tables gs)).pre s := by
  obtain ⟨-, -, -, hl, hv, hw⟩ := hok
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil vs hv
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil gs hw
  have hL := lens_of v
  exact ⟨_, verify_sat_of hv hw hl (by revert hL; generalize v.w.l.G.len = d; decide +revert) rfl
    (verifySat_b _ hL)⟩

/-- `vg_rsa_pss_verify_precomputed`, with the tables of `vs` and `gs`. -/
theorem verify_ok (hok : OK vs gs) :
    Verified RISCV64.target (Impl.RsaPss.RISCV64.verifyPrecomputed (MdHashTable.RISCV64.fnsOf vs)
      (HashTable.RISCV64.fnsOf gs)) (verSpec (MdHashTable.RISCV64.tables vs) (HashTable.RISCV64.tables gs)) :=
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
    ⟨0x4100, dl⟩, ⟨0x4700, 0⟩, ⟨0x300000, 88⟩, ⟨0x300100, 40⟩, ⟨0x10000, 128⟩]
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
  have e : Sg.stackBytes = 3471 + 1 := rfl
  unfold Sg.signSpec
  rw [e]
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
    Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs,
    Sg.stackArgs_sixteen, List.append_eq, Sig.tableRegion]
  have hdl' : (BitVec.ofNat 64 dl).toNat = dl := by rw [BitVec.toNat_ofNat]; omega
  have hA : ∀ j, stackArgAddr s j = 0x10000 + BitVec.ofNat 64 (8 * j) := fun j => by
    simp only [stackArgAddr, hsp]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide),
    ha 11 (by decide), ha 12 (by decide), ha 13 (by decide), ha 14 (by decide), ha 15 (by decide), hg, hsp, hrd,
    hwr, hA, signArgs, signSatBase]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
    Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs,
    Sg.stackArgs_sixteen, List.append_eq, Sig.tableRegion]
  sig_and_intros
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

theorem sign_sat_of {v : MVar} (hv : v ∈ vs) {w : TVar} (hw : w ∈ gs) (hl : (allNames vs gs).length < 2 ^ 32)
    {dl : Nat} (hdl : dl ≤ 64) (hlen : v.w.l.G.len = dl)
    (hb : ∀ j < 16, stackArg (signSatBase dl) j = signArgs dl j) :
    (Sg.signSpec (MdHashTable.RISCV64.tables vs) (HashTable.RISCV64.tables gs)).pre
      (withTabs (signSatBase dl) vs gs v w) :=
  sign_pre_of hdl rfl rfl (fun j hj => (withTabs_arg _ (signSat_args dl j hj)).trans (hb j hj)) rfl rfl
    ⟨_, List.mem_map_of_mem hv, withTabs_heldH _⟩ ⟨_, List.mem_map_of_mem hw, withTabs_heldG _⟩
    (symsOf_distinct hl) fun H hH => by
      have hA := MdHashTable.RISCV64.hashAt_tableOf
        (MdHashTable.RISCV64.held_tableOf (withTabs_heldH (vs := vs) (gs := gs) (v := v) (w := w)
          (signSatBase dl))).2
      cases hH.symm.trans hA
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hlen]

theorem signSat_b : ∀ dl ∈ [16, 20, 28, 32, 48, 64], ∀ j < 16, stackArg (signSatBase dl) j = signArgs dl j := by
  decide

theorem sign_sat (hok : OK vs gs) :
    ∃ s, (Sg.signSpec (MdHashTable.RISCV64.tables vs) (HashTable.RISCV64.tables gs)).pre s := by
  obtain ⟨-, -, -, hl, hv, hw⟩ := hok
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil vs hv
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil gs hw
  have hL := lens_of v
  exact ⟨_, sign_sat_of hv hw hl (by revert hL; generalize v.w.l.G.len = d; decide +revert) rfl
    (signSat_b _ hL)⟩

/-- `vg_rsa_pss_sign`, with the tables of `vs` and `gs`. -/
theorem sign_ok (hok : OK vs gs) :
    Verified RISCV64.target (Impl.RsaPss.RISCV64.Sign.sign (MdHashTable.RISCV64.fnsOf vs)
      (HashTable.RISCV64.fnsOf gs)) (Sg.signSpec (MdHashTable.RISCV64.tables vs) (HashTable.RISCV64.tables gs)) :=
  ⟨Sg.code_correct hok, Sg.code_constantTime hok, sign_sat hok⟩

end VG.Proof.RsaPss.RISCV64
