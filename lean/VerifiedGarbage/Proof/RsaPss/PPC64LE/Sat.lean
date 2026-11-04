module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Verified
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Verified
public import VerifiedGarbage.Proof.MdHashTable.PPC64LE.Vars
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Mem

/-!
# RSASSA-PSS on PPC64LE with the tables: the contracts are satisfiable

As on x86-64 (`Proof/RsaPss/X86_64/Sat.lean`): by the states of the
contracts with the hash functions fixed, with the table of `MdHash` of a
variant `w` of `vs` at `0x300000`, the table of `Hash` of a variant `w'` of
`gs` at `0x300100` (the stack arguments' values), and the tables' functions
at distinct addresses (`symsOf`): `sign_sat`, `verify_sat`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE
open VG.Proof.HashTable (symsOf symsOf_distinct readW_sep64)
open VG.Proof.HashTable.PPC64LE (TVar)
open VG.Proof.MdHashTable.PPC64LE (MVar)

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
def allNames (vs : List MVar) (gs : List TVar) : List String := MdHashTable.PPC64LE.names vs ++ HashTable.PPC64LE.names gs

/-- The memory `m` with the tables of `w` at `0x300000` and `0x300100`, and
`m` itself below `0x300000`. -/
def tabMem (m : Mem) (vs : List MVar) (gs : List TVar) (w : MVar) (w' : TVar) : Mem := fun a =>
  bif Nat.blt a.toNat 0x300000 then m a
  else putWs (putWs m 0x300000 (tw (allNames vs gs) (MdHashTable.PPC64LE.tableOf w))) 0x300100
    (tw (allNames vs gs) (HashTable.PPC64LE.tableOf w')) a

/-- A state with `s`'s registers and regions, the tables of `w` at `0x300000`
and `0x300100`, and `vs`' functions at distinct addresses. -/
def withTabs (s : State) (vs : List MVar) (gs : List TVar) (w : MVar) (w' : TVar) : State :=
  { s with mem := tabMem s.mem vs gs w w', syms := symsOf (allNames vs gs) }

theorem withTabs_arg (s : State) (vs : List MVar) (gs : List TVar) (w : MVar) (w' : TVar) {j : Nat}
    (hj : (stackArgAddr s j).toNat + 8 ≤ 0x300000) : stackArg (withTabs s vs gs w w') j = stackArg s j := by
  show (tabMem s.mem vs gs w w').readW (stackArgAddr s j) 64 = s.mem.readW (stackArgAddr s j) 64
  refine Mem.readW_congr fun i hi => ?_
  have : (stackArgAddr s j + BitVec.ofNat 64 i).toNat < 0x300000 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  simp only [tabMem, Nat.blt_eq.mpr this, Bool.cond_true]

theorem withTabs_addr (s : State) (vs : List MVar) (gs : List TVar) (w : MVar) (w' : TVar) (j : Nat) :
    stackArgAddr (withTabs s vs gs w w') j = stackArgAddr s j := rfl

/-- Above `0x300000`, the tables' memory. -/
theorem tabMem_above {m : Mem} {vs : List MVar} {gs : List TVar} {w : MVar} {w' : TVar} {p : Addr} {ws : List (BitVec 64)}
    (hp : 0x300000 ≤ p.toNat) (hl : p.toNat + 8 * ws.length < 2 ^ 64)
    (h : Abi.tableHeld 64 (putWs (putWs m 0x300000 (tw (allNames vs gs) (MdHashTable.PPC64LE.tableOf w))) 0x300100
      (tw (allNames vs gs) (HashTable.PPC64LE.tableOf w'))) p ws) :
    Abi.tableHeld 64 (tabMem m vs gs w w') p ws := by
  intro i hi
  rw [← h i hi]
  refine Mem.readW_congr fun k hk => ?_
  have : ¬ (p + BitVec.ofNat 64 (64 / 8 * i) + BitVec.ofNat 64 k).toNat < 0x300000 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hb : Nat.blt (p + BitVec.ofNat 64 (64 / 8 * i) + BitVec.ofNat 64 k).toNat 0x300000 = false := by
    rw [Bool.eq_false_iff]; intro hc; exact this (Nat.blt_eq.mp hc)
  simp only [tabMem, hb, Bool.cond_false]

theorem withTabs_heldH (s : State) (vs : List MVar) (gs : List TVar) (w : MVar) (w' : TVar) :
    Abi.tableHeld 64 (withTabs s vs gs w w').mem 0x300000
      (FnTable.words isa (withTabs s vs gs w w') (MdHashTable.PPC64LE.tableOf w)) := by
  have hl : (tw (allNames vs gs) (MdHashTable.PPC64LE.tableOf w)).length = 11 := by
    simp [tw, MdHashTable.PPC64LE.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf]
  have c1 : (0x300000 : Addr).toNat = 0x300000 := rfl
  have c2 : (0x300100 : Addr).toNat = 0x300100 := rfl
  refine tabMem_above (by rw [c1]) (by simp [FnTable.words, MdHashTable.PPC64LE.tableOf, Spec.MdHashTable.dataOf,
    Spec.HashTable.dataOf]) fun i hi => ?_
  have hi' : i < 11 := by
    simp [FnTable.words, MdHashTable.PPC64LE.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf] at hi; omega
  rw [putWs_out (.inl (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))
    (by simp [tw, HashTable.PPC64LE.tableOf, Spec.HashTable.dataOf]) (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]
  exact putWs_held (by rw [hl]; decide) i (by rw [hl]; exact hi')

theorem withTabs_heldG (s : State) (vs : List MVar) (gs : List TVar) (w : MVar) (w' : TVar) :
    Abi.tableHeld 64 (withTabs s vs gs w w').mem 0x300100
      (FnTable.words isa (withTabs s vs gs w w') (HashTable.PPC64LE.tableOf w')) :=
  tabMem_above (by decide) (by simp [FnTable.words, HashTable.PPC64LE.tableOf, Spec.HashTable.dataOf])
    (putWs_held (by simp [tw, HashTable.PPC64LE.tableOf, Spec.HashTable.dataOf]))


/-! ## Verification with a precomputed key -/

/-- A state meeting verification's precondition but for the tables: a
512-bit modulus, one-byte `e`, a digest of `dl` bytes, 16 words of `pre` at
`0x5000`, the stack arguments at `0x10060`, and the tables' addresses
`0x300000` and `0x300100`. -/
def verifySatBase (dl : Nat) : State where
  gpr r := match r with
    | .r3 => 0x2000 | .r4 => 64 | .r5 => 0x3000 | .r6 => 1 | .r7 => 0x4600 | .r8 => BitVec.ofNat 64 dl
    | .r9 => 0x4000 | .r10 => 64 | _ => 0
  lr := 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10072 then 0x02 else bif Nat.beq a.toNat 0x10078 then 0x20
    else bif Nat.beq a.toNat 0x10079 then 0x08 else bif Nat.beq a.toNat 0x10081 then 0x50
    else bif Nat.beq a.toNat 0x10088 then 16 else bif Nat.beq a.toNat 0x10092 then 0x30
    else bif Nat.beq a.toNat 0x10099 then 0x01 else bif Nat.beq a.toNat 0x1009A then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4600, dl⟩, ⟨0x4000, 64⟩, ⟨0x5000, 128⟩, ⟨0x300000, 88⟩, ⟨0x300100, 40⟩,
    ⟨0x10060, 64⟩]
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
    (hsy : ((tsH.map (fun T : FnTable => T.fns)).flatten ++ (tsG.map (fun T : FnTable => T.fns)).flatten).Pairwise
      fun f g => f ≠ g → s.syms f ≠ s.syms g)
    (hd : Spec.RsaPss.digestLenOk 64 s.mem 0x300000 (BitVec.ofNat 64 dl)) :
    (verSpec tsH tsG).pre s := by
  have e : (304 : Nat) = 303 + 1 := rfl
  unfold verSpec
  rw [e]
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argRegs, stackArgs_eight, List.append_eq, Sig.tableRegion, List.range, List.range.loop]
  have hdl' : (BitVec.ofNat 64 dl).toNat = dl := by rw [BitVec.toNat_ofNat]; omega
  have hA : ∀ j, stackArgAddr s j = 0x10000 + BitVec.ofNat 64 (32 + 8 * (8 + j)) := fun j => by
    simp only [stackArgAddr, hsp]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), hg, hsp, hrd, hwr, hA, verifyArgs]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argRegs, stackArgs_eight, List.append_eq, Sig.tableRegion, List.range, List.range.loop]
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

theorem verify_sat_of {vs : List MVar} {gs : List TVar} {w : MVar} (hw : w ∈ vs) {w' : TVar} (hw' : w' ∈ gs)
    (hl : (allNames vs gs).length < 2 ^ 32) {dl : Nat} (hdl : dl ≤ 64)
    (hlen : w.l.G.len = dl) (hb : ∀ j < 8, stackArg (verifySatBase dl) j = verifyArgs j) :
    (verSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)).pre (withTabs (verifySatBase dl) vs gs w w') :=
  verify_pre_of hdl rfl rfl (fun j hj => (withTabs_arg _ vs gs w w' (verifySat_args dl j hj)).trans (hb j hj)) rfl rfl
    ⟨_, List.mem_map_of_mem hw, withTabs_heldH _ vs gs w w'⟩ ⟨_, List.mem_map_of_mem hw', withTabs_heldG _ vs gs w w'⟩
    (symsOf_distinct hl) fun H hH => by
      have hA := MdHashTable.PPC64LE.hashAt_tableOf
        (MdHashTable.PPC64LE.held_tableOf (withTabs_heldH (verifySatBase dl) vs gs w w')).2.2.2
      cases hH.symm.trans hA
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hlen]

theorem verifySat_b16 : ∀ j < 8, stackArg (verifySatBase 16) j = verifyArgs j := by decide
theorem verifySat_b20 : ∀ j < 8, stackArg (verifySatBase 20) j = verifyArgs j := by decide
theorem verifySat_b28 : ∀ j < 8, stackArg (verifySatBase 28) j = verifyArgs j := by decide
theorem verifySat_b32 : ∀ j < 8, stackArg (verifySatBase 32) j = verifyArgs j := by decide
theorem verifySat_b48 : ∀ j < 8, stackArg (verifySatBase 48) j = verifyArgs j := by decide
theorem verifySat_b64 : ∀ j < 8, stackArg (verifySatBase 64) j = verifyArgs j := by decide

theorem verify_sat {vs : List MVar} {gs : List TVar} {w : MVar} (hw : w ∈ vs) {w' : TVar} (hw' : w' ∈ gs)
    (hl : (allNames vs gs).length < 2 ^ 32) :
    ∃ s, (verSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)).pre s := by
  have hm := w.l.lens_mem
  rw [← w.l.len] at hm
  simp only [Impl.RsaOaep.PPC64LE.lens, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e
  · exact ⟨_, verify_sat_of hw hw' hl (by decide) e verifySat_b16⟩
  · exact ⟨_, verify_sat_of hw hw' hl (by decide) e verifySat_b20⟩
  · exact ⟨_, verify_sat_of hw hw' hl (by decide) e verifySat_b28⟩
  · exact ⟨_, verify_sat_of hw hw' hl (by decide) e verifySat_b32⟩
  · exact ⟨_, verify_sat_of hw hw' hl (by decide) e verifySat_b48⟩
  · exact ⟨_, verify_sat_of hw hw' hl (by decide) e verifySat_b64⟩

/-! ## Signing -/

/-- A state meeting signing's precondition but for the tables: a 512-bit
modulus, one-byte `e`, primes, exponents and `qInv`, a digest of `dl` bytes,
an empty salt, a working space of 2080 words, the stack arguments at
`0x10060`, and the tables' addresses `0x300000` and `0x300100`. -/
def signSatBase (dl : Nat) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x2000 | .r6 => 64 | .r7 => 0x3000 | .r8 => 1 | .r9 => 0x4200
    | .r10 => 1 | _ => 0
  lr := 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10061 then 0x43
    else bif Nat.beq a.toNat 0x10068 then 1 else bif Nat.beq a.toNat 0x10071 then 0x44
    else bif Nat.beq a.toNat 0x10078 then 1 else bif Nat.beq a.toNat 0x10081 then 0x45
    else bif Nat.beq a.toNat 0x10088 then 1 else bif Nat.beq a.toNat 0x10091 then 0x46
    else bif Nat.beq a.toNat 0x10098 then 1 else bif Nat.beq a.toNat 0x100A1 then 0x41
    else bif Nat.beq a.toNat 0x100A8 then BitVec.ofNat 8 dl else bif Nat.beq a.toNat 0x100B1 then 0x47
    else bif Nat.beq a.toNat 0x100C2 then 0x02 else bif Nat.beq a.toNat 0x100C8 then 0x20
    else bif Nat.beq a.toNat 0x100C9 then 0x08 else bif Nat.beq a.toNat 0x100D2 then 0x30
    else bif Nat.beq a.toNat 0x100D9 then 0x01 else bif Nat.beq a.toNat 0x100DA then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩, ⟨0x4500, 1⟩, ⟨0x4600, 1⟩,
    ⟨0x4100, dl⟩, ⟨0x4700, 0⟩, ⟨0x300000, 88⟩, ⟨0x300100, 40⟩, ⟨0x10060, 128⟩]
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
    (hsy : ((tsH.map (fun T : FnTable => T.fns)).flatten ++ (tsG.map (fun T : FnTable => T.fns)).flatten).Pairwise
      fun f g => f ≠ g → s.syms f ≠ s.syms g)
    (hd : Spec.RsaPss.digestLenOk 64 s.mem 0x300000 (BitVec.ofNat 64 dl)) :
    (Sg.signSpec tsH tsG).pre s := by
  have e : Sg.stackBytes = 3775 + 1 := rfl
  unfold Sg.signSpec
  rw [e]
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argRegs, Sg.stackArgs_sixteen, List.append_eq, Sig.tableRegion, List.range, List.range.loop]
  have hdl' : (BitVec.ofNat 64 dl).toNat = dl := by rw [BitVec.toNat_ofNat]; omega
  have hA : ∀ j, stackArgAddr s j = 0x10000 + BitVec.ofNat 64 (32 + 8 * (8 + j)) := fun j => by
    simp only [stackArgAddr, hsp]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide),
    ha 11 (by decide), ha 12 (by decide), ha 13 (by decide), ha 14 (by decide), ha 15 (by decide), hg, hsp, hrd,
    hwr, hA, signArgs]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argRegs, Sg.stackArgs_sixteen, List.append_eq, Sig.tableRegion, List.range, List.range.loop]
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

theorem sign_sat_of {vs : List MVar} {gs : List TVar} {w : MVar} (hw : w ∈ vs) {w' : TVar} (hw' : w' ∈ gs)
    (hl : (allNames vs gs).length < 2 ^ 32) {dl : Nat} (hdl : dl ≤ 64)
    (hlen : w.l.G.len = dl) (hb : ∀ j < 16, stackArg (signSatBase dl) j = signArgs dl j) :
    (Sg.signSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)).pre
      (withTabs (signSatBase dl) vs gs w w') :=
  sign_pre_of hdl rfl rfl (fun j hj => (withTabs_arg _ vs gs w w' (signSat_args dl j hj)).trans (hb j hj)) rfl rfl
    ⟨_, List.mem_map_of_mem hw, withTabs_heldH _ vs gs w w'⟩ ⟨_, List.mem_map_of_mem hw', withTabs_heldG _ vs gs w w'⟩
    (symsOf_distinct hl) fun H hH => by
      have hA := MdHashTable.PPC64LE.hashAt_tableOf
        (MdHashTable.PPC64LE.held_tableOf (withTabs_heldH (signSatBase dl) vs gs w w')).2.2.2
      cases hH.symm.trans hA
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hlen]

theorem signSat_b16 : ∀ j < 16, stackArg (signSatBase 16) j = signArgs 16 j := by decide
theorem signSat_b20 : ∀ j < 16, stackArg (signSatBase 20) j = signArgs 20 j := by decide
theorem signSat_b28 : ∀ j < 16, stackArg (signSatBase 28) j = signArgs 28 j := by decide
theorem signSat_b32 : ∀ j < 16, stackArg (signSatBase 32) j = signArgs 32 j := by decide
theorem signSat_b48 : ∀ j < 16, stackArg (signSatBase 48) j = signArgs 48 j := by decide
theorem signSat_b64 : ∀ j < 16, stackArg (signSatBase 64) j = signArgs 64 j := by decide

theorem sign_sat {vs : List MVar} {gs : List TVar} {w : MVar} (hw : w ∈ vs) {w' : TVar} (hw' : w' ∈ gs)
    (hl : (allNames vs gs).length < 2 ^ 32) :
    ∃ s, (Sg.signSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)).pre s := by
  have hm := w.l.lens_mem
  rw [← w.l.len] at hm
  simp only [Impl.RsaOaep.PPC64LE.lens, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e
  · exact ⟨_, sign_sat_of hw hw' hl (by decide) e signSat_b16⟩
  · exact ⟨_, sign_sat_of hw hw' hl (by decide) e signSat_b20⟩
  · exact ⟨_, sign_sat_of hw hw' hl (by decide) e signSat_b28⟩
  · exact ⟨_, sign_sat_of hw hw' hl (by decide) e signSat_b32⟩
  · exact ⟨_, sign_sat_of hw hw' hl (by decide) e signSat_b48⟩
  · exact ⟨_, sign_sat_of hw hw' hl (by decide) e signSat_b64⟩

/-! ## The instances -/

/-- What the registration checks of the variants: their functions of the
same name have the same code, there are some, and not too many names. -/
def OK (vs : List MVar) (gs : List TVar) : Prop :=
  MdHashTable.PPC64LE.Coh vs ∧ HashTable.PPC64LE.Coh gs ∧ vs ≠ [] ∧ gs ≠ [] ∧ (allNames vs gs).length < 2 ^ 32

instance (vs : List MVar) (gs : List TVar) : Decidable (OK vs gs) := by unfold OK; infer_instance

theorem ok_mem {vs : List MVar} {gs : List TVar} (h : OK vs gs) : ∃ w, w ∈ vs ∧ ∃ w', w' ∈ gs := by
  obtain ⟨-, -, h1, h2, -⟩ := h
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ h1
  obtain ⟨w', hw'⟩ := List.exists_mem_of_ne_nil _ h2
  exact ⟨w, hw, w', hw'⟩

/-- `vg_rsa_pss_verify_precomputed`, with the tables of `vs` and `gs`. -/
theorem verify_ok' {vs : List MVar} {gs : List TVar} (h : OK vs gs) :
    Verified PPC64LE.target (Impl.RsaPss.PPC64LE.verifyPrecomputed (MdHashTable.PPC64LE.fnsOf vs)
      (HashTable.PPC64LE.fnsOf gs)) (verSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)) :=
  let ⟨_, hw, _, hw'⟩ := ok_mem h
  verify_verified h.1 h.2.1 (verify_sat hw hw' h.2.2.2.2)

/-- `vg_rsa_pss_sign`, with the tables of `vs` and `gs`. -/
theorem sign_ok' {vs : List MVar} {gs : List TVar} (h : OK vs gs) :
    Verified PPC64LE.target (Impl.RsaPss.PPC64LE.Sign.sign (MdHashTable.PPC64LE.fnsOf vs)
      (HashTable.PPC64LE.fnsOf gs)) (Sg.signSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)) :=
  let ⟨_, hw, _, hw'⟩ := ok_mem h
  Sg.sign_verified h.1 h.2.1 (sign_sat hw hw' h.2.2.2.2)

end VG.Proof.RsaPss.PPC64LE
