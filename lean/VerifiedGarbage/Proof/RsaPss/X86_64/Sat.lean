module

public import VerifiedGarbage.Proof.RsaPss.X86_64.Instances
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSASSA-PSS on x86-64 with the tables of `vs`: the contracts are satisfiable

By the states of the contracts with the hash functions fixed, with the table
of `MdHash` of a variant `w` of `vs` at `0x300000`, the table of `Hash` of
`w` at `0x300100` (the stack arguments' values), and the tables' functions at
distinct addresses (`symsOf`): `sign_sat`, `verify_sat`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)
open VG.Proof.HashTable (symsOf symsOf_distinct readW_sep64)
open VG.Proof.Bignum VG.Proof.Bignum.X86_64

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
def allNames (vs : List MdHash) : List String := MdHashTable.X86_64.names vs ++ HashTable.X86_64.names vs

/-- The memory `m` with the tables of `w` at `0x300000` and `0x300100`, and
`m` itself below `0x300000`. -/
def tabMem (m : Mem) (vs : List MdHash) (w : MdHash) : Mem := fun a =>
  bif Nat.blt a.toNat 0x300000 then m a
  else putWs (putWs m 0x300000 (tw (allNames vs) (MdHashTable.X86_64.tableOf w))) 0x300100
    (tw (allNames vs) (HashTable.X86_64.tableOf w)) a

/-- A state with `s`'s registers and regions, the tables of `w` at `0x300000`
and `0x300100`, and `vs`' functions at distinct addresses. -/
def withTabs (s : State) (vs : List MdHash) (w : MdHash) : State :=
  { s with mem := tabMem s.mem vs w, syms := symsOf (allNames vs) }

theorem withTabs_arg (s : State) (vs : List MdHash) (w : MdHash) {j : Nat}
    (hj : (stackArgAddr s j).toNat + 8 ≤ 0x300000) : stackArg (withTabs s vs w) j = stackArg s j := by
  show (tabMem s.mem vs w).readW (stackArgAddr s j) 64 = s.mem.readW (stackArgAddr s j) 64
  refine Mem.readW_congr fun i hi => ?_
  have : (stackArgAddr s j + BitVec.ofNat 64 i).toNat < 0x300000 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  simp only [tabMem, Nat.blt_eq.mpr this, Bool.cond_true]

theorem withTabs_addr (s : State) (vs : List MdHash) (w : MdHash) (j : Nat) :
    stackArgAddr (withTabs s vs w) j = stackArgAddr s j := rfl

/-- Above `0x300000`, the tables' memory. -/
theorem tabMem_above {m : Mem} {vs : List MdHash} {w : MdHash} {p : Addr} {ws : List (BitVec 64)}
    (hp : 0x300000 ≤ p.toNat) (hl : p.toNat + 8 * ws.length < 2 ^ 64)
    (h : Abi.tableHeld 64 (putWs (putWs m 0x300000 (tw (allNames vs) (MdHashTable.X86_64.tableOf w))) 0x300100
      (tw (allNames vs) (HashTable.X86_64.tableOf w))) p ws) :
    Abi.tableHeld 64 (tabMem m vs w) p ws := by
  intro i hi
  rw [← h i hi]
  refine Mem.readW_congr fun k hk => ?_
  have : ¬ (p + BitVec.ofNat 64 (64 / 8 * i) + BitVec.ofNat 64 k).toNat < 0x300000 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hb : Nat.blt (p + BitVec.ofNat 64 (64 / 8 * i) + BitVec.ofNat 64 k).toNat 0x300000 = false := by
    rw [Bool.eq_false_iff]; intro hc; exact this (Nat.blt_eq.mp hc)
  simp only [tabMem, hb, Bool.cond_false]

theorem withTabs_heldH (s : State) (vs : List MdHash) (w : MdHash) :
    Abi.tableHeld 64 (withTabs s vs w).mem 0x300000
      (FnTable.words isa (withTabs s vs w) (MdHashTable.X86_64.tableOf w)) := by
  have hl : (tw (allNames vs) (MdHashTable.X86_64.tableOf w)).length = 11 := by
    simp [tw, MdHashTable.X86_64.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf]
  have c1 : (0x300000 : Addr).toNat = 0x300000 := rfl
  have c2 : (0x300100 : Addr).toNat = 0x300100 := rfl
  refine tabMem_above (by rw [c1]) (by simp [FnTable.words, MdHashTable.X86_64.tableOf, Spec.MdHashTable.dataOf,
    Spec.HashTable.dataOf]) fun i hi => ?_
  have hi' : i < 11 := by
    simp [FnTable.words, MdHashTable.X86_64.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf] at hi; omega
  rw [putWs_out (.inl (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))
    (by simp [tw, HashTable.X86_64.tableOf, Spec.HashTable.dataOf]) (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]
  exact putWs_held (by rw [hl]; decide) i (by rw [hl]; exact hi')

theorem withTabs_heldG (s : State) (vs : List MdHash) (w : MdHash) :
    Abi.tableHeld 64 (withTabs s vs w).mem 0x300100
      (FnTable.words isa (withTabs s vs w) (HashTable.X86_64.tableOf w)) :=
  tabMem_above (by decide) (by simp [FnTable.words, HashTable.X86_64.tableOf, Spec.HashTable.dataOf])
    (putWs_held (by simp [tw, HashTable.X86_64.tableOf, Spec.HashTable.dataOf]))

/-! ## Signing -/

/-- A state meeting signing's precondition but for the tables: a 512-bit
modulus, one-byte `e`, primes, exponents and `qInv`, a digest of `dl` bytes,
an empty salt, the stack arguments at `0x10008`, and the tables' addresses
`0x300000` and `0x300100`. -/
def signSatBase (dl : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x3000 | .r9 => 1
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := bif Nat.beq a.toNat 0x10009 then 0x41 else bif Nat.beq a.toNat 0x10010 then 1
    else bif Nat.beq a.toNat 0x10019 then 0x42 else bif Nat.beq a.toNat 0x10020 then 1
    else bif Nat.beq a.toNat 0x10029 then 0x43 else bif Nat.beq a.toNat 0x10030 then 1
    else bif Nat.beq a.toNat 0x10039 then 0x44 else bif Nat.beq a.toNat 0x10040 then 1
    else bif Nat.beq a.toNat 0x10049 then 0x45 else bif Nat.beq a.toNat 0x10050 then 1
    else bif Nat.beq a.toNat 0x10059 then 0x46 else bif Nat.beq a.toNat 0x10060 then BitVec.ofNat 8 dl
    else bif Nat.beq a.toNat 0x10069 then 0x47 else bif Nat.beq a.toNat 0x1007A then 0x02
    else bif Nat.beq a.toNat 0x10080 then 0x20 else bif Nat.beq a.toNat 0x10081 then 0x08
    else bif Nat.beq a.toNat 0x1008A then 0x30 else bif Nat.beq a.toNat 0x10091 then 0x01
    else bif Nat.beq a.toNat 0x10092 then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩, ⟨0x4500, 1⟩,
    ⟨0x4600, dl⟩, ⟨0x4700, 0⟩, ⟨0x300000, 88⟩, ⟨0x300100, 40⟩, ⟨0x10008, 144⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 2080 * 8⟩]


variable {vs : List MdHash}

theorem signSat_args (dl : Nat) : ∀ j < 18, (stackArgAddr (signSatBase dl) j).toNat + 8 ≤ 0x300000 := fun j hj => by
  have c0 : (65536 : Addr).toNat = 65536 := rfl
  simp only [stackArgAddr, signSatBase, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The stack arguments of `signSatBase dl`. -/
def signArgs (dl : Nat) : Nat → BitVec 64
  | 0 => 0x4100 | 1 => 1 | 2 => 0x4200 | 3 => 1 | 4 => 0x4300 | 5 => 1 | 6 => 0x4400 | 7 => 1
  | 8 => 0x4500 | 9 => 1 | 10 => 0x4600 | 11 => BitVec.ofNat 64 dl | 12 => 0x4700 | 13 => 0
  | 14 => 0x20000 | 15 => 2080 | 16 => 0x300000 | _ => 0x300100

/-- Signing's precondition, from the facts of a state. -/
theorem sign_pre_of {tsH tsG : List FnTable} {dl : Nat} (hdl : dl ≤ 64) {s : State}
    (hg : s.gpr = (signSatBase dl).gpr) (ha : ∀ j < 18, stackArg s j = signArgs dl j)
    (hrd : s.rd = (signSatBase dl).rd) (hwr : s.wr = (signSatBase dl).wr)
    (hH : ∃ T ∈ tsH, Abi.tableHeld 64 s.mem 0x300000 (FnTable.words isa s T))
    (hG : ∃ T ∈ tsG, Abi.tableHeld 64 s.mem 0x300100 (FnTable.words isa s T))
    (hsy : (tabFns tsH ++ tabFns tsG).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g)
    (hd : Spec.RsaPss.digestLenOk 64 s.mem 0x300000 (BitVec.ofNat 64 dl)) :
    (signC tsH tsG).pre s := by
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
    Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs, signStack,
    stackArgs_eighteen, List.append_eq, Sig.tableRegion]
  have hsp : s.gpr .rsp = 0x10000 := by rw [hg]; rfl
  have hdl' : (BitVec.ofNat 64 dl).toNat = dl := by rw [BitVec.toNat_ofNat]; omega
  have hA : ∀ j, stackArgAddr s j = 0x10000 + BitVec.ofNat 64 (8 * (j + 1)) := fun j => by
    simp only [stackArgAddr, hsp]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide),
    ha 11 (by decide), ha 12 (by decide), ha 13 (by decide), ha 14 (by decide), ha 15 (by decide),
    ha 16 (by decide), ha 17 (by decide), hg, hrd, hwr, hA, signArgs]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
    Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs, signStack,
    stackArgs_eighteen, List.append_eq, Sig.tableRegion]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | assumption
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (rw [hdl']; rfl)
    | (rw [hdl']; apply Region.disjoint_of_sep; simp [Region.sep]; omega)
    | (rw [hdl']; simp; omega)
    | skip

theorem sign_sat_of {w : MdHash} (hw : w ∈ vs) (hl : (allNames vs).length < 2 ^ 32) {dl : Nat} (hdl : dl ≤ 64)
    (hlen : w.mgf.G.len = dl) (hb : ∀ j < 18, stackArg (signSatBase dl) j = signArgs dl j) :
    (signC (MdHashTable.X86_64.tables vs) (HashTable.X86_64.tables vs)).pre (withTabs (signSatBase dl) vs w) :=
  sign_pre_of hdl rfl (fun j hj => (withTabs_arg _ vs w (signSat_args dl j hj)).trans (hb j hj)) rfl rfl
    ⟨_, List.mem_map_of_mem hw, withTabs_heldH _ vs w⟩ ⟨_, List.mem_map_of_mem hw, withTabs_heldG _ vs w⟩
    (symsOf_distinct hl) fun H hH => by
      have hA := MdHashTable.X86_64.hashAt_tableOf
        (MdHashTable.X86_64.held_tableOf (withTabs_heldH (signSatBase dl) vs w)).2.2.2.1
      cases hH.symm.trans hA
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hlen]

theorem signSat_b16 : ∀ j < 18, stackArg (signSatBase 16) j = signArgs 16 j := by decide
theorem signSat_b20 : ∀ j < 18, stackArg (signSatBase 20) j = signArgs 20 j := by decide
theorem signSat_b28 : ∀ j < 18, stackArg (signSatBase 28) j = signArgs 28 j := by decide
theorem signSat_b32 : ∀ j < 18, stackArg (signSatBase 32) j = signArgs 32 j := by decide
theorem signSat_b48 : ∀ j < 18, stackArg (signSatBase 48) j = signArgs 48 j := by decide
theorem signSat_b64 : ∀ j < 18, stackArg (signSatBase 64) j = signArgs 64 j := by decide

theorem sign_sat (hok : OK vs) :
    ∃ s, (signC (MdHashTable.X86_64.tables vs) (HashTable.X86_64.tables vs)).pre s := by
  obtain ⟨w, hw, -⟩ := hok.2.2.2.1 0 (by decide)
  have hl := hok.2.2.2.2
  have hm := w.mgf.mem
  simp only [Pbkdf2.Md.X86_64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e | e | e
  · exact ⟨_, sign_sat_of hw hl (by decide) (by rw [e]; rfl) signSat_b16⟩
  · exact ⟨_, sign_sat_of hw hl (by decide) (by rw [e]; rfl) signSat_b20⟩
  · exact ⟨_, sign_sat_of hw hl (by decide) (by rw [e]; rfl) signSat_b28⟩
  · exact ⟨_, sign_sat_of hw hl (by decide) (by rw [e]; rfl) signSat_b32⟩
  · exact ⟨_, sign_sat_of hw hl (by decide) (by rw [e]; rfl) signSat_b48⟩
  · exact ⟨_, sign_sat_of hw hl (by decide) (by rw [e]; rfl) signSat_b64⟩
  · exact ⟨_, sign_sat_of hw hl (by decide) (by rw [e]; rfl) signSat_b28⟩
  · exact ⟨_, sign_sat_of hw hl (by decide) (by rw [e]; rfl) signSat_b32⟩

end VG.Proof.RsaPss.X86_64
