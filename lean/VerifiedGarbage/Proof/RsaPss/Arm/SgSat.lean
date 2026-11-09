module

public import VerifiedGarbage.Proof.RsaPss.Arm.SgBase
public import VerifiedGarbage.Proof.MdHashTable.Arm.Tables
public import VerifiedGarbage.Proof.HashTable.Arm
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSASSA-PSS signing on ARMv7 with the tables: the contract is satisfiable

A state with the table of `MdHash` of `w` at `0x300000` and the table of
`Hash` of `wg` at `0x300100` (`withTabs`, the stack arguments' values), and
the tables' functions at distinct addresses (`symsOf32`), and the arguments
of a 512-bit key, a digest of `w`'s length and an empty salt: `sign_sat`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm
open VG.Proof.HashTable (symsOf32 symsOf32_distinct readW_sep32)
open VG.Proof.HashTable.Arm (TVar)
open VG.Proof.MdHashTable.Arm (MVar)

/-- The words `ws` written from `p`, 32 bits each. -/
def putWs (m : Mem) (p : Addr) : List (BitVec 64) → Mem
  | [] => m
  | w :: ws => putWs (m.writeW p (w.setWidth 32)) (p + 4) ws

theorem add4_toNat {p : Addr} (h : p.toNat + 4 < 2 ^ 64) : (p + 4).toNat = p.toNat + 4 := by
  rw [BitVec.toNat_add, show (4 : Addr).toNat = 4 from rfl, Nat.mod_eq_of_lt h]

/-- A word apart from the words `putWs` writes. -/
theorem putWs_out {m : Mem} {a : Addr} : ∀ {p : Addr} {ws : List (BitVec 64)},
    (a.toNat + 4 ≤ p.toNat ∨ p.toNat + 4 * ws.length ≤ a.toNat) → p.toNat + 4 * ws.length < 2 ^ 64 →
    a.toNat + 4 ≤ 2 ^ 64 → (putWs m p ws).readW a 32 = m.readW a 32
  | _, [], _, _, _ => rfl
  | p, w :: ws, h, hp, ha => by
    simp only [List.length_cons] at h hp
    have h4 := add4_toNat (p := p) (by omega)
    simp only [putWs]
    rw [putWs_out (by rw [h4]; omega) (by rw [h4]; omega) ha, readW_sep32 (by omega) ha (by omega)]

/-- The words `putWs` writes. -/
theorem putWs_held {m : Mem} : ∀ {p : Addr} {ws : List (BitVec 64)}, p.toNat + 4 * ws.length < 2 ^ 64 →
    Abi.tableHeld 32 (putWs m p ws) p ws
  | _, [], _ => fun i hi => absurd hi (Nat.not_lt_zero _)
  | p, w :: ws, hp => by
    simp only [List.length_cons] at hp
    have h4 := add4_toNat (p := p) (by omega)
    intro i hi
    simp only [putWs]
    cases i with
    | zero =>
      rw [show p + BitVec.ofNat 64 (32 / 8 * 0) = p from BitVec.add_zero p,
        putWs_out (.inl (by rw [h4])) (by rw [h4]; omega) (by omega), Mem.readW_writeW_self32]
      simp
    | succ i =>
      have := putWs_held (m := m.writeW p (w.setWidth 32)) (p := p + 4) (ws := ws) (by rw [h4]; omega) i
        (by simp at hi; omega)
      rw [show p + BitVec.ofNat 64 (32 / 8 * (i + 1)) = p + 4 + BitVec.ofNat 64 (32 / 8 * i) by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega]
      simpa using this

/-- The words of a table, its functions at the addresses `symsOf32 ns`. -/
def tw (ns : List String) (T : FnTable) : List (BitVec 64) := T.fns.map (fun n => (symsOf32 ns n).setWidth 64) ++ T.data

/-- The names of the tables' functions. -/
def allNames (mvs : List MVar) (vs : List TVar) : List String :=
  MdHashTable.Arm.names mvs ++ HashTable.Arm.names vs

/-- The memory `m` with the table of `MdHash` of `w` at `0x300000` and the
table of `Hash` of `wg` at `0x300100`, and `m` itself below `0x300000`. -/
def tabMem (m : Mem) (mvs : List MVar) (vs : List TVar) (w : MVar) (wg : TVar) : Mem := fun a =>
  bif Nat.blt a.toNat 0x300000 then m a
  else putWs (putWs m 0x300000 (tw (allNames mvs vs) (MdHashTable.Arm.tableOf w))) 0x300100
    (tw (allNames mvs vs) (HashTable.Arm.tableOf wg)) a

/-- A state with `s`'s registers and regions, those tables, and the tables'
functions at distinct addresses. -/
def withTabs (s : State) (mvs : List MVar) (vs : List TVar) (w : MVar) (wg : TVar) : State :=
  { s with mem := tabMem s.mem mvs vs w wg, syms := symsOf32 (allNames mvs vs) }

variable {mvs : List MVar} {vs : List TVar} {w : MVar} {wg : TVar}

/-- Below `0x300000`, a word as in `s`. -/
theorem withTabs_below (s : State) {a : Addr} (ha : a.toNat + 4 ≤ 0x300000) :
    (withTabs s mvs vs w wg).mem.readW a 32 = s.mem.readW a 32 := by
  refine Mem.readW_congr fun i hi => ?_
  have : (a + BitVec.ofNat 64 i).toNat < 0x300000 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  simp only [withTabs, tabMem, Nat.blt_eq.mpr this, Bool.cond_true]

/-- A stack argument below `0x300000`, as in `s`. -/
theorem withTabs_arg (s : State) {j : Nat} (hj : (stackArgAddr s j).toNat + 4 ≤ 0x300000) :
    stackArg (withTabs s mvs vs w wg) j = stackArg s j :=
  show (withTabs s mvs vs w wg).mem.readW (stackArgAddr s j) 32 = s.mem.readW (stackArgAddr s j) 32 from
    withTabs_below s hj

/-- Above `0x300000`, the tables' memory. -/
theorem tabMem_above {m : Mem} {p : Addr} {ws : List (BitVec 64)}
    (hp : 0x300000 ≤ p.toNat) (hl : p.toNat + 4 * ws.length < 2 ^ 64)
    (h : Abi.tableHeld 32 (putWs (putWs m 0x300000 (tw (allNames mvs vs) (MdHashTable.Arm.tableOf w))) 0x300100
      (tw (allNames mvs vs) (HashTable.Arm.tableOf wg))) p ws) :
    Abi.tableHeld 32 (tabMem m mvs vs w wg) p ws := by
  intro i hi
  rw [← h i hi]
  refine Mem.readW_congr fun k hk => ?_
  have : ¬ (p + BitVec.ofNat 64 (32 / 8 * i) + BitVec.ofNat 64 k).toNat < 0x300000 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hb : Nat.blt (p + BitVec.ofNat 64 (32 / 8 * i) + BitVec.ofNat 64 k).toNat 0x300000 = false := by
    rw [Bool.eq_false_iff]; intro hc; exact this (Nat.blt_eq.mp hc)
  simp only [tabMem, hb, Bool.cond_false]

theorem tw_words (s : State) (hs : s.syms = symsOf32 (allNames mvs vs)) (T : FnTable) :
    FnTable.words isa s T = tw (allNames mvs vs) T := by
  simp only [FnTable.words, tw, hs]

theorem withTabs_heldH (s : State) :
    Abi.tableHeld 32 (withTabs s mvs vs w wg).mem 0x300000
      (FnTable.words isa (withTabs s mvs vs w wg) (MdHashTable.Arm.tableOf w)) := by
  have hl : (tw (allNames mvs vs) (MdHashTable.Arm.tableOf w)).length = 11 := by
    simp [tw, MdHashTable.Arm.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf]
  have c1 : (0x300000 : Addr).toNat = 0x300000 := rfl
  have c2 : (0x300100 : Addr).toNat = 0x300100 := rfl
  rw [tw_words _ rfl]
  refine tabMem_above (by decide) (by rw [hl]; decide) fun i hi => ?_
  rw [hl] at hi
  rw [putWs_out (.inl (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat, c1, c2, Nat.reduceDiv]; omega))
    (by simp [tw, HashTable.Arm.tableOf, Spec.HashTable.dataOf])
    (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat, c1, Nat.reduceDiv]; omega)]
  exact putWs_held (by rw [hl]; decide) i (by rw [hl]; exact hi)

theorem withTabs_heldG (s : State) :
    Abi.tableHeld 32 (withTabs s mvs vs w wg).mem 0x300100
      (FnTable.words isa (withTabs s mvs vs w wg) (HashTable.Arm.tableOf wg)) := by
  rw [tw_words _ rfl]
  exact tabMem_above (by decide) (by simp [tw, HashTable.Arm.tableOf, Spec.HashTable.dataOf])
    (putWs_held (by simp [tw, HashTable.Arm.tableOf, Spec.HashTable.dataOf]))

namespace Sg

/-- A state meeting signing's precondition but for the tables: a 512-bit
modulus, one-byte `e`, primes, exponents and `qInv`, a digest of `D` bytes,
an empty salt, the stack arguments at `0x8000`, and the tables' addresses
`0x300000` and `0x300100`. -/
def satState (D : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x2000 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x21 else
    if a = 0x8004 then 1 else
    if a = 0x8009 then 0x31 else
    if a = 0x800c then 1 else
    if a = 0x8011 then 0x32 else
    if a = 0x8014 then 1 else
    if a = 0x8019 then 0x33 else
    if a = 0x801c then 1 else
    if a = 0x8021 then 0x34 else
    if a = 0x8024 then 1 else
    if a = 0x8029 then 0x35 else
    if a = 0x802c then 1 else
    if a = 0x8031 then 0x30 else
    if a = 0x8034 then BitVec.ofNat 8 D else
    if a = 0x8039 then 0x36 else
    if a = 0x8042 then 1 else
    if a = 0x8044 then 0x20 else
    if a = 0x8045 then 8 else
    if a = 0x804a then 0x30 else
    if a = 0x804d then 1 else
    if a = 0x804e then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x3300, 1⟩, ⟨0x3400, 1⟩, ⟨0x3500, 1⟩,
    ⟨0x3000, D⟩, ⟨0x3600, 0⟩, ⟨0x300000, 44⟩, ⟨0x300100, 20⟩, ⟨0x8000, 80⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x10000, 2080 * 8⟩]

/-- Its stack arguments. -/
def satArgs (D : Nat) : Nat → BitVec 32
  | 0 => 0x2100 | 1 => 1 | 2 => 0x3100 | 3 => 1 | 4 => 0x3200 | 5 => 1 | 6 => 0x3300 | 7 => 1
  | 8 => 0x3400 | 9 => 1 | 10 => 0x3500 | 11 => 1 | 12 => 0x3000 | 13 => BitVec.ofNat 32 D | 14 => 0x3600
  | 15 => 0 | 16 => 0x10000 | 17 => 0x820 | 18 => 0x300000 | _ => 0x300100

theorem sat_args (D : Nat) : ∀ j < 20, (stackArgAddr (satState D) j).toNat + 4 ≤ 0x300000 := by
  show ∀ j < 20, (stackArgAddr (satState 0) j).toNat + 4 ≤ 0x300000
  decide

/-- A region within `⟨p, 64⟩`, apart from what that is apart from. -/
theorem dig_disj {A : Region} {p : Addr} {D : Nat} (hD : D ≤ 64) (h : A.Disjoint ⟨p, 64⟩) : A.Disjoint ⟨p, D⟩ :=
  h.sub_right fun a ha => by simp only [Region.Contains] at ha ⊢; omega

theorem sat_b16 : ∀ j < 20, stackArg (satState 16) j = satArgs 16 j := by decide
theorem sat_b20 : ∀ j < 20, stackArg (satState 20) j = satArgs 20 j := by decide
theorem sat_b28 : ∀ j < 20, stackArg (satState 28) j = satArgs 28 j := by decide
theorem sat_b32 : ∀ j < 20, stackArg (satState 32) j = satArgs 32 j := by decide
theorem sat_b48 : ∀ j < 20, stackArg (satState 48) j = satArgs 48 j := by decide
theorem sat_b64 : ∀ j < 20, stackArg (satState 64) j = satArgs 64 j := by decide

/-- Signing's precondition, from the facts of a state. -/
theorem sign_pre_of {hs ts : List FnTable} {D : Nat} (hD : D ≤ 64) {s : State}
    (hg : s.gpr = (satState D).gpr) (hsp : s.sp = (satState D).sp) (ha : ∀ j < 20, stackArg s j = satArgs D j)
    (hrd : s.rd = (satState D).rd) (hwr : s.wr = (satState D).wr)
    (hH : ∃ T ∈ hs, Abi.tableHeld 32 s.mem 0x300000 (FnTable.words isa s T))
    (hG : ∃ T ∈ ts, Abi.tableHeld 32 s.mem 0x300100 (FnTable.words isa s T))
    (hsy : ((hs.map (fun T : FnTable => T.fns)).flatten ++ ((ts.map (fun T : FnTable => T.fns)).flatten ++ [])).Pairwise
      fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64)
    (hd : Spec.RsaPss.digestLenOk 32 s.mem 0x300000 (BitVec.ofNat 32 D)) :
    (spec hs ts).pre s := by
  have g0 : s.gpr .r0 = 0x1000 := by rw [hg]; rfl
  have g1 : s.gpr .r1 = 64 := by rw [hg]; rfl
  have g2 : s.gpr .r2 = 0x2000 := by rw [hg]; rfl
  have g3 : s.gpr .r3 = 64 := by rw [hg]; rfl
  have sp0 : s.sp = 0x8000 := hsp
  have e0 : stackArgAddr s 0 = 0x8000 := by simp only [stackArgAddr, sp0]; decide
  have hD' : (BitVec.ofNat 32 D).toNat = D := by rw [BitVec.toNat_ofNat]; omega
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
    Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs, reduceClassify,
    Loc.val]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide),
    ha 11 (by decide), ha 12 (by decide), ha 13 (by decide), ha 14 (by decide), ha 15 (by decide),
    ha 16 (by decide), ha 17 (by decide), ha 18 (by decide), ha 19 (by decide), g0, g1, g2, g3, e0, sp0, hrd, hwr,
    satArgs]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
    Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs, reduceClassify,
    Loc.val]
  sig_and_intros
  all_goals first
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
    | skip

theorem sign_sat_of {mvs : List MVar} {vs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ mvs) (hwg : wg ∈ vs)
    (hl : (allNames mvs vs).length < 2 ^ 24) {D : Nat} (hD : D ≤ 64) (hlen : w.h.G.len = D)
    (hb : ∀ j < 20, stackArg (satState D) j = satArgs D j) :
    (spec (MdHashTable.Arm.tables mvs) (HashTable.Arm.tables vs)).pre (withTabs (satState D) mvs vs w wg) :=
  sign_pre_of hD rfl rfl (fun j hj => (withTabs_arg _ (sat_args D j hj)).trans (hb j hj)) rfl rfl
    ⟨_, List.mem_map_of_mem hw, withTabs_heldH _⟩ ⟨_, List.mem_map_of_mem hwg, withTabs_heldG _⟩
    (by rw [List.append_nil]; exact symsOf32_distinct hl) fun H hH => by
      have e3 : State.addr (0x300000 : BitVec 32) = (0x300000 : Addr) := by decide
      have hheld := withTabs_heldH (satState D) (mvs := mvs) (vs := vs) (w := w) (wg := wg)
      rw [← e3] at hheld
      have hA := MdHashTable.Arm.hashAt_tableOf (p := 0x300000) (by decide)
        (MdHashTable.Arm.held_tableOf (by decide) hheld).2.2.2
      rw [e3] at hA
      rw [hA, Option.some.injEq] at hH
      subst hH
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hlen]

/-- Signing's contract, with the tables of `mvs` and `vs`, is satisfiable. -/
theorem sign_sat {mvs : List MVar} {vs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ mvs) (hwg : wg ∈ vs)
    (hl : (allNames mvs vs).length < 2 ^ 24) :
    ∃ s, (spec (MdHashTable.Arm.tables mvs) (HashTable.Arm.tables vs)).pre s := by
  have hG : w.h.G ∈ Spec.Mgf1.hashes := List.mem_of_getElem? w.idx
  have hlen : w.h.G.len = 16 ∨ w.h.G.len = 20 ∨ w.h.G.len = 28 ∨ w.h.G.len = 32 ∨ w.h.G.len = 48 ∨
      w.h.G.len = 64 := by
    simp only [Spec.Mgf1.hashes, List.mem_cons, List.not_mem_nil, or_false] at hG
    rcases hG with e | e | e | e | e | e | e | e | e | e | e | e | e | e <;> rw [e] <;> decide
  rcases hlen with e | e | e | e | e | e
  · exact ⟨_, sign_sat_of hw hwg hl (by decide) e sat_b16⟩
  · exact ⟨_, sign_sat_of hw hwg hl (by decide) e sat_b20⟩
  · exact ⟨_, sign_sat_of hw hwg hl (by decide) e sat_b28⟩
  · exact ⟨_, sign_sat_of hw hwg hl (by decide) e sat_b32⟩
  · exact ⟨_, sign_sat_of hw hwg hl (by decide) e sat_b48⟩
  · exact ⟨_, sign_sat_of hw hwg hl (by decide) e sat_b64⟩

end Sg

end VG.Proof.RsaPss.Arm
