module

public import VerifiedGarbage.Proof.RsaPss.X86.SgVerified
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSASSA-PSS signing on x86: the contract is satisfiable

A state that meets `signTableContract` (`sign_sat`), with the hash
function's table that of any variant `w` of `vs` and MGF1's that of any
variant `wg` of `gs`: a modulus of 64 bytes, `e`, `p`, `q`, `dP`, `dQ` and
`qInv` of one byte, an empty salt, the working space it needs, the
arguments above `esp = 0x20000`, and the tables at `0x300000` and
`0x300100` (`withTabs`), written a word at a time (`putWs`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Sg

open VG
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes)
open VG.Proof.MdHashTable.X86 (MVar)
open VG.Proof.HashTable.X86 (TVar)
open VG.Proof.HashTable (symsOf32 symsOf32_distinct2 readW_sep32)

/-- The 32-bit words `ws` written from `p` on. -/
def putWs (m : Mem) (p : Addr) : List (BitVec 32) → Mem
  | [] => m
  | w :: ws => putWs (m.writeW p w) (p + 4) ws

theorem putWs_below {a : Addr} : ∀ {ws : List (BitVec 32)} {m : Mem} {p : Addr},
    a.toNat + 4 ≤ p.toNat → p.toNat + 4 * ws.length < 2 ^ 64 → (putWs m p ws).readW a 32 = m.readW a 32
  | [], _, _, _, _ => rfl
  | w :: ws, m, p, ha, hp => by
    have e : (p + 4).toNat = p.toNat + 4 := by
      rw [BitVec.toNat_add]; simp only [List.length_cons] at hp; simp; omega
    simp only [putWs]
    rw [putWs_below (by rw [e]; omega) (by rw [e]; simp only [List.length_cons] at hp; omega),
      readW_sep32 (.inl ha) (by simp only [List.length_cons] at hp; omega) (by simp only [List.length_cons] at hp; omega)]

theorem putWs_at : ∀ {ws : List (BitVec 32)} {m : Mem} {p : Addr} {i : Nat}, i < ws.length →
    p.toNat + 4 * ws.length < 2 ^ 64 → (putWs m p ws).readW (p + BitVec.ofNat 64 (4 * i)) 32 = ws.getD i 0
  | [], _, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | w :: ws, m, p, i, hi, hp => by
    have e : (p + 4).toNat = p.toNat + 4 := by
      rw [BitVec.toNat_add]; simp only [List.length_cons] at hp; simp; omega
    simp only [putWs, List.length_cons] at hi hp ⊢
    rcases i with _ | k
    · rw [show p + BitVec.ofNat 64 (4 * 0) = p by simp, putWs_below (by rw [e]) (by rw [e]; omega),
        Mem.readW_writeW_self32]; rfl
    · rw [show p + BitVec.ofNat 64 (4 * (k + 1)) = p + 4 + BitVec.ofNat 64 (4 * k) by
          rw [BitVec.add_assoc, show (4 : Addr) = BitVec.ofNat 64 4 from rfl, BitVec.ofNat_add_ofNat]; congr 2; omega,
        putWs_at (by omega) (by rw [e]; omega)]
      rfl

/-- The table of the words `ws`, written at `p`. -/
theorem putWs_held {m : Mem} {p : Addr} {ws : List (BitVec 64)} (hp : p.toNat + 4 * ws.length < 2 ^ 64) :
    Abi.tableHeld 32 (putWs m p (ws.map (·.setWidth 32))) p ws := by
  intro i hi
  rw [show (32 / 8 * i) = 4 * i from rfl, putWs_at (by simpa using hi) (by simpa using hp)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ws[i]? <;> rfl

/-- The state, but for the tables, for a digest of `D` bytes. -/
def satState (D : Nat) : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 131144 then BitVec.ofNat 8 D else if a = 131077 then 0x10 else if a = 131080 then 0x40 else if a = 131085 then 0x20 else if a = 131088 then 0x40 else if a = 131093 then 0x21 else if a = 131096 then 0x1 else if a = 131101 then 0x31 else if a = 131104 then 0x1 else if a = 131109 then 0x32 else if a = 131112 then 0x1 else if a = 131117 then 0x33 else if a = 131120 then 0x1 else if a = 131125 then 0x34 else if a = 131128 then 0x1 else if a = 131133 then 0x35 else if a = 131136 then 0x1 else if a = 131141 then 0x30 else if a = 131149 then 0x36 else if a = 131158 then 0x1 else if a = 131160 then 0x20 else if a = 131161 then 0x8 else if a = 131166 then 0x30 else if a = 131169 then 0x1 else if a = 131170 then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x3300, 1⟩, ⟨0x3400, 1⟩, ⟨0x3500, 1⟩,
    ⟨0x3000, D⟩, ⟨0x3600, 0⟩, ⟨0x300000, 44⟩, ⟨0x300100, 20⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x10000, 2080 * 8⟩, ⟨0x20004, 96⟩]

/-- `s` with the table of `w` at `0x300000`, that of `wg` at `0x300100`,
and the functions of `vs` and `gs` at distinct addresses. -/
def withTabs (s : State) (vs : List MVar) (gs : List TVar) (w : MVar) (wg : TVar) : State :=
  let s' : State := { s with syms := symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) }
  { s' with
    mem := putWs (putWs s.mem 0x300000 ((FnTable.words isa s' (Proof.MdHashTable.X86.tableOf w)).map
      (·.setWidth 32))) 0x300100 ((FnTable.words isa s' (Proof.HashTable.X86.tableOf wg)).map (·.setWidth 32)) }

theorem withTabs_mem (s : State) (vs : List MVar) (gs : List TVar) (w : MVar) (wg : TVar) {a : Addr}
    (ha : a.toNat + 4 ≤ 0x300000) : (withTabs s vs gs w wg).mem.readW a 32 = s.mem.readW a 32 := by
  simp only [withTabs]
  rw [putWs_below (by simp; omega) (by simp [FnTable.words, Proof.HashTable.X86.tableOf, Spec.HashTable.dataOf]),
    putWs_below (by simp; omega) (by simp [FnTable.words, Proof.MdHashTable.X86.tableOf, Spec.MdHashTable.dataOf,
      Spec.HashTable.dataOf])]

theorem withTabs_arg (s : State) (vs : List MVar) (gs : List TVar) (w : MVar) (wg : TVar) {j : Nat}
    (hj : (VG.X86.argAddr s j).toNat + 4 ≤ 0x300000) : VG.X86.arg (withTabs s vs gs w wg) j = VG.X86.arg s j :=
  withTabs_mem s vs gs w wg hj

theorem withTabs_heldH (s : State) (vs : List MVar) (gs : List TVar) (w : MVar) (wg : TVar) :
    Abi.tableHeld 32 (withTabs s vs gs w wg).mem ((0x300000 : BitVec 32).setWidth 64)
      (FnTable.words isa (withTabs s vs gs w wg) (Proof.MdHashTable.X86.tableOf w)) := by
  rw [show ((0x300000 : BitVec 32).setWidth 64) = 0x300000 by decide]
  intro i hi
  have hl : (FnTable.words isa (withTabs s vs gs w wg) (Proof.MdHashTable.X86.tableOf w)).length = 11 := by
    simp [FnTable.words, Proof.MdHashTable.X86.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf]
  rw [hl] at hi
  simp only [withTabs]
  rw [putWs_below (by rw [show (32 / 8 * i) = 4 * i from rfl]; simp; omega)
    (by simp [FnTable.words, Proof.HashTable.X86.tableOf, Spec.HashTable.dataOf])]
  exact putWs_held (by simp [FnTable.words, Proof.MdHashTable.X86.tableOf, Spec.MdHashTable.dataOf,
    Spec.HashTable.dataOf]) i (lt_of_lt_of_eq hi (by simp [FnTable.words, Proof.MdHashTable.X86.tableOf,
      Spec.MdHashTable.dataOf, Spec.HashTable.dataOf]))

theorem withTabs_held (s : State) (vs : List MVar) (gs : List TVar) (w : MVar) (wg : TVar) :
    Abi.tableHeld 32 (withTabs s vs gs w wg).mem ((0x300100 : BitVec 32).setWidth 64)
      (FnTable.words isa (withTabs s vs gs w wg) (Proof.HashTable.X86.tableOf wg)) := by
  rw [show ((0x300100 : BitVec 32).setWidth 64) = 0x300100 by decide]
  exact putWs_held (by simp [FnTable.words, Proof.HashTable.X86.tableOf, Spec.HashTable.dataOf])

/-- The digest lengths of the hash functions with the sizes of an index. -/
theorem D_mem {w : MVar} (hs : Proof.MdHashTable.X86.Shape w) : w.h.D ∈ [16, 20, 28, 32, 48, 64] := by
  obtain ⟨hi, hz⟩ := hs
  have hD : w.h.D = (Impl.RsaPss.X86.sizesOf (Proof.MdHashTable.X86.idx w)).2.2.2.1 := by
    rw [← hz]; rfl
  rw [hD]
  simp only [Impl.RsaPss.X86.idxs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with e | e | e | e | e | e | e | e <;> rw [e] <;> decide

theorem sign_sat16 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 16) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (sspec vs gs).pre s := by
  have hA : ∀ j < 24, (argAddr (satState 16) j).toNat + 4 ≤ 0x300000 := by decide
  have hhH := withTabs_heldH (satState 16) vs gs w wg
  have hhG := withTabs_held (satState 16) vs gs w wg
  have hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  refine ⟨withTabs (satState 16) vs gs w wg, ?_⟩
  have a0 : arg (withTabs (satState 16) vs gs w wg) 0 = 0x1000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  have a1 : arg (withTabs (satState 16) vs gs w wg) 1 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  have a2 : arg (withTabs (satState 16) vs gs w wg) 2 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  have a3 : arg (withTabs (satState 16) vs gs w wg) 3 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  have a4 : arg (withTabs (satState 16) vs gs w wg) 4 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  have a5 : arg (withTabs (satState 16) vs gs w wg) 5 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  have a6 : arg (withTabs (satState 16) vs gs w wg) 6 = 0x3100 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  have a7 : arg (withTabs (satState 16) vs gs w wg) 7 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  have a8 : arg (withTabs (satState 16) vs gs w wg) 8 = 0x3200 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  have a9 : arg (withTabs (satState 16) vs gs w wg) 9 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  have a10 : arg (withTabs (satState 16) vs gs w wg) 10 = 0x3300 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  have a11 : arg (withTabs (satState 16) vs gs w wg) 11 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  have a12 : arg (withTabs (satState 16) vs gs w wg) 12 = 0x3400 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  have a13 : arg (withTabs (satState 16) vs gs w wg) 13 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  have a14 : arg (withTabs (satState 16) vs gs w wg) 14 = 0x3500 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  have a15 : arg (withTabs (satState 16) vs gs w wg) 15 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  have a16 : arg (withTabs (satState 16) vs gs w wg) 16 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 16 (by decide))]; decide
  have a17 : arg (withTabs (satState 16) vs gs w wg) 17 = 0x10 := by rw [withTabs_arg _ vs gs w wg (hA 17 (by decide))]; decide
  have a18 : arg (withTabs (satState 16) vs gs w wg) 18 = 0x3600 := by rw [withTabs_arg _ vs gs w wg (hA 18 (by decide))]; decide
  have a19 : arg (withTabs (satState 16) vs gs w wg) 19 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 19 (by decide))]; decide
  have a20 : arg (withTabs (satState 16) vs gs w wg) 20 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 20 (by decide))]; decide
  have a21 : arg (withTabs (satState 16) vs gs w wg) 21 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 21 (by decide))]; decide
  have a22 : arg (withTabs (satState 16) vs gs w wg) 22 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 22 (by decide))]; decide
  have a23 : arg (withTabs (satState 16) vs gs w wg) 23 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 23 (by decide))]; decide
  have e : argAddr (withTabs (satState 16) vs gs w wg) 0 = 0x20004 := show argAddr (satState 16) 0 = _ by decide
  have esp : (withTabs (satState 16) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (satState 16) vs gs w wg).rd = (satState 16).rd := rfl
  have wr : (withTabs (satState 16) vs gs w wg).wr = (satState 16).wr := rfl
  have sy : (withTabs (satState 16) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (satState 16) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
    Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes,
    stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, e, esp, rd, wr, sy, satState]
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
    Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes,
    stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem sign_sat20 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 20) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (sspec vs gs).pre s := by
  have hA : ∀ j < 24, (argAddr (satState 20) j).toNat + 4 ≤ 0x300000 := by decide
  have hhH := withTabs_heldH (satState 20) vs gs w wg
  have hhG := withTabs_held (satState 20) vs gs w wg
  have hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  refine ⟨withTabs (satState 20) vs gs w wg, ?_⟩
  have a0 : arg (withTabs (satState 20) vs gs w wg) 0 = 0x1000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  have a1 : arg (withTabs (satState 20) vs gs w wg) 1 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  have a2 : arg (withTabs (satState 20) vs gs w wg) 2 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  have a3 : arg (withTabs (satState 20) vs gs w wg) 3 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  have a4 : arg (withTabs (satState 20) vs gs w wg) 4 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  have a5 : arg (withTabs (satState 20) vs gs w wg) 5 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  have a6 : arg (withTabs (satState 20) vs gs w wg) 6 = 0x3100 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  have a7 : arg (withTabs (satState 20) vs gs w wg) 7 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  have a8 : arg (withTabs (satState 20) vs gs w wg) 8 = 0x3200 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  have a9 : arg (withTabs (satState 20) vs gs w wg) 9 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  have a10 : arg (withTabs (satState 20) vs gs w wg) 10 = 0x3300 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  have a11 : arg (withTabs (satState 20) vs gs w wg) 11 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  have a12 : arg (withTabs (satState 20) vs gs w wg) 12 = 0x3400 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  have a13 : arg (withTabs (satState 20) vs gs w wg) 13 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  have a14 : arg (withTabs (satState 20) vs gs w wg) 14 = 0x3500 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  have a15 : arg (withTabs (satState 20) vs gs w wg) 15 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  have a16 : arg (withTabs (satState 20) vs gs w wg) 16 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 16 (by decide))]; decide
  have a17 : arg (withTabs (satState 20) vs gs w wg) 17 = 0x14 := by rw [withTabs_arg _ vs gs w wg (hA 17 (by decide))]; decide
  have a18 : arg (withTabs (satState 20) vs gs w wg) 18 = 0x3600 := by rw [withTabs_arg _ vs gs w wg (hA 18 (by decide))]; decide
  have a19 : arg (withTabs (satState 20) vs gs w wg) 19 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 19 (by decide))]; decide
  have a20 : arg (withTabs (satState 20) vs gs w wg) 20 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 20 (by decide))]; decide
  have a21 : arg (withTabs (satState 20) vs gs w wg) 21 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 21 (by decide))]; decide
  have a22 : arg (withTabs (satState 20) vs gs w wg) 22 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 22 (by decide))]; decide
  have a23 : arg (withTabs (satState 20) vs gs w wg) 23 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 23 (by decide))]; decide
  have e : argAddr (withTabs (satState 20) vs gs w wg) 0 = 0x20004 := show argAddr (satState 20) 0 = _ by decide
  have esp : (withTabs (satState 20) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (satState 20) vs gs w wg).rd = (satState 20).rd := rfl
  have wr : (withTabs (satState 20) vs gs w wg).wr = (satState 20).wr := rfl
  have sy : (withTabs (satState 20) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (satState 20) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
    Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes,
    stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, e, esp, rd, wr, sy, satState]
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
    Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes,
    stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem sign_sat28 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 28) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (sspec vs gs).pre s := by
  have hA : ∀ j < 24, (argAddr (satState 28) j).toNat + 4 ≤ 0x300000 := by decide
  have hhH := withTabs_heldH (satState 28) vs gs w wg
  have hhG := withTabs_held (satState 28) vs gs w wg
  have hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  refine ⟨withTabs (satState 28) vs gs w wg, ?_⟩
  have a0 : arg (withTabs (satState 28) vs gs w wg) 0 = 0x1000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  have a1 : arg (withTabs (satState 28) vs gs w wg) 1 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  have a2 : arg (withTabs (satState 28) vs gs w wg) 2 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  have a3 : arg (withTabs (satState 28) vs gs w wg) 3 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  have a4 : arg (withTabs (satState 28) vs gs w wg) 4 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  have a5 : arg (withTabs (satState 28) vs gs w wg) 5 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  have a6 : arg (withTabs (satState 28) vs gs w wg) 6 = 0x3100 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  have a7 : arg (withTabs (satState 28) vs gs w wg) 7 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  have a8 : arg (withTabs (satState 28) vs gs w wg) 8 = 0x3200 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  have a9 : arg (withTabs (satState 28) vs gs w wg) 9 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  have a10 : arg (withTabs (satState 28) vs gs w wg) 10 = 0x3300 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  have a11 : arg (withTabs (satState 28) vs gs w wg) 11 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  have a12 : arg (withTabs (satState 28) vs gs w wg) 12 = 0x3400 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  have a13 : arg (withTabs (satState 28) vs gs w wg) 13 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  have a14 : arg (withTabs (satState 28) vs gs w wg) 14 = 0x3500 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  have a15 : arg (withTabs (satState 28) vs gs w wg) 15 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  have a16 : arg (withTabs (satState 28) vs gs w wg) 16 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 16 (by decide))]; decide
  have a17 : arg (withTabs (satState 28) vs gs w wg) 17 = 0x1c := by rw [withTabs_arg _ vs gs w wg (hA 17 (by decide))]; decide
  have a18 : arg (withTabs (satState 28) vs gs w wg) 18 = 0x3600 := by rw [withTabs_arg _ vs gs w wg (hA 18 (by decide))]; decide
  have a19 : arg (withTabs (satState 28) vs gs w wg) 19 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 19 (by decide))]; decide
  have a20 : arg (withTabs (satState 28) vs gs w wg) 20 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 20 (by decide))]; decide
  have a21 : arg (withTabs (satState 28) vs gs w wg) 21 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 21 (by decide))]; decide
  have a22 : arg (withTabs (satState 28) vs gs w wg) 22 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 22 (by decide))]; decide
  have a23 : arg (withTabs (satState 28) vs gs w wg) 23 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 23 (by decide))]; decide
  have e : argAddr (withTabs (satState 28) vs gs w wg) 0 = 0x20004 := show argAddr (satState 28) 0 = _ by decide
  have esp : (withTabs (satState 28) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (satState 28) vs gs w wg).rd = (satState 28).rd := rfl
  have wr : (withTabs (satState 28) vs gs w wg).wr = (satState 28).wr := rfl
  have sy : (withTabs (satState 28) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (satState 28) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
    Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes,
    stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, e, esp, rd, wr, sy, satState]
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
    Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes,
    stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem sign_sat32 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 32) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (sspec vs gs).pre s := by
  have hA : ∀ j < 24, (argAddr (satState 32) j).toNat + 4 ≤ 0x300000 := by decide
  have hhH := withTabs_heldH (satState 32) vs gs w wg
  have hhG := withTabs_held (satState 32) vs gs w wg
  have hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  refine ⟨withTabs (satState 32) vs gs w wg, ?_⟩
  have a0 : arg (withTabs (satState 32) vs gs w wg) 0 = 0x1000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  have a1 : arg (withTabs (satState 32) vs gs w wg) 1 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  have a2 : arg (withTabs (satState 32) vs gs w wg) 2 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  have a3 : arg (withTabs (satState 32) vs gs w wg) 3 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  have a4 : arg (withTabs (satState 32) vs gs w wg) 4 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  have a5 : arg (withTabs (satState 32) vs gs w wg) 5 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  have a6 : arg (withTabs (satState 32) vs gs w wg) 6 = 0x3100 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  have a7 : arg (withTabs (satState 32) vs gs w wg) 7 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  have a8 : arg (withTabs (satState 32) vs gs w wg) 8 = 0x3200 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  have a9 : arg (withTabs (satState 32) vs gs w wg) 9 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  have a10 : arg (withTabs (satState 32) vs gs w wg) 10 = 0x3300 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  have a11 : arg (withTabs (satState 32) vs gs w wg) 11 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  have a12 : arg (withTabs (satState 32) vs gs w wg) 12 = 0x3400 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  have a13 : arg (withTabs (satState 32) vs gs w wg) 13 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  have a14 : arg (withTabs (satState 32) vs gs w wg) 14 = 0x3500 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  have a15 : arg (withTabs (satState 32) vs gs w wg) 15 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  have a16 : arg (withTabs (satState 32) vs gs w wg) 16 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 16 (by decide))]; decide
  have a17 : arg (withTabs (satState 32) vs gs w wg) 17 = 0x20 := by rw [withTabs_arg _ vs gs w wg (hA 17 (by decide))]; decide
  have a18 : arg (withTabs (satState 32) vs gs w wg) 18 = 0x3600 := by rw [withTabs_arg _ vs gs w wg (hA 18 (by decide))]; decide
  have a19 : arg (withTabs (satState 32) vs gs w wg) 19 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 19 (by decide))]; decide
  have a20 : arg (withTabs (satState 32) vs gs w wg) 20 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 20 (by decide))]; decide
  have a21 : arg (withTabs (satState 32) vs gs w wg) 21 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 21 (by decide))]; decide
  have a22 : arg (withTabs (satState 32) vs gs w wg) 22 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 22 (by decide))]; decide
  have a23 : arg (withTabs (satState 32) vs gs w wg) 23 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 23 (by decide))]; decide
  have e : argAddr (withTabs (satState 32) vs gs w wg) 0 = 0x20004 := show argAddr (satState 32) 0 = _ by decide
  have esp : (withTabs (satState 32) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (satState 32) vs gs w wg).rd = (satState 32).rd := rfl
  have wr : (withTabs (satState 32) vs gs w wg).wr = (satState 32).wr := rfl
  have sy : (withTabs (satState 32) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (satState 32) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
    Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes,
    stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, e, esp, rd, wr, sy, satState]
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
    Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes,
    stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem sign_sat48 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 48) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (sspec vs gs).pre s := by
  have hA : ∀ j < 24, (argAddr (satState 48) j).toNat + 4 ≤ 0x300000 := by decide
  have hhH := withTabs_heldH (satState 48) vs gs w wg
  have hhG := withTabs_held (satState 48) vs gs w wg
  have hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  refine ⟨withTabs (satState 48) vs gs w wg, ?_⟩
  have a0 : arg (withTabs (satState 48) vs gs w wg) 0 = 0x1000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  have a1 : arg (withTabs (satState 48) vs gs w wg) 1 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  have a2 : arg (withTabs (satState 48) vs gs w wg) 2 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  have a3 : arg (withTabs (satState 48) vs gs w wg) 3 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  have a4 : arg (withTabs (satState 48) vs gs w wg) 4 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  have a5 : arg (withTabs (satState 48) vs gs w wg) 5 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  have a6 : arg (withTabs (satState 48) vs gs w wg) 6 = 0x3100 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  have a7 : arg (withTabs (satState 48) vs gs w wg) 7 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  have a8 : arg (withTabs (satState 48) vs gs w wg) 8 = 0x3200 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  have a9 : arg (withTabs (satState 48) vs gs w wg) 9 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  have a10 : arg (withTabs (satState 48) vs gs w wg) 10 = 0x3300 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  have a11 : arg (withTabs (satState 48) vs gs w wg) 11 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  have a12 : arg (withTabs (satState 48) vs gs w wg) 12 = 0x3400 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  have a13 : arg (withTabs (satState 48) vs gs w wg) 13 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  have a14 : arg (withTabs (satState 48) vs gs w wg) 14 = 0x3500 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  have a15 : arg (withTabs (satState 48) vs gs w wg) 15 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  have a16 : arg (withTabs (satState 48) vs gs w wg) 16 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 16 (by decide))]; decide
  have a17 : arg (withTabs (satState 48) vs gs w wg) 17 = 0x30 := by rw [withTabs_arg _ vs gs w wg (hA 17 (by decide))]; decide
  have a18 : arg (withTabs (satState 48) vs gs w wg) 18 = 0x3600 := by rw [withTabs_arg _ vs gs w wg (hA 18 (by decide))]; decide
  have a19 : arg (withTabs (satState 48) vs gs w wg) 19 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 19 (by decide))]; decide
  have a20 : arg (withTabs (satState 48) vs gs w wg) 20 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 20 (by decide))]; decide
  have a21 : arg (withTabs (satState 48) vs gs w wg) 21 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 21 (by decide))]; decide
  have a22 : arg (withTabs (satState 48) vs gs w wg) 22 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 22 (by decide))]; decide
  have a23 : arg (withTabs (satState 48) vs gs w wg) 23 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 23 (by decide))]; decide
  have e : argAddr (withTabs (satState 48) vs gs w wg) 0 = 0x20004 := show argAddr (satState 48) 0 = _ by decide
  have esp : (withTabs (satState 48) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (satState 48) vs gs w wg).rd = (satState 48).rd := rfl
  have wr : (withTabs (satState 48) vs gs w wg).wr = (satState 48).wr := rfl
  have sy : (withTabs (satState 48) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (satState 48) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
    Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes,
    stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, e, esp, rd, wr, sy, satState]
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
    Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes,
    stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem sign_sat64 {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hD : w.h.D = 64) (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (sspec vs gs).pre s := by
  have hA : ∀ j < 24, (argAddr (satState 64) j).toNat + 4 ≤ 0x300000 := by decide
  have hhH := withTabs_heldH (satState 64) vs gs w wg
  have hhG := withTabs_held (satState 64) vs gs w wg
  have hH := Proof.MdHashTable.X86.hashAt_tableOf (by decide) (Proof.MdHashTable.X86.held_tableOf (by decide) hhH).2.2.2
  refine ⟨withTabs (satState 64) vs gs w wg, ?_⟩
  have a0 : arg (withTabs (satState 64) vs gs w wg) 0 = 0x1000 := by rw [withTabs_arg _ vs gs w wg (hA 0 (by decide))]; decide
  have a1 : arg (withTabs (satState 64) vs gs w wg) 1 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 1 (by decide))]; decide
  have a2 : arg (withTabs (satState 64) vs gs w wg) 2 = 0x2000 := by rw [withTabs_arg _ vs gs w wg (hA 2 (by decide))]; decide
  have a3 : arg (withTabs (satState 64) vs gs w wg) 3 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 3 (by decide))]; decide
  have a4 : arg (withTabs (satState 64) vs gs w wg) 4 = 0x2100 := by rw [withTabs_arg _ vs gs w wg (hA 4 (by decide))]; decide
  have a5 : arg (withTabs (satState 64) vs gs w wg) 5 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 5 (by decide))]; decide
  have a6 : arg (withTabs (satState 64) vs gs w wg) 6 = 0x3100 := by rw [withTabs_arg _ vs gs w wg (hA 6 (by decide))]; decide
  have a7 : arg (withTabs (satState 64) vs gs w wg) 7 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 7 (by decide))]; decide
  have a8 : arg (withTabs (satState 64) vs gs w wg) 8 = 0x3200 := by rw [withTabs_arg _ vs gs w wg (hA 8 (by decide))]; decide
  have a9 : arg (withTabs (satState 64) vs gs w wg) 9 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 9 (by decide))]; decide
  have a10 : arg (withTabs (satState 64) vs gs w wg) 10 = 0x3300 := by rw [withTabs_arg _ vs gs w wg (hA 10 (by decide))]; decide
  have a11 : arg (withTabs (satState 64) vs gs w wg) 11 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 11 (by decide))]; decide
  have a12 : arg (withTabs (satState 64) vs gs w wg) 12 = 0x3400 := by rw [withTabs_arg _ vs gs w wg (hA 12 (by decide))]; decide
  have a13 : arg (withTabs (satState 64) vs gs w wg) 13 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 13 (by decide))]; decide
  have a14 : arg (withTabs (satState 64) vs gs w wg) 14 = 0x3500 := by rw [withTabs_arg _ vs gs w wg (hA 14 (by decide))]; decide
  have a15 : arg (withTabs (satState 64) vs gs w wg) 15 = 1 := by rw [withTabs_arg _ vs gs w wg (hA 15 (by decide))]; decide
  have a16 : arg (withTabs (satState 64) vs gs w wg) 16 = 0x3000 := by rw [withTabs_arg _ vs gs w wg (hA 16 (by decide))]; decide
  have a17 : arg (withTabs (satState 64) vs gs w wg) 17 = 0x40 := by rw [withTabs_arg _ vs gs w wg (hA 17 (by decide))]; decide
  have a18 : arg (withTabs (satState 64) vs gs w wg) 18 = 0x3600 := by rw [withTabs_arg _ vs gs w wg (hA 18 (by decide))]; decide
  have a19 : arg (withTabs (satState 64) vs gs w wg) 19 = 0 := by rw [withTabs_arg _ vs gs w wg (hA 19 (by decide))]; decide
  have a20 : arg (withTabs (satState 64) vs gs w wg) 20 = 0x10000 := by rw [withTabs_arg _ vs gs w wg (hA 20 (by decide))]; decide
  have a21 : arg (withTabs (satState 64) vs gs w wg) 21 = 0x820 := by rw [withTabs_arg _ vs gs w wg (hA 21 (by decide))]; decide
  have a22 : arg (withTabs (satState 64) vs gs w wg) 22 = 0x300000 := by rw [withTabs_arg _ vs gs w wg (hA 22 (by decide))]; decide
  have a23 : arg (withTabs (satState 64) vs gs w wg) 23 = 0x300100 := by rw [withTabs_arg _ vs gs w wg (hA 23 (by decide))]; decide
  have e : argAddr (withTabs (satState 64) vs gs w wg) 0 = 0x20004 := show argAddr (satState 64) 0 = _ by decide
  have esp : (withTabs (satState 64) vs gs w wg).gpr .esp = 0x20000 := rfl
  have rd : (withTabs (satState 64) vs gs w wg).rd = (satState 64).rd := rfl
  have wr : (withTabs (satState 64) vs gs w wg).wr = (satState 64).wr := rfl
  have sy : (withTabs (satState 64) vs gs w wg).syms =
      symsOf32 (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs) := rfl
  generalize withTabs (satState 64) vs gs w wg = S at *
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
    Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes,
    stackBelow]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, e, esp, rd, wr, sy, satState]
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
    Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes,
    stackBelow]
  sig_and_intros
  all_goals try (exact Region.disjoint_of_sep (by decide))
  all_goals try (simp only [Spec.Rsa.lenValid]; decide)
  all_goals try decide
  · exact ⟨Proof.MdHashTable.X86.tableOf w, List.mem_map_of_mem hw, hhH⟩
  · exact ⟨Proof.HashTable.X86.tableOf wg, List.mem_map_of_mem hwg, hhG⟩
  · rw [List.append_eq, List.append_eq, List.append_nil]; exact (symsOf32_distinct2 hl).sublist (List.sublist_append_left _ _)
  · intro H hH'; rw [hH, Option.some.injEq] at hH'; subst hH'; rw [w.h.glen]; show _ = w.h.D; rw [hD]; rfl

theorem sign_sat {vs : List MVar} {gs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hs : Proof.MdHashTable.X86.Shape w)
    (hl : (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24) :
    ∃ s, (sspec vs gs).pre s := by
  have hDm := D_mem hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hDm
  rcases hDm with e | e | e | e | e | e
  exacts [sign_sat16 hw hwg e hl, sign_sat20 hw hwg e hl, sign_sat28 hw hwg e hl, sign_sat32 hw hwg e hl,
    sign_sat48 hw hwg e hl, sign_sat64 hw hwg e hl]

end VG.Proof.RsaPss.X86.Sg
