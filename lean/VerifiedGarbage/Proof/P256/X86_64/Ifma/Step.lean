module

public import VerifiedGarbage.Proof.P256.X86_64.Ifma.Glue
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.P256.X86_64.Ifma.Stage

/-!
# P-256 on x86-64 with AVX512_IFMA: a stage's piece of code

`cut_step`: what a stage's piece of code does to what is known between the
stages. From bounds of what it starts from (`EnvOK`), the numbers (`vI`) of
the lanes of the field vectors in the places of its results are those of the
stage's terms in the state before, and are carried where those are; and the
bounds the next stage starts from hold (`bndsOf`), which are the bounds of
the terms (`T.iv`) but for the carried lanes `ovs`, known by their number.
-/

@[expose] public section

namespace VG.Proof.P256.X86_64.Ifma

/-!
## The bounds between the stages

For each stage of each block: the bounds of its terms' limbs (`…IV`), lane
by lane, from the bounds before it, which the kernel computes (`T.iv`,
`StageFacts.lean`); and the bounds its results are known to have (`…BT`), which are
those but for carried results, whose top limb's bounds are from their value
(`normI_lt`).
-/

section

/-!
## Between the stages of a block

Between two stages the values a block still needs are in the places `L`
(five for each field vector, `Code.lean`). What is known of them is said of
the integers of their limbs, lane by lane (`tab`), and passes from the
terms of a stage, in the state before its piece of code, to the places
after it (`stage_tab`), for the lanes whose terms have bounds within 64
signed bits (`ivWithin`, which the kernel evaluates).
-/

section

open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma
open VG.Proof.Bignum.X86_64.Ifma (qv)
open VG.Impl.Rsa.X86_64.CrtIfma (vreg)
open VG.Proof.Weierstrass (Unch)

/-- A field vector of no meaning. -/
def zero5 : F5 T := F5.rep (.lit 0 0 0 0)

/-- Limb `i` of lane `k` of field vector `j`, as an integer. -/
def tab (E : Env) (xs : List (F5 T)) (j i k : Nat) : Int := ((xs.getD j zero5).get i).int E k

/-- The field vectors in the places `L`, as terms of the state. -/
def leaves (L : List Loc) : List (F5 T) := group5 (L.map leafOf)

/-- Bounds for the limbs of each lane of each field vector, where known. -/
abbrev BT := List (List (Option (Int × Int)))

def BT.get (bt : BT) (j k : Nat) : Option (Int × Int) := (bt.getD j []).getD k none

/-- The bounds of the place numbered `n` of `L` in lane `k`, else those of any quadword. -/
def bndAt (bt : BT) (n : Option Nat) (k : Nat) : Int × Int :=
  match n with
  | some n => (bt.get (n / 5) k).getD (-2 ^ 63, 2 ^ 63 - 1)
  | none => (-2 ^ 63, 2 ^ 63 - 1)

/-- The number of the first place of `L` that is `l`. -/
def locIdx (L : List Loc) (l : Loc) : Option Nat :=
  let n := L.idxOf l
  if n < L.length then some n else none

/-- The slot at an offset of the working space, if it is one. -/
def slotAt (d : Nat) : Option Nat :=
  if cfg.sbase ≤ d ∧ (d - cfg.sbase) % 32 = 0 then some ((d - cfg.sbase) / 32) else none

/-- The bounds of what a piece starts from, by the places `L` and their bounds `bt`. -/
def bndsOf (L : List Loc) (bt : BT) : Bnds where
  vl r k := (bndAt bt (locIdx L (.reg r)) k).1
  vh r k := (bndAt bt (locIdx L (.reg r)) k).2
  ml b d k := if uBase b then 0
    else (bndAt bt (if b = .rdi then (slotAt d).bind fun i => locIdx L (.slot i) else none) k).1
  mh b d k := if uBase b then 2 ^ 64 - 1
    else (bndAt bt (if b = .rdi then (slotAt d).bind fun i => locIdx L (.slot i) else none) k).2

theorem toInt_range (x : BitVec 64) : -2 ^ 63 ≤ x.toInt ∧ x.toInt ≤ 2 ^ 63 - 1 := by
  have := x.isLt
  rw [BitVec.toInt_eq_toNat_cond]
  split <;> omega

theorem group5_getD : ∀ (ts : List T) (j i : Nat), i < 5 → 5 * j + 5 ≤ ts.length →
    ((group5 ts).getD j zero5).get i = ts.getD (5 * j + i) (.lit 0 0 0 0)
  | a :: b :: c :: d :: e :: rest, 0, i, hi, _ => by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl
  | a :: b :: c :: d :: e :: rest, j + 1, i, hi, h => by
    have := group5_getD rest j i hi (by simp only [List.length_cons] at h; omega)
    simp only [group5, List.getD_cons_succ]
    rw [this, show 5 * (j + 1) + i = (5 * j + i) + 5 by omega]
    rfl
  | [], _, _, _, h => by simp at h
  | [_], _, _, _, h => by simp at h
  | [_, _], _, _, _, h => by simp at h
  | [_, _, _], _, _, _, h => by simp at h
  | [_, _, _, _], _, _, _, h => by simp at h

/-- A limb of the vectors in the places `L` is the quadword of its place. -/
theorem tab_leaves (s : State) (L : List Loc) {j i : Nat} (hi : i < 5) (hj : 5 * j + 5 ≤ L.length) (k : Nat) :
    tab (envOf s) (leaves L) j i k = ints s (L.getD (5 * j + i) (.reg 0)) k := by
  have hl : 5 * j + i < L.length := by omega
  rw [tab, leaves, group5_getD _ j i hi (by rw [List.length_map]; exact hj)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  simp only [Option.map_some, Option.getD_some]
  cases L[5 * j + i] <;> rfl

/-- What a piece starts from is within the bounds of its places. -/
theorem envOK_of {s : State} {L : List Loc} {bt : BT}
    (h : ∀ n l, L[n]? = some l → ∀ k, k < 4 → ∀ b, bt.get (n / 5) k = some b → b.1 ≤ ints s l k ∧ ints s l k ≤ b.2) :
    EnvOK s (bndsOf L bt) := by
  have key (l : Loc) (k : Nat) (hk : k < 4) :
      (bndAt bt (locIdx L l) k).1 ≤ ints s l k ∧ ints s l k ≤ (bndAt bt (locIdx L l) k).2 := by
    unfold locIdx bndAt
    dsimp only
    split
    · rename_i n hn
      split at hn
      · rename_i hlt
        cases hn
        have hl : L[L.idxOf l]? = some l := by
          rw [List.getElem?_eq_getElem hlt]; exact congrArg some (List.getElem_idxOf hlt)
        cases hb : bt.get (L.idxOf l / 5) k with
        | none => exact toInt_range _
        | some b => exact h _ l hl k hk b hb
      · cases hn
    · exact toInt_range _
  refine ⟨fun r k hk => key (.reg r) k hk, fun b d k hk => ?_⟩
  simp only [bndsOf]
  by_cases hu : uBase b = true
  · simp only [hu, ite_true, envOf]
    have := (s.mem.readW (s.gpr b + BitVec.ofNat 64 (d + 8 * k)) 64).isLt
    omega
  have hm : (envOf s).m b d k = (s.mem.readW (s.gpr b + BitVec.ofNat 64 (d + 8 * k)) 64).toInt := by
    simp only [envOf, hu, Bool.false_eq_true, ite_false]
  simp only [hu, Bool.false_eq_true, ite_false]
  by_cases hb : b = .rdi
  · subst hb
    simp only [ite_true]
    cases hs : slotAt d with
    | none => rw [hm]; exact toInt_range _
    | some i =>
      simp only [Option.bind_some]
      have hd : d = slotOff i := by
        unfold slotAt at hs
        split at hs
        · rename_i hc; cases hs; simp only [slotOff]; omega
        · cases hs
      subst hd
      exact key (.slot i) k hk
  · simp only [hb, ite_false]
    rw [hm]
    exact toInt_range _

/-- The terms of the limbs of the lanes with bounds in `bt` have bounds within 64 signed bits. -/
def ivWithin (B : Bnds) (ts : List T) (bt : BT) : Bool :=
  ts.zipIdx.all fun (t, n) => (List.range 4).all fun k =>
    match bt.get (n / 5) k with
    | none => true
    | some b => match t.iv B k with
      | some iv => decide (b.1 ≤ iv.1 ∧ iv.2 ≤ b.2 ∧ -2 ^ 63 ≤ b.1 ∧ b.2 < 2 ^ 63)
      | none => false

/-- What a piece does, for integers: in the lanes with bounds in `bt`, the
limbs in the places of its results are those of the stage's terms, within
those bounds. -/
theorem stage_tab {c : List Instr} {ins : List (F5 T)} {seg : Seg Id T} {outs : List Loc}
    (h : chkSeg c ins seg outs = true) {s₀ : State} (hc : Ctx par s₀) {B : Bnds} (hB : EnvOK s₀ B) {bt : BT}
    (hiv : ivWithin B (segT seg ins) bt = true) :
    WP isa (.block c) s₀ fun s =>
      (∃ σ, SRel par σ s₀ s) ∧ Unch (s₀.gpr .rdi) [(cfg.sbase, par.win - cfg.sbase)] s₀.mem s.mem ∧
      ∀ (n : Nat) (l : Loc) (t : T), outs[n]? = some l → (segT seg ins)[n]? = some t →
        ∀ k, k < 4 → ∀ b, bt.get (n / 5) k = some b →
          ints s l k = t.int (envOf s₀) k ∧ b.1 ≤ ints s l k ∧ ints s l k ≤ b.2 := by
  refine WP.mono (stage_int h hc hB) fun s ⟨hσ, hu, hs⟩ => ⟨hσ, hu, fun n l t hl ht k hk b hb => ?_⟩
  have hm : (t, n) ∈ (segT seg ins).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]; simpa using ht
  have h1 := List.all_eq_true.1 hiv (t, n) hm
  have h2 := List.all_eq_true.1 h1 k (List.mem_range.2 hk)
  simp only [hb] at h2
  cases hiv' : t.iv B k with
  | none => simp [hiv'] at h2
  | some iv =>
    simp only [hiv', decide_eq_true_eq] at h2
    obtain ⟨e, lo, hi⟩ := hs n l t hl ht k hk iv hiv' (by omega) (by omega)
    exact ⟨e, by omega, by omega⟩

end

/-!
## What the blocks start from

The terms each block starts from: the accumulator in `ymm0`–`ymm19`, an
entry's vectors and the mask of its sign in memory.
-/

section

open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma

/-- The registers from `r` as a field vector. -/
def t5 (r : Nat) : F5 T := ⟨.reg r, .reg (r + 1), .reg (r + 2), .reg (r + 3), .reg (r + 4)⟩

/-- Five times 32 bytes from `b + d`, `n` bytes apart. -/
def ld5 (b : Reg) (d n : Nat) : F5 T := ⟨.ld b d, .ld b (d + n), .ld b (d + 2 * n), .ld b (d + 3 * n), .ld b (d + 4 * n)⟩

/-- The accumulator in `ymm0`–`ymm19`. -/
def stT : List (F5 T) := [t5 0, t5 5, t5 10, t5 15]

/-- The mask of an entry's sign. -/
def sgnT : F5 T := F5.rep (.ld .r9 0)

/-- What the addition starts from: the accumulator, the entry's two vectors and its sign. -/
def addT : List (F5 T) := stT ++ [t5 20, t5 25, sgnT]

def setT : List (F5 T) := [t5 20, sgnT]

/-- The words of a Jacobian point at `rcx` and of its `Z²` and `Z³` at `rdx`. -/
def rawQT : F5 T := ⟨.ld .rcx 0, .ld .rcx 32, .ld .rcx 64, .ld .rdx 0, .ld .rdx 32⟩

/-- The words of an affine point at `rdx`. -/
def rawGT : F5 T := ⟨.ld .rdx 0, .ld .rdx 32, .ld .rdx 0, .ld .rdx 0, .ld .rdx 0⟩

/-- What the entry of a Jacobian point starts from: the accumulator, and the point's words. -/
def convQT : List (F5 T) := stT ++ [rawQT]

def convGT : List (F5 T) := stT ++ [rawGT]

def regs20 : List Loc := (List.range 20).map .reg

def regs5 : List Loc := (List.range 5).map .reg

/-- The accumulator's registers and the entry's, `ymm20`–`ymm29`. -/
def regs30 : List Loc := (List.range 30).map .reg

/-- The registers of the entry's first vector, `ymm20`–`ymm24`. -/
def regsE : List Loc := (List.range 5).map fun i => .reg (20 + i)

end

/-!
## The bounds a block starts from

The limbs of the accumulator in `ymm0`–`ymm19` (`stBT`: `u` in
`[-2⁶⁰ - 2⁵⁸, 2⁶⁰]`, `zn` and `n3` carried, `q3` in `[0, 2⁵⁶)`, each in its lanes),
and of an entry and the mask of its sign in memory (`entB`).
-/

section

open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma

/-- The bounds of carried limbs. -/
def carriedB : Option (Int × Int) := some (0, 2 ^ 52 - 1)

/-- The bounds of the accumulator's limbs: `u`, `zn`, `n3`, `q3`. -/
def stBT : BT :=
  [[some (-(2 ^ 60 + 2 ^ 58), 2 ^ 60), none, none, none],
   [none, carriedB, none, none],
   [none, carriedB, none, carriedB],
   [none, some (0, 2 ^ 56 - 1), none, some (0, 2 ^ 56 - 1)]]

/-- `B`, with the mask of an entry's sign at `r9` (zero, or all ones in the lanes 0 and 1). -/
def sgnB (B : Bnds) : Bnds where
  vl := B.vl
  vh := B.vh
  ml b d k := if b = .r9 ∧ d = 0 then (if k < 2 then -1 else 0) else B.ml b d k
  mh b d k := if b = .r9 ∧ d = 0 then 0 else B.mh b d k

/-- The bounds of an entry's limbs: `ta`, carried, and the first lane of `tb`. -/
def entBT : BT := [[carriedB, carriedB, carriedB, carriedB], [carriedB, none, none, none]]

/-- The bounds the doubling and the conversion out start from. -/
def stB : Bnds := bndsOf regs20 stBT

/-- The bounds the addition starts from. -/
def addB : Bnds := sgnB (bndsOf regs30 (stBT ++ entBT))

/-- The bounds the first point starts from: the addition's. -/
def setB : Bnds := addB

/-- The terms of stage `j` of a block. -/
def stageT (locs : List (List Loc)) (segs : List (Seg Id T)) (ins : List (F5 T)) (j : Nat) : List T :=
  segT (segs.getD j (fun _ => pure [])) (if j = 0 then ins else leaves (locs.getD (j - 1) []))

/-- The bounds stage `j` of a block starts from: `B0`, or those of the places before it. -/
def stageB (locs : List (List Loc)) (bts : List BT) (B0 : Bnds) (j : Nat) : Bnds :=
  if j = 0 then B0 else bndsOf (locs.getD (j - 1) []) (bts.getD (j - 1) [])

end


open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma

def dblIV0 : BT :=
  [[some (-1337001217, 2 ^ 52 - 1), some (-1337001217, 2 ^ 52 - 1), some (-1337001217, 2 ^ 52 - 1), some (-799081217, 2 ^ 52 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1)]]

def dblBT0 : BT :=
  [[some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1337001217, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1)]]

def dblIV1 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1337001217, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1)]]

def dblBT1 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1337001217, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1)]]

def dblIV2 : BT :=
  [[some (-1, 2 ^ 52 - 1), some (-16252945, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1337001217, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1)]]

def dblBT2 : BT :=
  [[some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1337001217, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1)]]

def dblIV3 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1337001217, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1)]]

def dblBT3 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1337001217, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1)]]

def dblIV4 : BT :=
  [[some (-1686111829, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1686111829, 2 ^ 52 - 1), some (-50331697, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)]]

def dblBT4 : BT :=
  [[some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)]]

def dblIV5 : BT :=
  [[some (-978161965391019888, 54342331410612216), some (-978161965391019888, 54342331410612216), some (-978161965391019888, 54342331410612216), some (-978161965391019888, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)]]

def dblBT5 : BT :=
  [[some (-978161965391019888, 54342331410612216), some (-978161965391019888, 54342331410612216), some (-978161965391019888, 54342331410612216), some (-978161965391019888, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)]]

/-- The bounds after each stage. -/
def dblBTs : List BT := [dblBT0, dblBT1, dblBT2, dblBT3, dblBT4, dblBT5]

/-- The bounds of the terms of each stage. -/
def dblIVs : List BT := [dblIV0, dblIV1, dblIV2, dblIV3, dblIV4, dblIV5]

def addIV0 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (-1441151880758558720, 1152921504606846976), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-1, 0), some (-1, 0), some (0, 0), some (0, 0)]]

def addBT0 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (-1441151880758558720, 1152921504606846976), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-1, 0), some (-1, 0), some (0, 0), some (0, 0)]]

def addIV1 : BT :=
  [[some (-334299457, 2 ^ 52 - 1), some (-12517389, 2 ^ 52 - 1), some (-12517389, 2 ^ 52 - 1), some (-12713997, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)]]

def addBT1 : BT :=
  [[some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)]]

def addIV2 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)]]

def addBT2 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)]]

def addIV3 : BT :=
  [[some (-12582925, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)],
   [some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def addBT3 : BT :=
  [[some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def addIV4 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def addBT4 : BT :=
  [[some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def addIV5 : BT :=
  [[some (-12582925, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-150995089, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def addBT5 : BT :=
  [[some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def addIV6 : BT :=
  [[some (-434738651284897728, 108684662821224432), some (-434738651284897728, 108684662821224432), some (-434738651284897728, 108684662821224432), some (-434738651284897728, 108684662821224432)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)]]

def addBT6 : BT :=
  [[some (-434738651284897728, 108684662821224432), some (-434738651284897728, 108684662821224432), some (-434738651284897728, 108684662821224432), some (-434738651284897728, 108684662821224432)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)]]

/-- The bounds after each stage. -/
def addBTs : List BT := [addBT0, addBT1, addBT2, addBT3, addBT4, addBT5, addBT6]

/-- The bounds of the terms of each stage. -/
def addIVs : List BT := [addIV0, addIV1, addIV2, addIV3, addIV4, addIV5, addIV6]

def setIV0 : BT :=
  [[some (-4503599627370495, 2 ^ 52 - 1), some (-4503599627370495, 2 ^ 52 - 1), some (-4503599627370495, 2 ^ 52 - 1), some (-4503599627370495, 2 ^ 52 - 1)],
   [some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)],
   [some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)]]

def setBT0 : BT :=
  [[some (-4503599627370495, 2 ^ 52 - 1), some (-4503599627370495, 2 ^ 52 - 1), some (-4503599627370495, 2 ^ 52 - 1), some (-4503599627370495, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def setIV1 : BT :=
  [[some (-4503599627370495, 2 ^ 52 - 1), some (-4503599627370495, 2 ^ 52 - 1), some (-4503599627370495, 2 ^ 52 - 1), some (-4503599627370495, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)]]

def setBT1 : BT :=
  [[some (-4503599627370495, 2 ^ 52 - 1), some (-4503599627370495, 2 ^ 52 - 1), some (-4503599627370495, 2 ^ 52 - 1), some (-4503599627370495, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216), some (0, 54342331410612216)]]

/-- The bounds after each stage. -/
def setBTs : List BT := [setBT0, setBT1]

/-- The bounds of the terms of each stage. -/
def setIVs : List BT := [setIV0, setIV1]

def outIV0 : BT :=
  [[some (-334299457, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), none, some (-1, 2 ^ 52 - 1)]]

def outBT0 : BT :=
  [[some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), none, some (0, 2 ^ 52 - 1)]]

def outIV1 : BT :=
  [[some (0, 45264488534048764), some (0, 45299810344959994), some (0, 31824333273759742), some (0, 45264488534048764)]]

def outBT1 : BT :=
  [[some (0, 45264488534048764), some (0, 45299810344959994), some (0, 31824333273759742), some (0, 45264488534048764)]]

def outIV2 : BT :=
  [[some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)]]

def outBT2 : BT :=
  [[some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

/-- The bounds after each stage. -/
def outBTs : List BT := [outBT0, outBT1, outBT2]

/-- The bounds of the terms of each stage. -/
def outIVs : List BT := [outIV0, outIV1, outIV2]

def convQIV0 : BT :=
  [[some (-1441151880758558720, 1152921504606846976), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1)],
   [some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1), some (-1, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

def convQBT0 : BT :=
  [[some (-1441151880758558720, 1152921504606846976), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)]]

/-- The bounds after each stage. -/
def convQBTs : List BT := [convQBT0]

/-- The bounds of the terms of each stage. -/
def convQIVs : List BT := [convQIV0]

def convGIV0 : BT :=
  [[some (-1441151880758558720, 1152921504606846976), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1)],
   [some (4, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (8, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (2, 2 ^ 52 - 1), some (0, 0), some (0, 0), some (0, 0)]]

def convGBT0 : BT :=
  [[some (-1441151880758558720, 1152921504606846976), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (-9223372036854775808, 2 ^ 63 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 52 - 1)],
   [some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1), some (-9223372036854775808, 2 ^ 63 - 1), some (0, 2 ^ 56 - 1)],
   [some (4, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1), some (8, 2 ^ 52 - 1), some (0, 2 ^ 52 - 1)],
   [some (2, 2 ^ 52 - 1), some (0, 0), some (0, 0), some (0, 0)]]

/-- The bounds after each stage. -/
def convGBTs : List BT := [convGBT0]

/-- The bounds of the terms of each stage. -/
def convGIVs : List BT := [convGIV0]

end


open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma
open VG.Proof.Weierstrass (Unch)

theorem group5_flat : ∀ xs : List (F5 T), group5 (xs.flatMap F5.toList) = xs
  | [] => rfl
  | x :: xs => by
    simp only [List.flatMap_cons, F5.toList, List.cons_append, List.nil_append, group5]
    rw [group5_flat xs]

theorem flat_length (xs : List (F5 T)) : (xs.flatMap F5.toList).length = 5 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, List.length_append, ih, F5.toList, List.length_cons, List.length_nil]; omega

/-- A limb of the flattened vectors. -/
theorem flat_get (xs : List (F5 T)) {j i : Nat} (hi : i < 5) (hj : j < xs.length) :
    (xs.flatMap F5.toList)[5 * j + i]? = some ((xs.getD j zero5).get i) := by
  have h := group5_getD (xs.flatMap F5.toList) j i hi (by rw [flat_length]; omega)
  rw [group5_flat] at h
  rw [h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [flat_length]; omega)]
  rfl

theorem vI_get (E : Env) (k : Nat) (v : F5 T) :
    vI E k v = val5 ((v.get 0).int E k) ((v.get 1).int E k) ((v.get 2).int E k) ((v.get 3).int E k) ((v.get 4).int E k) :=
  rfl

/-- The bounds after a stage are those of its terms (or wider), but for the lanes `ovs`, which are carried. -/
def ovOk (bt iv : BT) (ovs : List (Nat × Nat)) : Bool :=
  (List.range bt.length).all fun j => (List.range ((bt.getD j []).length)).all fun k =>
    match bt.get j k with
    | none => true
    | some b => (match iv.get j k with
        | some c => decide (b.1 ≤ c.1 ∧ c.2 ≤ b.2)
        | none => false) ||
        (ovs.contains (j, k) && decide (b = (0, 2 ^ 52 - 1)) && (iv.get j k).isSome)

theorem ovOk_spec {bt iv : BT} {ovs : List (Nat × Nat)} (h : ovOk bt iv ovs = true) {j k : Nat} {b : Int × Int}
    (hb : bt.get j k = some b) :
    (∃ c, iv.get j k = some c ∧ b.1 ≤ c.1 ∧ c.2 ≤ b.2) ∨
      ((j, k) ∈ ovs ∧ b = (0, 2 ^ 52 - 1) ∧ ∃ c, iv.get j k = some c) := by
  have hj : j < bt.length := by
    by_contra hn
    simp only [BT.get, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hn), Option.getD_none,
      List.getElem?_nil] at hb
    cases hb
  have hk : k < (bt.getD j []).length := by
    by_contra hn
    simp only [BT.get] at hb
    rw [List.getD_eq_getElem?_getD (l := bt.getD j []), List.getElem?_eq_none (Nat.le_of_not_lt hn)] at hb
    cases hb
  have := List.all_eq_true.1 (List.all_eq_true.1 h j (List.mem_range.2 hj)) k (List.mem_range.2 hk)
  simp only [hb, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at this
  rcases this with h1 | ⟨⟨h1, h2⟩, h3⟩
  · cases hc : iv.get j k with
    | none => simp [hc] at h1
    | some c =>
      simp only [hc, decide_eq_true_eq] at h1
      exact Or.inl ⟨c, rfl, h1⟩
  · exact Or.inr ⟨h1, h2, Option.isSome_iff_exists.1 h3⟩

theorem ivWithin_get {B : Bnds} {ts : List T} {bt : BT} (h : ivWithin B ts bt = true) {n k : Nat} {t : T}
    (ht : ts[n]? = some t) (hk : k < 4) {b : Int × Int} (hb : bt.get (n / 5) k = some b) :
    ∃ iv, t.iv B k = some iv ∧ b.1 ≤ iv.1 ∧ iv.2 ≤ b.2 ∧ -2 ^ 63 ≤ b.1 ∧ b.2 < 2 ^ 63 := by
  have hm : (t, n) ∈ ts.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]; simpa using ht
  have h2 := List.all_eq_true.1 (List.all_eq_true.1 h (t, n) hm) k (List.mem_range.2 hk)
  simp only [hb] at h2
  cases hiv : t.iv B k with
  | none => simp [hiv] at h2
  | some iv =>
    simp only [hiv, decide_eq_true_eq] at h2
    exact ⟨iv, rfl, h2⟩

theorem Carried.get {E : Env} {k : Nat} {v : F5 T} (h : Carried E k v) {i : Nat} (hi : i < 5) :
    0 ≤ (v.get i).int E k ∧ (v.get i).int E k < 2 ^ 52 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4]

/-- The limbs of the vectors `ys` under `E'` are those of `xs` under `E`, in the lanes with bounds in `iv`. -/
def Same (iv : BT) (E' : Env) (ys : List (F5 T)) (E : Env) (xs : List (F5 T)) : Prop :=
  ∀ j k b, k < 4 → iv.get j k = some b → ∀ i, i < 5 → tab E' ys j i k = tab E xs j i k

theorem Same.vI {iv : BT} {E' E : Env} {ys xs : List (F5 T)} (h : Same iv E' ys E xs) {j k : Nat} {b : Int × Int}
    (hk : k < 4) (hb : iv.get j k = some b) : vI E' k (ys.getD j zero5) = vI E k (xs.getD j zero5) := by
  have e := h j k b hk hb
  simp only [tab] at e
  rw [vI_get, vI_get, e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide)]

theorem Same.carried {iv : BT} {E' E : Env} {ys xs : List (F5 T)} (h : Same iv E' ys E xs) {j k : Nat}
    {b : Int × Int} (hk : k < 4) (hb : iv.get j k = some b) (hc : Carried E k (xs.getD j zero5)) :
    Carried E' k (ys.getD j zero5) := by
  have e := h j k b hk hb
  simp only [tab] at e
  have e0 := e 0 (by decide); have e1 := e 1 (by decide); have e2 := e 2 (by decide)
  have e3 := e 3 (by decide); have e4 := e 4 (by decide)
  simp only [F5.get] at e0 e1 e2 e3 e4
  unfold Carried at hc ⊢
  rw [e0, e1, e2, e3, e4]
  exact hc

theorem BT.get_lt {bt : BT} {j k : Nat} {b : Int × Int} (h : bt.get j k = some b) : j < bt.length := by
  by_contra hn
  simp only [BT.get, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hn), Option.getD_none,
    List.getElem?_nil] at h
  cases h

/-- What a stage's piece of code does to what is known between the stages. -/
theorem cut_step {c : List Instr} {ins : List (F5 T)} {seg : Seg Id T} {outs : List Loc}
    (h : chkSeg c ins seg outs = true) {s₀ : State} (hc : Ctx par s₀) {B : Bnds} (hB : EnvOK s₀ B)
    {iv bt : BT} {ovs : List (Nat × Nat)} (hiv : ivWithin B (segT seg ins) iv = true) (hov : ovOk bt iv ovs = true)
    (hlen : outs.length = 5 * (Id.run (seg ins)).length) (hrows : iv.length ≤ (Id.run (seg ins)).length)
    (hcar : ∀ j k, (j, k) ∈ ovs → Carried (envOf s₀) k ((Id.run (seg ins)).getD j zero5)) :
    WP isa (.block c) s₀ fun s =>
      (∃ σ, SRel par σ s₀ s) ∧ Unch (s₀.gpr .rdi) [(cfg.sbase, par.win - cfg.sbase)] s₀.mem s.mem ∧
        EnvOK s (bndsOf outs bt) ∧ Same iv (envOf s) (leaves outs) (envOf s₀) (Id.run (seg ins)) := by
  refine WP.mono (stage_tab h hc hB hiv) fun s ⟨hσ, hu, hs⟩ => ⟨hσ, hu, ?_, ?_⟩
  · refine envOK_of fun n l hl k hk b hb => ?_
    have hn : n < outs.length := (List.getElem?_eq_some_iff.1 hl).1
    have hj : n / 5 < (Id.run (seg ins)).length := by omega
    have ht := flat_get (Id.run (seg ins)) (i := n % 5) (Nat.mod_lt _ (by decide)) hj
    rw [show 5 * (n / 5) + n % 5 = n by omega] at ht
    rcases ovOk_spec hov hb with ⟨c', h1, l1, l2⟩ | ⟨h1, h2, c', h3⟩
    · have := (hs n l _ hl ht k hk c' h1).2
      exact ⟨by omega, by omega⟩
    · obtain ⟨e, -, -⟩ := hs n l _ hl ht k hk c' h3
      have := (hcar _ _ h1).get (i := n % 5) (Nat.mod_lt _ (by decide))
      rw [e, h2]
      exact ⟨this.1, by have := this.2; omega⟩
  · intro j k b hk hb i hi
    have hj : j < (Id.run (seg ins)).length := Nat.lt_of_lt_of_le (BT.get_lt hb) hrows
    have ht := flat_get (Id.run (seg ins)) hi hj
    have hn : 5 * j + i < outs.length := by omega
    have hl : outs[5 * j + i]? = some (outs.getD (5 * j + i) (.reg 0)) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]; rfl
    rw [tab_leaves s outs hi (by omega) k]
    exact (hs (5 * j + i) _ _ hl ht k hk b (by rw [show (5 * j + i) / 5 = j by omega]; exact hb)).1

theorem par_cst_length : par.cst.length = 220 := by decide +kernel

/-- A piece of code leaves what the next may read and write, and the constants. -/
theorem ctx_step {σ : VSym} {s₀ s : State} (hc : Ctx par s₀) (h : SRel par σ s₀ s) : Ctx par s := by
  have hg := h.gpr
  refine ⟨?_, hc.small, ?_, ?_, ?_, ?_, ?_, hc.cb⟩
  · intro d hd; rw [h.wr, hg]; exact hc.win d hd
  · intro b d hb hcb hd; rw [h.rd, h.wr, hg]; exact hc.rd b d hb hcb hd
  · intro b d hb hcb hd; rw [hg]; exact hc.sep b d hb hcb hd
  · intro d hd; rw [h.rd, h.wr, hg]; exact hc.crd d hd
  · intro d hd; rw [hg]; exact hc.csep d hd
  · intro i hi
    rw [par_cst_length] at hi
    -- the 32 bytes of the constants that hold quadword `i`
    have hd : 8 * (min i 216) + 32 ≤ 8 * par.cst.length := by rw [par_cst_length]; omega
    have e := stores_sep (hc.csep _ hd) hc.small (k := i - min i 216) (by omega) σ.st h.al h.lo
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 8 * min i 216 + 8 * (i - min i 216) = 8 * i by omega] at e
    rw [h.mem, hg, e]
    exact hc.cst i (by rw [par_cst_length]; exact hi)

end VG.Proof.P256.X86_64.Ifma
