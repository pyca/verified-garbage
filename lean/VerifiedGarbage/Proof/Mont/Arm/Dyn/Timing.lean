module

public import VerifiedGarbage.Impl.Mont.Arm.Context
public import VerifiedGarbage.Proof.Framework.Arm.TaintEraseU
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Mont.Arm.Context
meta import VerifiedGarbage.Proof.Framework.Arm.TaintEraseU
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: constant time

Only the working space's base `r12` is public on entry (`wsT`), and
optionally `r11` and `lr`, which the arithmetic leaves alone, for its
callers' loops. Every address is `r12` plus an offset, or a pointer moved by
public steps, and every branch compares pointers or counts, but those of
the context's setup on bits of the modulus (below): the analysis
of an operation's code without its offsets and `movw` immediates
(`Code.eraseOff`) is the analysis of the code itself (`check_eraseOff`),
and that code is the same for every modulus and layout, so each check below
evaluates the analysis of one instance (`erased_relCT`). The exponentiation's
shift has a word a step (`shiftUp_check`), checked by induction. The
analysis is `taintU`, which follows the `umaal` of the multiplication on
words.
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic

variable {umaal : Bool}

/-- The public registers: the working space's base, and `r11` and `lr` if `p` and `q`. -/
def wsRegs (p q : Bool) : List Reg := .r12 :: ((if p then [.r11] else []) ++ (if q then [.lr] else []))

def wsT (p q : Bool) : taintU.T := Taint.ofRegs (wsRegs p q)

theorem wsT_noBase (p q : Bool) : Taint.NoBase (wsT p q) := Taint.noBase_ofRegs _

/-- A modulus whose code stands for every modulus's, once erased. -/
def eraseMod : Mod := { n := 1, mo := 0, tmp := 0, minv := 0 }

/-- A program whose code is `c₀`'s but for offsets and immediates, from the
analysis of `c₀`. -/
theorem erased_relCT {c c₀ : Prog isa} {τ σ : taintU.T} (h : VG.Taint.Hint taintU.T)
    (e : Code.eraseOff c = Code.eraseOff c₀) (hn : Taint.NoBase τ)
    (L : (VG.Taint.check taintU τ c₀ h).map (taintU.le σ) = some true) :
    RelCT isa (VG.Arm.Taint.Agree τ) c (VG.Arm.Taint.Agree σ) := by
  obtain ⟨τ', H, L'⟩ := Option.map_eq_some_iff.mp L
  have H' : VG.Taint.check taintU τ c h = some τ' := by
    rw [← Taint.checkU_eraseOff c h hn, e, Taint.checkU_eraseOff c₀ h hn, H]
  intro s t tr ur sf tf A E F
  obtain ⟨T, B⟩ := VG.Taint.check_sound H' A E F
  exact ⟨T, taintU.le_sound L' B⟩

/-! ## Code without its offsets

Each operation's code without its offsets and `movw` immediates is one
program for every modulus and layout. A program built from several
operations is proven so by rewriting with each operation's equation: `rfl`
on the whole program has the elaborator unify the two programs' offsets
(arithmetic in the width) before it unfolds them, seconds per program. The
equations are stated about `Code Instr Cond`, the type of the operations'
code, so that `simp` matches them. -/

theorem eraseOff_seq (a b : Code Instr Cond) :
    Code.eraseOff (@Code.seq Instr Cond a b) = @Code.seq Instr Cond (Code.eraseOff a) (Code.eraseOff b) := rfl

theorem eraseOff_ite (c : Cond) (a b : Code Instr Cond) :
    Code.eraseOff (@Code.ite Instr Cond c a b) = @Code.ite Instr Cond c (Code.eraseOff a) (Code.eraseOff b) := rfl

theorem eraseOff_loop (a : Code Instr Cond) (c : Cond) :
    Code.eraseOff (@Code.loop Instr Cond a c) = @Code.loop Instr Cond (Code.eraseOff a) c := rfl

theorem eraseOff_ptr (d : Reg) (k : Nat) (l : List Instr) :
    Code.eraseOff (@Code.block Instr Cond (ptr d k ++ l)) = Code.eraseOff (@Code.block Instr Cond (ptr d 0 ++ l)) :=
  rfl

theorem zeros_eraseOff (k o : Nat) : Code.eraseOff (zeros k o) = Code.eraseOff (zeros 1 0) := rfl

theorem addD_eraseOff (M : Mod) (acc o a b : Nat) :
    Code.eraseOff (addD M acc o a b) = Code.eraseOff (addD eraseMod 0 0 0 0) := rfl

theorem mul_eraseOff (M : Mod) (inv acc o a b : Nat) :
    Code.eraseOff (mul umaal M inv acc o a b) = Code.eraseOff (mul umaal eraseMod 0 0 0 0 0) := by
  cases umaal <;> rfl

theorem selectW_eraseOff (k src tmp o : Nat) :
    Code.eraseOff (selectW k src tmp o) = Code.eraseOff (selectW 1 0 0 0) := rfl

theorem one_eraseOff (n out : Nat) : Code.eraseOff (one n out) = Code.eraseOff (one 1 0) := rfl

theorem eraseOff_movw (d : Reg) (k : BitVec 16) :
    Code.eraseOff (@Code.block Instr Cond [.movw d k]) = @Code.block Instr Cond [.movw d 0] := rfl

theorem wordTop_eraseOff (n out w : Nat) : Code.eraseOff (wordTop n out w) = Code.eraseOff (wordTop 1 0 0) := rfl

theorem fromTop_eraseOff (n w : Nat) : Code.eraseOff (fromTop n w) = Code.eraseOff (fromTop 1 0) := by
  simp only [fromTop, eraseOff_seq, wordTop_eraseOff, eraseOff_movw]

theorem fromOne_eraseOff (n : Nat) : Code.eraseOff (fromOne n) = Code.eraseOff (fromOne 1) := rfl

theorem doublings_eraseOff (M : Mod) (acc out : Nat) :
    Code.eraseOff (doublings M acc out) = Code.eraseOff (doublings eraseMod 0 0) := rfl

theorem raise_eraseOff (n : Nat) : Code.eraseOff (raise umaal n) = Code.eraseOff (raise umaal 1) := by
  simp only [raise, eraseOff_seq, eraseOff_loop, doublings_eraseOff, mul_eraseOff]

theorem setupInverse_eraseOff (mo : Nat) :
    Code.eraseOff (@Code.block Instr Cond (setupInverse mo)) =
      Code.eraseOff (@Code.block Instr Cond (setupInverse 0)) := rfl

theorem copyOut_eraseOff (k src : Nat) : Code.eraseOff (copyOut k src) = Code.eraseOff (copyOut 1 0) := rfl

theorem table_eraseOff (n : Nat) : Code.eraseOff (table umaal n) = Code.eraseOff (table umaal 1) := by
  simp only [table, tableStep, eraseOff_seq, eraseOff_loop, mul_eraseOff, copyOut_eraseOff, eraseOff_ptr]

theorem squareFour_eraseOff (n : Nat) :
    Code.eraseOff (squareFour umaal n) = Code.eraseOff (squareFour umaal 1) := by
  simp only [squareFour, eraseOff_seq, eraseOff_loop, mul_eraseOff]

theorem scan_eraseOff (n : Nat) : Code.eraseOff (scan n) = Code.eraseOff (scan 1) := by
  simp only [scan, scanFrom, pick, eraseOff_seq, selectW_eraseOff]

/-! ## The operations -/

theorem mul_check (p q : Bool) :
    ∃ h, (VG.Taint.check taintU (wsT p q) (mul umaal eraseMod 0 0 0 0 0) h).map (taintU.le (wsT p q)) = some true := by
  cases umaal <;> cases p <;> cases q <;> exact ⟨_, by taint_decide⟩

theorem mul_relCT (p q : Bool) (M : Mod) (inv acc o a b : Nat) :
    RelCT isa (VG.Arm.Taint.Agree (wsT p q)) (mul umaal M inv acc o a b) (VG.Arm.Taint.Agree (wsT p q)) := by
  obtain ⟨h, H⟩ := mul_check (umaal := umaal) p q
  exact erased_relCT h (mul_eraseOff ..) (wsT_noBase p q) H

theorem addD_relCT (p q : Bool) (M : Mod) (acc o a b : Nat) :
    RelCT isa (VG.Arm.Taint.Agree (wsT p q)) (addD M acc o a b) (VG.Arm.Taint.Agree (wsT p q)) := by
  obtain ⟨h, H⟩ : ∃ h, (VG.Taint.check taintU (wsT p q) (addD eraseMod 0 0 0 0) h).map (taintU.le (wsT p q)) =
      some true := by cases p <;> cases q <;> exact ⟨_, by taint_decide⟩
  exact erased_relCT h (addD_eraseOff ..) (wsT_noBase p q) H

theorem zeros_relCT (p q : Bool) (k o : Nat) :
    RelCT isa (VG.Arm.Taint.Agree (wsT p q)) (zeros k o) (VG.Arm.Taint.Agree (wsT p q)) := by
  obtain ⟨h, H⟩ : ∃ h, (VG.Taint.check taintU (wsT p q) (zeros 1 0) h).map (taintU.le (wsT p q)) = some true := by
    cases p <;> cases q <;> exact ⟨_, by taint_decide⟩
  exact erased_relCT h (zeros_eraseOff ..) (wsT_noBase p q) H

/-! ## The context's setup

The top bits of some of the modulus's words choose where the setup's
doublings start, and so how many it makes (`rSquared`, `start`), so its code
is not analysed in one piece: what comes before the tests, each test, and
what follows them on either side are each analysed from the working space's
base alone, and the callers show that the tests read the same bits in both
runs. -/

/-- The inverse and one, before the tests. -/
theorem setupHead_relCT (n : Nat) :
    RelCT isa (VG.Arm.Taint.Agree (wsT false false))
      (.seq (.block (setupInverse (modS n))) (one n (oneS n))) (VG.Arm.Taint.Agree (wsT false false)) := by
  obtain ⟨h, H⟩ : ∃ h, (VG.Taint.check taintU (wsT false false) (.seq (.block (setupInverse 0)) (one 1 0)) h).map
      (taintU.le (wsT false false)) = some true := ⟨_, by taint_decide⟩
  exact erased_relCT h (by rw [eraseOff_seq, eraseOff_seq, setupInverse_eraseOff, one_eraseOff]) (wsT_noBase _ _) H

/-- A test of a word's top bit reads the word at a public address. -/
theorem topTest_relCT (n w : Nat) :
    RelCT isa (VG.Arm.Taint.Agree (wsT false false)) (.block (topTest n w)) (VG.Arm.Taint.Agree (wsT false false)) :=
  erased_relCT (c₀ := .block (topTest 0 0)) (.block []) rfl (wsT_noBase _ _) (by decide)

/-- Where the doublings start, on either side of a test: the number and its
count in `lr`, which is public. -/
theorem fromTop_relCT (n w : Nat) :
    RelCT isa (VG.Arm.Taint.Agree (wsT false false)) (fromTop n w) (VG.Arm.Taint.Agree (wsT false true)) := by
  obtain ⟨h, H⟩ : ∃ h, (VG.Taint.check taintU (wsT false false) (fromTop 1 0) h).map
      (taintU.le (wsT false true)) = some true := ⟨_, by taint_decide⟩
  exact erased_relCT h (fromTop_eraseOff n w) (wsT_noBase _ _) H

theorem fromOne_relCT (n : Nat) :
    RelCT isa (VG.Arm.Taint.Agree (wsT false false)) (fromOne n) (VG.Arm.Taint.Agree (wsT false true)) := by
  obtain ⟨h, H⟩ : ∃ h, (VG.Taint.check taintU (wsT false false) (fromOne 1) h).map
      (taintU.le (wsT false true)) = some true := ⟨_, by taint_decide⟩
  exact erased_relCT h (fromOne_eraseOff n) (wsT_noBase _ _) H

/-- The doublings that `lr` counts, and the squarings. -/
theorem raise_relCT (n : Nat) :
    RelCT isa (VG.Arm.Taint.Agree (wsT false true)) (raise umaal n) (VG.Arm.Taint.Agree (wsT false false)) := by
  obtain ⟨h, H⟩ : ∃ h, (VG.Taint.check taintU (wsT false true) (raise umaal 1) h).map
      (taintU.le (wsT false false)) = some true := by cases umaal <;> exact ⟨_, by taint_decide⟩
  exact erased_relCT h (raise_eraseOff n) (wsT_noBase _ _) H

/-! ## The exponentiation -/

/-- A sequence whose second part's analysis satisfies `P`. -/
theorem check_seq_of {τ mid : taintU.T} {a b : Prog isa} {ha hb : VG.Taint.Hint taintU.T} {P : taintU.T → Bool}
    (h₁ : (VG.Taint.check taintU τ a ha).map (taintU.le mid) = some true)
    (h₂ : (VG.Taint.check taintU mid b hb).map P = some true) :
    (VG.Taint.check taintU τ (.seq a b) (.seq mid ha hb)).map P = some true := by
  obtain ⟨u, H, L⟩ := Option.map_eq_some_iff.mp h₁
  change ((VG.Taint.check taintU τ a ha).bind fun τ' => if taintU.le mid τ' then _ else none).map P = _
  rw [H, Option.bind_some, L, ite_eq_left rfl]
  exact h₂

theorem check_erased {c c₀ : Prog isa} {τ : taintU.T} (h : VG.Taint.Hint taintU.T)
    (e : Code.eraseOff c = Code.eraseOff c₀) (hn : Taint.NoBase τ) :
    VG.Taint.check taintU τ c h = VG.Taint.check taintU τ c₀ h := by
  rw [← Taint.checkU_eraseOff c h hn, e, Taint.checkU_eraseOff c₀ h hn]

theorem checkBlock_append {M : ISA} (A : VG.Taint M) (τ : A.T) (a b : List M.Instr) :
    A.checkBlock τ (a ++ b) = (A.checkBlock τ a).bind (A.checkBlock · b) := by
  induction a generalizing τ with
  | nil => rfl
  | cons i is ih =>
    change (A.step τ i).bind (fun t => A.checkBlock t (is ++ b)) =
      ((A.step τ i).bind (fun t => A.checkBlock t is)).bind (A.checkBlock · b)
    rw [Option.bind_assoc]
    simp only [ih]


/-- The taint of a window's shift: the exponent's address in `r1` public too. -/
def shiftT : taintU.T := Taint.ofRegs (.r1 :: wsRegs true true)

theorem shiftT_noBase : Taint.NoBase shiftT := Taint.noBase_ofRegs _

/-- A word of the shift, which leaves its taint as it was. -/
theorem shiftUpWord_check (j : Nat) :
    taintU.checkBlock shiftT ([.ldr .r4 .r1 (4 * j), .dp .orr .r5 .r2 (.shifted .r4 .lsl 4),
      .mov .r2 (.shifted .r4 .lsr 28), .str .r5 .r1 (4 * j)] : List Instr) = some shiftT := by
  rw [← Taint.checkBlockU_eraseOff shiftT_noBase]
  rfl

theorem shiftUp_check : ∀ k j, taintU.checkBlock shiftT (shiftUp k j) = some shiftT
  | 0, _ => rfl
  | k + 1, j => by
    rw [shiftUp, checkBlock_append taintU, shiftUpWord_check, Option.bind_some, shiftUp_check k (j + 1)]

/-- The window's block: the bits that come in are zero, which is public,
until the first word's go out. -/
theorem window_check (n expWords : Nat) :
    (taintU.checkBlock (wsT true true) (window n expWords)).map (taintU.le shiftT) = some true := by
  rw [window, checkBlock_append taintU,
    show taintU.checkBlock (wsT true true) (ptr .r1 (expS n)) = some shiftT by
      rw [← Taint.checkBlockU_eraseOff (wsT_noBase true true)]; rfl,
    Option.bind_some]
  cases expWords with
  | zero => rfl
  | succ k =>
    rw [shiftUp, ← List.cons_append, checkBlock_append taintU,
      show taintU.checkBlock shiftT (.mov .r2 (.imm 0) :: ([.ldr .r4 .r1 (4 * 0),
        .dp .orr .r5 .r2 (.shifted .r4 .lsl 4), .mov .r2 (.shifted .r4 .lsr 28),
        .str .r5 .r1 (4 * 0)] : List Instr)) = some shiftT from rfl,
      Option.bind_some, shiftUp_check]
    rfl

theorem check_erased_map {c c₀ : Prog isa} {τ : taintU.T} {h : VG.Taint.Hint taintU.T} {P : taintU.T → Bool}
    (e : Code.eraseOff c = Code.eraseOff c₀) (hn : Taint.NoBase τ)
    (L : (VG.Taint.check taintU τ c₀ h).map P = some true) : (VG.Taint.check taintU τ c h).map P = some true := by
  rw [check_erased h e hn]; exact L

theorem check_loop_of {τ σ : taintU.T} {body : Prog isa} {c : Cond} {h : VG.Taint.Hint taintU.T}
    (hσ : taintU.le σ τ = true)
    (hb : (VG.Taint.check taintU σ body h).map (fun σ' => taintU.le σ σ' && taintU.condPub σ' c) = some true) :
    (VG.Taint.check taintU τ (.loop body c) (.loop σ h)).map (taintU.le σ) = some true := by
  obtain ⟨σ', H, L⟩ := Option.map_eq_some_iff.mp hb
  change (if taintU.le σ τ then (VG.Taint.check taintU σ body h).bind
    (fun σ' => if taintU.le σ σ' && taintU.condPub σ' c then some σ' else none) else none).map _ = _
  rw [hσ, ite_eq_left rfl, H, Option.bind_some, L, ite_eq_left rfl]
  simp only [Option.map_some, Option.some.injEq]
  simp only [Bool.and_eq_true] at L
  exact L.1

/-- Constant time from a check. -/
theorem relCT_of_check {c : Prog isa} {τ σ : taintU.T} {h : VG.Taint.Hint taintU.T}
    (L : (VG.Taint.check taintU τ c h).map (taintU.le σ) = some true) :
    RelCT isa (VG.Arm.Taint.Agree τ) c (VG.Arm.Taint.Agree σ) := by
  obtain ⟨τ', H, L'⟩ := Option.map_eq_some_iff.mp L
  intro s t tr ur sf tf A E F
  obtain ⟨T, B⟩ := VG.Taint.check_sound H A E F
  exact ⟨T, taintU.le_sound L' B⟩

theorem windowStep_check (n expWords : Nat) :
    ∃ h, (VG.Taint.check taintU (wsT true true) (windowStep umaal n expWords) h).map
      (fun σ' => taintU.le (wsT true true) σ' && taintU.condPub σ' .ne) = some true := by
  obtain ⟨h₁, H₁⟩ : ∃ h, (VG.Taint.check taintU (wsT true true) (squareFour umaal 1) h).map
      (taintU.le (wsT true true)) = some true := by cases umaal <;> exact ⟨_, by taint_decide⟩
  obtain ⟨h₂, H₂⟩ : ∃ h, (VG.Taint.check taintU shiftT (scan 1) h).map (taintU.le (wsT true true)) = some true :=
    ⟨_, by taint_decide⟩
  obtain ⟨h₃, H₃⟩ := mul_check (umaal := umaal) true true
  unfold windowStep
  refine ⟨.seq (wsT true true) h₁ (.seq shiftT (.block []) (.seq (wsT true true) h₂
      (.seq (wsT true true) h₃ (.block [])))),
    check_seq_of (check_erased_map (squareFour_eraseOff n) (wsT_noBase _ _) H₁)
      (check_seq_of (window_check n expWords)
        (check_seq_of (check_erased_map (scan_eraseOff n) shiftT_noBase H₂)
          (check_seq_of (check_erased_map (mul_eraseOff ..) (wsT_noBase _ _) H₃) ?_)))⟩
  rfl

/-- The exponentiation, from the working space's base alone: it sets `r11`
and `lr` itself. -/
theorem exponentiate_relCT (n expWords : Nat) :
    RelCT isa (VG.Arm.Taint.Agree (wsT false false)) (exponentiate umaal n expWords)
      (VG.Arm.Taint.Agree (wsT false false)) := by
  obtain ⟨h₁, H₁⟩ : ∃ h, (VG.Taint.check taintU (wsT false false) (table umaal 1) h).map
      (taintU.le (wsT true true)) = some true := by cases umaal <;> exact ⟨_, by taint_decide⟩
  obtain ⟨h₂, H₂⟩ := mul_check (umaal := umaal) true true
  obtain ⟨h₃, H₃⟩ := windowStep_check (umaal := umaal) n expWords
  obtain ⟨h₄, H₄⟩ : ∃ h, (VG.Taint.check taintU (wsT true true) (mul umaal eraseMod 0 0 0 0 0) h).map
      (taintU.le (wsT false false)) = some true := by cases umaal <;> exact ⟨_, by taint_decide⟩
  refine relCT_of_check (h := .seq (wsT true true) h₁ (.seq (wsT true true) h₂ (.seq (wsT true true) (.block [])
    (.seq (wsT true true) (.loop (wsT true true) h₃) h₄)))) ?_
  unfold exponentiate
  refine check_seq_of (check_erased_map (table_eraseOff n) (wsT_noBase _ _) H₁) ?_
  refine check_seq_of (check_erased_map (mul_eraseOff ..) (wsT_noBase _ _) H₂) ?_
  refine check_seq_of (check_erased_map (c₀ := .block [.movw .lr 0]) rfl (wsT_noBase _ _) rfl) ?_
  refine check_seq_of (check_loop_of rfl H₃) ?_
  exact check_erased_map (mul_eraseOff ..) (wsT_noBase _ _) H₄

/-! ## A product of two powers -/

theorem tableFill_check (n : Nat) : ∀ ops : List (Nat × Nat × Nat),
    ∃ h, (VG.Taint.check taintU (wsT false false) (tableFill umaal n ops) h).map (taintU.le (wsT false false)) =
      some true
  | [] => ⟨.block [], rfl⟩
  | (k, a, b) :: r => by
    obtain ⟨h₁, H₁⟩ := mul_check (umaal := umaal) false false
    obtain ⟨h₂, H₂⟩ := tableFill_check n r
    refine ⟨.seq (wsT false false) h₁ h₂, ?_⟩
    rw [tableFill]
    exact check_seq_of (check_erased_map (mul_eraseOff ..) (wsT_noBase _ _) H₁) H₂

/-- The taint of a two-bit shift: the exponent's address in `r1` public too. -/
def shiftT2 : taintU.T := Taint.ofRegs (.r1 :: wsRegs false true)

theorem shiftT2_noBase : Taint.NoBase shiftT2 := Taint.noBase_ofRegs _

theorem shiftUp2Word_check (j : Nat) :
    taintU.checkBlock shiftT2 ([.ldr .r4 .r1 (4 * j), .dp .orr .r5 .r2 (.shifted .r4 .lsl 2),
      .mov .r2 (.shifted .r4 .lsr 30), .str .r5 .r1 (4 * j)] : List Instr) = some shiftT2 := by
  rw [← Taint.checkBlockU_eraseOff shiftT2_noBase]
  rfl

theorem shiftUp2_check : ∀ k j, taintU.checkBlock shiftT2 (shiftUp2 k j) = some shiftT2
  | 0, _ => rfl
  | k + 1, j => by
    rw [shiftUp2, checkBlock_append taintU, shiftUp2Word_check, Option.bind_some, shiftUp2_check k (j + 1)]

theorem windowTwo_check (E expWords : Nat) :
    (taintU.checkBlock (wsT false true) (windowTwo E expWords)).map (taintU.le (wsT false true)) = some true := by
  rw [windowTwo, checkBlock_append taintU,
    show taintU.checkBlock (wsT false true) (ptr .r1 E) = some shiftT2 by
      rw [← Taint.checkBlockU_eraseOff (wsT_noBase false true)]; rfl,
    Option.bind_some]
  cases expWords with
  | zero => rfl
  | succ k =>
    rw [shiftUp2, ← List.cons_append, checkBlock_append taintU,
      show taintU.checkBlock shiftT2 (.mov .r2 (.imm 0) :: ([.ldr .r4 .r1 (4 * 0),
        .dp .orr .r5 .r2 (.shifted .r4 .lsl 2), .mov .r2 (.shifted .r4 .lsr 30),
        .str .r5 .r1 (4 * 0)] : List Instr)) = some shiftT2 from rfl,
      Option.bind_some, shiftUp2_check]
    rfl

theorem windowStep2_check (n expWords : Nat) :
    ∃ h, (VG.Taint.check taintU (wsT false true) (windowStep2 umaal n expWords) h).map
      (fun σ' => taintU.le (wsT false true) σ' && taintU.condPub σ' .ne) = some true := by
  obtain ⟨h₁, H₁⟩ := mul_check (umaal := umaal) false true
  obtain ⟨h₂, H₂⟩ : ∃ h, (VG.Taint.check taintU (wsT false true) (scan 1) h).map (taintU.le (wsT false true)) =
      some true := ⟨_, by taint_decide⟩
  unfold windowStep2 window2
  refine ⟨.seq (wsT false true) h₁ (.seq (wsT false true) h₁ (.seq (wsT false true)
      (.seq (wsT false true) (.block []) (.seq (wsT false true) (.block []) (.seq (wsT false true) (.block [])
        (.block []))))
      (.seq (wsT false true) h₂ (.seq (wsT false true) h₁ (.block []))))),
    check_seq_of (check_erased_map (mul_eraseOff ..) (wsT_noBase _ _) H₁)
      (check_seq_of (check_erased_map (mul_eraseOff ..) (wsT_noBase _ _) H₁)
        (check_seq_of (check_seq_of (windowTwo_check (exp2S n) expWords)
            (check_seq_of rfl (check_seq_of (windowTwo_check (expS n) expWords) rfl)))
          (check_seq_of (check_erased_map (scan_eraseOff n) (wsT_noBase _ _) H₂)
            (check_seq_of (check_erased_map (mul_eraseOff ..) (wsT_noBase _ _) H₁) ?_))))⟩
  rfl

/-- The product of two powers, from the working space's base alone. -/
theorem exponentiate2_relCT (n expWords : Nat) :
    RelCT isa (VG.Arm.Taint.Agree (wsT false false)) (exponentiate2 umaal n expWords)
      (VG.Arm.Taint.Agree (wsT false false)) := by
  obtain ⟨h₁, H₁⟩ := mul_check (umaal := umaal) false false
  obtain ⟨h₂, H₂⟩ := tableFill_check (umaal := umaal) n tableOps
  obtain ⟨h₃, H₃⟩ := windowStep2_check (umaal := umaal) n expWords
  obtain ⟨h₄, H₄⟩ : ∃ h, (VG.Taint.check taintU (wsT false true) (mul umaal eraseMod 0 0 0 0 0) h).map
      (taintU.le (wsT false false)) = some true := by cases umaal <;> exact ⟨_, by taint_decide⟩
  refine relCT_of_check (h := .seq (wsT false false)
    (.seq (wsT false false) h₁ (.seq (wsT false false) h₁ (.seq (wsT false false) h₁ h₂)))
    (.seq (wsT false false) h₁ (.seq (wsT false true) (.block [])
      (.seq (wsT false true) (.loop (wsT false true) h₃) h₄)))) ?_
  unfold exponentiate2 table2
  refine check_seq_of (check_seq_of (check_erased_map (mul_eraseOff ..) (wsT_noBase _ _) H₁)
    (check_seq_of (check_erased_map (mul_eraseOff ..) (wsT_noBase _ _) H₁)
      (check_seq_of (check_erased_map (mul_eraseOff ..) (wsT_noBase _ _) H₁) H₂))) ?_
  refine check_seq_of (check_erased_map (mul_eraseOff ..) (wsT_noBase _ _) H₁) ?_
  refine check_seq_of (check_erased_map (c₀ := .block [.movw .lr 0]) rfl (wsT_noBase _ _) rfl) ?_
  refine check_seq_of (check_loop_of rfl H₃) ?_
  exact check_erased_map (mul_eraseOff ..) (wsT_noBase _ _) H₄

end VG.Proof.Mont.Arm.Dyn
