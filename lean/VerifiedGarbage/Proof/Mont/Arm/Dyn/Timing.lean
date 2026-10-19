module

public import VerifiedGarbage.Impl.Mont.Arm.Context
public import VerifiedGarbage.Proof.Framework.Arm.TaintErase
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Impl.Mont.Arm.Context
meta import VerifiedGarbage.Proof.Framework.Arm.TaintErase
meta import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Arm.Target

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: constant time

Only the working space's base `r12` is public on entry (`wsT`), and
optionally `r11` and `lr`, which the arithmetic leaves alone, for its
callers' loops. Every address is `r12` plus an offset, or a pointer moved by
public steps, and every branch compares pointers or counts: the analysis
of an operation's code without its offsets and `movw` immediates
(`Code.eraseOff`) is the analysis of the code itself (`check_eraseOff`),
and that code is the same for every modulus and layout, so each check below
evaluates the analysis of one instance (`erased_relCT`). The exponentiation's
shift has a word a step (`shiftWords_check`), checked by induction.
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic

/-- The public registers: the working space's base, and `r11` and `lr` if `p` and `q`. -/
def wsRegs (p q : Bool) : List Reg := .r12 :: ((if p then [.r11] else []) ++ (if q then [.lr] else []))

def wsT (p q : Bool) : taint.T := Taint.ofRegs (wsRegs p q)

theorem wsT_noBase (p q : Bool) : Taint.NoBase (wsT p q) := Taint.noBase_ofRegs _

/-- A modulus whose code stands for every modulus's, once erased. -/
def eraseMod : Mod := { n := 1, mo := 0, tmp := 0, minv := 0 }

/-- A program whose code is `c₀`'s but for offsets and immediates, from the
analysis of `c₀`. -/
theorem erased_relCT {c c₀ : Prog isa} {τ σ : taint.T} (h : VG.Taint.Hint taint.T)
    (e : Code.eraseOff c = Code.eraseOff c₀) (hn : Taint.NoBase τ)
    (L : (VG.Taint.check taint τ c₀ h).map (taint.le σ) = some true) :
    RelCT isa (VG.Arm.Taint.Agree τ) c (VG.Arm.Taint.Agree σ) := by
  obtain ⟨τ', H, L'⟩ := Option.map_eq_some_iff.mp L
  have H' : VG.Taint.check taint τ c h = some τ' := by
    rw [← Taint.check_eraseOff c h hn, e, Taint.check_eraseOff c₀ h hn, H]
  intro s t tr ur sf tf A E F
  obtain ⟨T, B⟩ := VG.Taint.check_sound H' A E F
  exact ⟨T, taint.le_sound L' B⟩

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
    Code.eraseOff (mul M inv acc o a b) = Code.eraseOff (mul eraseMod 0 0 0 0 0) := rfl

theorem selectW_eraseOff (k src tmp o : Nat) :
    Code.eraseOff (selectW k src tmp o) = Code.eraseOff (selectW 1 0 0 0) := rfl

theorem one_eraseOff (n out : Nat) : Code.eraseOff (one n out) = Code.eraseOff (one 1 0) := rfl

theorem powerTwo_eraseOff (M : Mod) (acc out bits : Nat) :
    Code.eraseOff (powerTwo M acc out bits) = Code.eraseOff (powerTwo eraseMod 0 0 0) := rfl

theorem setupInverse_eraseOff (mo : Nat) :
    Code.eraseOff (@Code.block Instr Cond (setupInverse mo)) =
      Code.eraseOff (@Code.block Instr Cond (setupInverse 0)) := rfl

theorem contextSetup_eraseOff (n : Nat) : Code.eraseOff (contextSetup n) = Code.eraseOff (contextSetup 1) := by
  simp only [contextSetup, eraseOff_seq, setupInverse_eraseOff, one_eraseOff, powerTwo_eraseOff]

theorem exponentProduct_eraseOff (n : Nat) :
    Code.eraseOff (exponentProduct n) = Code.eraseOff (exponentProduct 1) := by
  simp only [exponentProduct, eraseOff_seq, mul_eraseOff, selectW_eraseOff, exponentMask, eraseOff_ptr]

/-! ## The operations -/

theorem mul_check (p q : Bool) :
    ∃ h, (VG.Taint.check taint (wsT p q) (mul eraseMod 0 0 0 0 0) h).map (taint.le (wsT p q)) = some true := by
  cases p <;> cases q <;> exact ⟨_, by taint_decide⟩

theorem mul_relCT (p q : Bool) (M : Mod) (inv acc o a b : Nat) :
    RelCT isa (VG.Arm.Taint.Agree (wsT p q)) (mul M inv acc o a b) (VG.Arm.Taint.Agree (wsT p q)) := by
  obtain ⟨h, H⟩ := mul_check p q
  exact erased_relCT h (mul_eraseOff ..) (wsT_noBase p q) H

theorem addD_relCT (p q : Bool) (M : Mod) (acc o a b : Nat) :
    RelCT isa (VG.Arm.Taint.Agree (wsT p q)) (addD M acc o a b) (VG.Arm.Taint.Agree (wsT p q)) := by
  obtain ⟨h, H⟩ : ∃ h, (VG.Taint.check taint (wsT p q) (addD eraseMod 0 0 0 0) h).map (taint.le (wsT p q)) =
      some true := by cases p <;> cases q <;> exact ⟨_, by taint_decide⟩
  exact erased_relCT h (addD_eraseOff ..) (wsT_noBase p q) H

theorem zeros_relCT (p q : Bool) (k o : Nat) :
    RelCT isa (VG.Arm.Taint.Agree (wsT p q)) (zeros k o) (VG.Arm.Taint.Agree (wsT p q)) := by
  obtain ⟨h, H⟩ : ∃ h, (VG.Taint.check taint (wsT p q) (zeros 1 0) h).map (taint.le (wsT p q)) = some true := by
    cases p <;> cases q <;> exact ⟨_, by taint_decide⟩
  exact erased_relCT h (zeros_eraseOff ..) (wsT_noBase p q) H

theorem selectW_check (p q : Bool) :
    ∃ h, (VG.Taint.check taint (wsT p q) (selectW 1 0 0 0) h).map (taint.le (wsT p q)) = some true := by
  cases p <;> cases q <;> exact ⟨_, by taint_decide⟩

theorem selectW_relCT (p q : Bool) (k src tmp o : Nat) :
    RelCT isa (VG.Arm.Taint.Agree (wsT p q)) (selectW k src tmp o) (VG.Arm.Taint.Agree (wsT p q)) := by
  obtain ⟨h, H⟩ := selectW_check p q
  exact erased_relCT h (selectW_eraseOff ..) (wsT_noBase p q) H

/-- The context's setup, whose doublings count in `lr`. -/
theorem contextSetup_relCT (p q : Bool) (n : Nat) :
    RelCT isa (VG.Arm.Taint.Agree (wsT p q)) (contextSetup n) (VG.Arm.Taint.Agree (wsT p q)) := by
  obtain ⟨h, H⟩ : ∃ h, (VG.Taint.check taint (wsT p q) (contextSetup 1) h).map (taint.le (wsT p q)) =
      some true := by
    cases p <;> cases q <;> exact ⟨_, by taint_decide⟩
  exact erased_relCT h (contextSetup_eraseOff n) (wsT_noBase p q) H

/-! ## The exponentiation -/

/-- A sequence whose second part's analysis satisfies `P`. -/
theorem check_seq_of {τ mid : taint.T} {a b : Prog isa} {ha hb : VG.Taint.Hint taint.T} {P : taint.T → Bool}
    (h₁ : (VG.Taint.check taint τ a ha).map (taint.le mid) = some true)
    (h₂ : (VG.Taint.check taint mid b hb).map P = some true) :
    (VG.Taint.check taint τ (.seq a b) (.seq mid ha hb)).map P = some true := by
  obtain ⟨u, H, L⟩ := Option.map_eq_some_iff.mp h₁
  change ((VG.Taint.check taint τ a ha).bind fun τ' => if taint.le mid τ' then _ else none).map P = _
  rw [H, Option.bind_some, L, ite_eq_left rfl]
  exact h₂

theorem check_erased {c c₀ : Prog isa} {τ : taint.T} (h : VG.Taint.Hint taint.T)
    (e : Code.eraseOff c = Code.eraseOff c₀) (hn : Taint.NoBase τ) :
    VG.Taint.check taint τ c h = VG.Taint.check taint τ c₀ h := by
  rw [← Taint.check_eraseOff c h hn, e, Taint.check_eraseOff c₀ h hn]

theorem checkBlock_append {M : ISA} (A : VG.Taint M) (τ : A.T) (a b : List M.Instr) :
    A.checkBlock τ (a ++ b) = (A.checkBlock τ a).bind (A.checkBlock · b) := by
  induction a generalizing τ with
  | nil => rfl
  | cons i is ih =>
    change (A.step τ i).bind (fun t => A.checkBlock t (is ++ b)) =
      ((A.step τ i).bind (fun t => A.checkBlock t is)).bind (A.checkBlock · b)
    rw [Option.bind_assoc]
    simp only [ih]


/-- The taint of the shift's words: `r1` public too. -/
def shiftT (p : Bool) : taint.T := Taint.ofRegs (.r1 :: wsRegs p true)

theorem shiftT_noBase (p : Bool) : Taint.NoBase (shiftT p) := Taint.noBase_ofRegs _

/-- A word of the shift, which leaves its taint as it was. -/
theorem shiftWord_check (p : Bool) (k j : Nat) :
    taint.checkBlock (shiftT p) (([.ldr .r4 .r1 (4 * j), .mov .r4 (.shifted .r4 .lsr 1)] : List Instr) ++
      ((if k = 0 then [] else [.ldr .r5 .r1 (4 * j + 4), .mov .r5 (.shifted .r5 .lsl 31),
        .dp .orr .r4 .r4 (.reg .r5)] : List Instr) ++ ([.str .r4 .r1 (4 * j)] : List Instr))) = some (shiftT p) := by
  rw [← Taint.checkBlock_eraseOff (shiftT_noBase p)]
  cases k <;> cases p <;> rfl

theorem shiftWords_check (p : Bool) : ∀ k j, taint.checkBlock (shiftT p) (shiftWords k j) = some (shiftT p)
  | 0, _ => rfl
  | k + 1, j => by
    have e : shiftWords (k + 1) j = (([.ldr .r4 .r1 (4 * j), .mov .r4 (.shifted .r4 .lsr 1)] : List Instr) ++
        ((if k = 0 then [] else [.ldr .r5 .r1 (4 * j + 4), .mov .r5 (.shifted .r5 .lsl 31),
          .dp .orr .r4 .r4 (.reg .r5)] : List Instr) ++ ([.str .r4 .r1 (4 * j)] : List Instr))) ++
          shiftWords k (j + 1) := by
      rw [shiftWords]; simp only [List.append_assoc]
    rw [e, checkBlock_append taint, shiftWord_check, Option.bind_some, shiftWords_check p k (j + 1)]

theorem shiftExponent_check (p : Bool) (n expWords : Nat) :
    taint.checkBlock (wsT p true) (shiftExponent n expWords) = some (shiftT p) := by
  rw [shiftExponent, checkBlock_append taint,
    show taint.checkBlock (wsT p true) (ptr .r1 (expS n)) = some (shiftT p) by
      rw [← Taint.checkBlock_eraseOff (wsT_noBase p true)]; cases p <;> rfl,
    Option.bind_some, shiftWords_check]

theorem check_erased_map {c c₀ : Prog isa} {τ : taint.T} {h : VG.Taint.Hint taint.T} {P : taint.T → Bool}
    (e : Code.eraseOff c = Code.eraseOff c₀) (hn : Taint.NoBase τ)
    (L : (VG.Taint.check taint τ c₀ h).map P = some true) : (VG.Taint.check taint τ c h).map P = some true := by
  rw [check_erased h e hn]; exact L

theorem check_loop_of {τ σ : taint.T} {body : Prog isa} {c : Cond} {h : VG.Taint.Hint taint.T}
    (hσ : taint.le σ τ = true)
    (hb : (VG.Taint.check taint σ body h).map (fun σ' => taint.le σ σ' && taint.condPub σ' c) = some true) :
    (VG.Taint.check taint τ (.loop body c) (.loop σ h)).map (taint.le σ) = some true := by
  obtain ⟨σ', H, L⟩ := Option.map_eq_some_iff.mp hb
  change (if taint.le σ τ then (VG.Taint.check taint σ body h).bind
    (fun σ' => if taint.le σ σ' && taint.condPub σ' c then some σ' else none) else none).map _ = _
  rw [hσ, ite_eq_left rfl, H, Option.bind_some, L, ite_eq_left rfl]
  simp only [Option.map_some, Option.some.injEq]
  simp only [Bool.and_eq_true] at L
  exact L.1

/-- Constant time from a check. -/
theorem relCT_of_check {c : Prog isa} {τ σ : taint.T} {h : VG.Taint.Hint taint.T}
    (L : (VG.Taint.check taint τ c h).map (taint.le σ) = some true) :
    RelCT isa (VG.Arm.Taint.Agree τ) c (VG.Arm.Taint.Agree σ) := by
  obtain ⟨τ', H, L'⟩ := Option.map_eq_some_iff.mp L
  intro s t tr ur sf tf A E F
  obtain ⟨T, B⟩ := VG.Taint.check_sound H A E F
  exact ⟨T, taint.le_sound L' B⟩

theorem exponentProduct_check (p : Bool) (n : Nat) :
    ∃ h, (VG.Taint.check taint (wsT p true) (exponentProduct n) h).map (taint.le (wsT p true)) = some true := by
  obtain ⟨h, H⟩ : ∃ h, (VG.Taint.check taint (wsT p true) (exponentProduct 1) h).map (taint.le (wsT p true)) =
      some true := by cases p <;> exact ⟨_, by taint_decide⟩
  exact ⟨h, check_erased_map (exponentProduct_eraseOff n) (wsT_noBase _ _) H⟩

theorem exponentStep_check (p : Bool) (n expWords : Nat) :
    ∃ h, (VG.Taint.check taint (wsT p true) (exponentStep n expWords) h).map
      (fun σ' => taint.le (wsT p true) σ' && taint.condPub σ' .ne) = some true := by
  obtain ⟨h₁, H₁⟩ := exponentProduct_check p n
  obtain ⟨h₂, H₂⟩ := mul_check p true
  unfold exponentStep exponentBody
  refine ⟨.seq (wsT p true) (.seq (wsT p true) h₁ (.seq (wsT p true) h₂ (.block []))) (.block []),
    check_seq_of (check_seq_of H₁ (check_seq_of (check_erased_map (mul_eraseOff ..) (wsT_noBase _ _) H₂) ?_)) ?_⟩
  · change (taint.checkBlock (wsT p true) (shiftExponent n expWords)).map _ = _
    rw [shiftExponent_check]; cases p <;> rfl
  · cases p <;> rfl

theorem exponentiate_relCT (p q : Bool) (n expWords : Nat) :
    RelCT isa (VG.Arm.Taint.Agree (wsT p q)) (exponentiate n expWords) (VG.Arm.Taint.Agree (wsT p q)) := by
  obtain ⟨h₁, H₁⟩ := mul_check p q
  obtain ⟨h₂, H₂⟩ := exponentStep_check p n expWords
  obtain ⟨h₃, H₃⟩ : ∃ h, (VG.Taint.check taint (wsT p true) (mul eraseMod 0 0 0 0 0) h).map
      (taint.le (wsT p q)) = some true := by cases p <;> cases q <;> exact ⟨_, by taint_decide⟩
  refine relCT_of_check (h := .seq (wsT p q) h₁ (.seq (wsT p q) h₁ (.seq (wsT p true) (.block [])
    (.seq (wsT p true) (.loop (wsT p true) h₂) h₃)))) ?_
  unfold exponentiate
  refine check_seq_of (check_erased_map (mul_eraseOff ..) (wsT_noBase _ _) H₁) ?_
  refine check_seq_of (check_erased_map (mul_eraseOff ..) (wsT_noBase _ _) H₁) ?_
  refine check_seq_of (check_erased_map (c₀ := .block [.movw .lr 0]) rfl (wsT_noBase _ _)
    (by cases p <;> cases q <;> rfl)) ?_
  refine check_seq_of (check_loop_of (by cases p <;> rfl) H₂) ?_
  exact check_erased_map (mul_eraseOff ..) (wsT_noBase _ _) H₃

end VG.Proof.Mont.Arm.Dyn
