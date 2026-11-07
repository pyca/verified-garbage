module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
public import VerifiedGarbage.Impl.Ffdh.X86_64.Domain
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Bignum.X86_64.Template
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
meta import VerifiedGarbage.Impl.Ffdh.X86_64.Domain
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.Bignum.X86_64.Template

/-!
# FFDH's exponentiation on x86-64, as its callers take it

An `ExpImpl` is an exponentiation of FFDH's domain operations: its code for
a multiplication `mul` (`Domain.pow`'s `ex`), the `CrtExpL` its proofs take,
and what their templates need of its code: that it inlines with `mul`, never
writes `rsp`, loads MXCSR only to restore it (`ctlOk`), and is constant
time, for the exponents' slots of the domain operations (`Slots`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum.X86_64

/-- The exponents' slots of the domain operations. -/
def Slots (sp sl : Nat) : Prop := (sp = sX ∧ sl = sXl) ∨ (sp = sEp ∧ sl = sEl)

/-- An exponentiation of the domain operations. -/
structure ExpImpl where
  code : (Nat → Nat → Nat → Prog isa) → Nat → Nat → List (Prog isa)
  E : (M : Mont) → CrtExpL M
  code_eq : ∀ M, (E M).code = code M.mm
  inline : ∀ mul sp sl, Slots sp sl →
    @List.map (Code Instr Cond) (Prog isa) (@Code.inline Instr Cond) (code mul sp sl) =
      code (fun o a b => (mul o a b).inline) sp sl
  inlineOk : ∀ mul, (∀ o a b, (mul o a b).InlineOk = true) → ∀ sp sl, Slots sp sl →
    (code mul sp sl).all Code.InlineOk = true
  spSafe : ∀ mul, (∀ o a b, (mul o a b).allInstrs (fun i => !isa.writesSp i) = true) → ∀ sp sl, Slots sp sl →
    (code mul sp sl).all (fun c => c.allInstrs (fun i => !isa.writesSp i)) = true
  ctl : ∀ mul, (∀ o a b, (mul o a b).allInstrs (fun i => !loadsMxcsr i) = true) → ∀ sp sl, Slots sp sl →
    (code mul sp sl).all ctlOk = true
  ctX : ∀ M, ExpCTL (E M) sX sXl
  ctE : ∀ M, ExpCTL (E M) sEp sEl
  suffix : String
  features : List String

/-! ## What the templates' proofs use -/

theorem all_seqs (p : Instr → Bool) (l : List (Prog isa)) :
    (seqs l).allInstrs p = l.all (fun c => c.allInstrs p) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => simp only [seqs, List.all_cons, List.all_nil, Bool.and_true]
    | cons b l => simp only [seqs, Code.allInstrs, List.all_cons] at ih ⊢; rw [ih]

theorem i_seq (p : Instr → Bool) (a b : Prog isa) :
    (Code.seq a b).allInstrs p = (a.allInstrs p && b.allInstrs p) := rfl
theorem i_ite (p : Instr → Bool) (c : Cond) (a b : Prog isa) :
    (Code.ite c a b).allInstrs p = (a.allInstrs p && b.allInstrs p) := rfl
theorem i_loop (p : Instr → Bool) (a : Prog isa) (c : Cond) :
    (Code.loop a c).allInstrs p = a.allInstrs p := rfl
theorem i_empty (p : Instr → Bool) :
    (Code.block ([] : List Instr) : Prog isa).allInstrs p = true := rfl

theorem k_seq (a b : Prog isa) : (Code.seq a b).InlineOk = (a.InlineOk && b.InlineOk) := rfl
theorem k_ite (c : Cond) (a b : Prog isa) : (Code.ite c a b).InlineOk = (a.InlineOk && b.InlineOk) := rfl
theorem k_loop (a : Prog isa) (c : Cond) : (Code.loop a c).InlineOk = a.InlineOk := rfl
theorem k_empty : (Code.block ([] : List Instr) : Prog isa).InlineOk = true := rfl

/-- `ctlOk` of each of a list from its instructions. -/
theorem all_ctl_of {l : List (Prog isa)} (h : l.all (fun c => c.allInstrs (fun i => !loadsMxcsr i)) = true) :
    l.all ctlOk = true :=
  List.all_eq_true.mpr fun c hc => ctlOk_of_allInstrs (List.all_eq_true.mp h c hc)

/-- One part of a conjunction, instruction by instruction. -/
theorem all_and_left {l : List (Prog isa)} {p q : Instr → Bool}
    (h : l.all (fun c => c.allInstrs (fun i => p i && q i)) = true) : l.all (fun c => c.allInstrs p) = true :=
  List.all_eq_true.mpr fun c hc => by
    have := List.all_eq_true.mp h c hc
    rw [Code.allInstrs_eq] at this ⊢
    exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp this i hi)).1

theorem all_and_right {l : List (Prog isa)} {p q : Instr → Bool}
    (h : l.all (fun c => c.allInstrs (fun i => p i && q i)) = true) : l.all (fun c => c.allInstrs q) = true :=
  List.all_eq_true.mpr fun c hc => by
    have := List.all_eq_true.mp h c hc
    rw [Code.allInstrs_eq] at this ⊢
    exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp this i hi)).2

theorem mul_and_left {mul : Nat → Nat → Nat → Prog isa} {p q : Instr → Bool}
    (h : ∀ o a b, (mul o a b).allInstrs (fun i => p i && q i) = true) : ∀ o a b, (mul o a b).allInstrs p = true :=
  fun o a b => by
    have := h o a b
    rw [Code.allInstrs_eq] at this ⊢
    exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp this i hi)).1

theorem mul_and_right {mul : Nat → Nat → Nat → Prog isa} {p q : Instr → Bool}
    (h : ∀ o a b, (mul o a b).allInstrs (fun i => p i && q i) = true) : ∀ o a b, (mul o a b).allInstrs q = true :=
  fun o a b => by
    have := h o a b
    rw [Code.allInstrs_eq] at this ⊢
    exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp this i hi)).2

theorem ctlOk_seqs_of {l : List (Prog isa)} (h : l.all ctlOk = true) : ctlOk (seqs l) = true := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases l with
    | nil => exact h.1
    | cons b l => exact ctlOk_seq_of h.1 (ih h.2)

/-! ## The baseline: `Crt.expLoop` -/

private theorem base_instrs (p : Instr → Bool) (mul : Nat → Nat → Nat → Prog isa) {sp sl : Nat}
    (hp : (Crt.expLoop (fun _ _ _ => .block []) Crt.tabSelect sp sl).all (fun c => c.allInstrs p) = true)
    (hm : ∀ o a b, (mul o a b).allInstrs p = true) :
    (Crt.expLoop mul Crt.tabSelect sp sl).all (fun c => c.allInstrs p) = true := by
  unfold Crt.expLoop Crt.expLoopS Crt.expWin Crt.tabBuild Crt.tabBuildN at hp ⊢
  repeat' first
    | rw [all_seqs] at *
    | rw [i_seq] at *
    | rw [i_ite] at *
    | rw [i_loop] at *
    | rw [List.all_append] at *
    | rw [List.all_cons] at *
  repeat' rw [hm]
  repeat' rw [i_empty] at hp
  exact hp

private theorem base_inlineOk (mul : Nat → Nat → Nat → Prog isa) {sp sl : Nat}
    (hp : (Crt.expLoop (fun _ _ _ => .block []) Crt.tabSelect sp sl).all Code.InlineOk = true)
    (hm : ∀ o a b, (mul o a b).InlineOk = true) :
    (Crt.expLoop mul Crt.tabSelect sp sl).all Code.InlineOk = true := by
  unfold Crt.expLoop Crt.expLoopS Crt.expWin Crt.tabBuild Crt.tabBuildN at hp ⊢
  repeat' first
    | rw [inlineOk_seqs] at *
    | rw [k_seq] at *
    | rw [k_ite] at *
    | rw [k_loop] at *
    | rw [List.all_append] at *
    | rw [List.all_cons] at *
  repeat' rw [hm]
  repeat' rw [k_empty] at hp
  exact hp

theorem base_ctX (M : Mont) : ExpCTL (CrtExpL.w4 M) sX sXl :=
  two_map id (fun _ _ h => h.1) (crtExpLoop_ct M CrtSel.sse CrtSel.sse_ct (by taint_decide))

theorem base_ctE (M : Mont) : ExpCTL (CrtExpL.w4 M) sEp sEl :=
  two_map id (fun _ _ h => h.1) (crtExpLoop_ct M CrtSel.sse CrtSel.sse_ct (by taint_decide))

/-- `Crt.expLoop`, by windows of 4 bits. -/
def ExpImpl.base : ExpImpl where
  code mul := Crt.expLoop mul Crt.tabSelect
  E := CrtExpL.w4
  code_eq _ := rfl
  inline mul sp sl hs := by
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [Crt.expLoop, Crt.expLoopS, Crt.expWin, Crt.tabBuild, Crt.tabBuildN, List.map_append,
        List.map_cons, List.map_nil, Code.inline, inline_seqs]
      simp (disch := decide) only [inline_of_noCalls, map_inline_of_noCalls]
  inlineOk mul hm sp sl hs := by
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact base_inlineOk mul (by decide +kernel) hm
  spSafe mul hm sp sl hs := by
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact base_instrs _ mul (by decide +kernel) hm
  ctl mul hm sp sl hs := by
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact all_ctl_of (base_instrs _ mul (by decide +kernel) hm)
  ctX := base_ctX
  ctE := base_ctE
  suffix := ""
  features := []

end VG.Proof.Ffdh.X86_64
