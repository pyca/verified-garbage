module

public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Contract
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Impl.MillerRabin.X86_64.Round
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallCorrect
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallCT
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallTemplate
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineRel
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr

/-! # Shared round implementations for generic RSA and FFDH callers -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.MillerRabin.X86_64

/-- The arithmetic a backend gives the round's callers, and the round they
inline: Montgomery multiplication by `mm`, which inlines to `mont.mm`. -/
structure RoundArith where
  mont : Mont
  /-- Arithmetic specialized for callers that inline their multiplication.
  The callable kernel may dispatch on operand indices at run time; this
  form can select that operation while constructing the caller. -/
  inlineMont : Mont := mont
  inlineDepth : ∀ o a b, (inlineMont.mm o a b).x86_64Depth = 0
  inlineSafe : ∀ o a b, (inlineMont.mm o a b).allInstrs
    (fun i => !loadsMxcsr i && !isa.writesSp i) = true
  /-- Montgomery multiplication as the round and its callers emit it: calls
  of a function, which inline to `mont.mm` (`Verified.of_inline`), or
  `mont.mm`. -/
  mm : Nat → Nat → Nat → Prog isa
  mmOk : ∀ o a b, (mm o a b).InlineOk = true
  mmInline : ∀ o a b, (mm o a b).inline = mont.mm o a b
  mxSafe : (round mm).allInstrs (fun i => !loadsMxcsr i) = true
  arithDepth : ∀ o a b, (mont.mm o a b).x86_64Depth = 0
  arithSafe : ∀ o a b, (mont.mm o a b).allInstrs (fun i => !loadsMxcsr i && !isa.writesSp i) = true

theorem RoundArith.body_inlineOk (v : RoundArith) : (body v.mm).InlineOk = true :=
  VG.Proof.MillerRabin.X86_64.body_inlineOk v.mm v.mmOk

theorem RoundArith.body_inline (v : RoundArith) : (body v.mm).inline = body v.mont.mm := by
  rw [VG.Proof.MillerRabin.X86_64.body_inline]
  simp only [v.mmInline]

theorem RoundArith.no_mx_load (v : RoundArith) : ∀ i ∈ instrs (round v.mm), loadsMxcsr i = false := by
  have h := v.mxSafe
  rw [Code.allInstrs_eq] at h
  intro i hi
  have := List.all_eq_true.mp h i hi
  simpa only [Bool.not_eq_true'] using this

/-- `round v.mm` is correct. -/
theorem RoundArith.round_correct (v : RoundArith) (s : State) (h : roundPre s) :
    ∃ tr t, Exec isa (round v.mm) s tr t ∧ abiPreserved s t ∧ roundPost s t :=
  round_call_correct v.mont v.body_inlineOk v.body_inline v.no_mx_load s h

theorem RoundArith.round_ct (v : RoundArith) : ConstantTime isa roundPre roundPub (round v.mm) :=
  round_call_ct v.mont v.body_inlineOk v.body_inline

/-- Code that never loads MXCSR satisfies `ctlC`. -/
theorem ctlC_of_noLoad {c : Prog isa} (h : c.allInstrs (fun i => !loadsMxcsr i) = true) : ctlC c = true := by
  induction c with
  | block is =>
    rw [Code.allInstrs_eq] at h
    exact (KList.all_eq _ _).trans h
  | seq _ _ iha ihb =>
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [ctlC, iha h.1, ihb h.2, Bool.and_self]
  | ite _ _ _ iht ihe =>
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [ctlC, iht h.1, ihe h.2, Bool.and_self]
  | loop _ _ ih => exact ih h
  | call _ _ _ => exact ctlOk_of_noLoad h
  | frame _ _ _ ih =>
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [ctlC, h.1.1, h.2, ih h.1.2, Bool.and_self]
  | icall _ _ _ _ _ ihn =>
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [ctlC, h.1.1, ctlOk_of_noLoad h.1.2, ihn h.2, Bool.and_self]

/-- `ctlC` of a sequence. -/
theorem ctlC_seqs (l : List (Prog isa)) : ctlC (VG.Impl.Bignum.X86_64.seqs l) = l.all ctlC := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => simp only [VG.Impl.Bignum.X86_64.seqs, List.all_cons, List.all_nil, Bool.and_true]
    | cons b l => simp only [VG.Impl.Bignum.X86_64.seqs, ctlC, List.all_cons] at ih ⊢; rw [ih]

theorem ctlC_seq (a b : Prog isa) : ctlC (.seq a b) = (ctlC a && ctlC b) := rfl
theorem ctlC_ite (c : Cond) (a b : Prog isa) : ctlC (.ite c a b) = (ctlC a && ctlC b) := rfl
theorem ctlC_loop (a : Prog isa) (c : Cond) : ctlC (.loop a c) = ctlC a := rfl
theorem ctlC_call (n : String) (b : Prog isa) : ctlC (.call n b) = ctlOk b := rfl
theorem ctlC_empty : ctlC (.block ([] : List Instr) : Prog isa) = true := rfl

/-- A backend: its arithmetic, and the round as the emitter emits it
(`code`, `round mm` unless the backend runs a round of its own), which the
callers call (`RoundImpl.name`) under the round's contract. The round may
load MXCSR only where it restores it (`ctlOk`). -/
structure RoundImpl extends RoundArith where
  code : Prog isa
  spSafe : code.all (fun i => !isa.writesSp i) = true
  depth : code.x86_64Depth ≤ 120
  ctl : ctlOk code = true
  correct : ∀ s, roundPre s → ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ roundPost s t
  ct : ConstantTime isa roundPre roundPub code
  suffix : String
  features : List String
  /-- The CPU features of the arithmetic alone, for callers that never call
  the round. -/
  arithFeatures : List String

/-- The backend whose round is `round mm`. -/
def RoundImpl.ofArith (a : RoundArith) (spSafe : (round a.mm).all (fun i => !isa.writesSp i) = true)
    (depth : (round a.mm).x86_64Depth ≤ 120) (suffix : String) (features : List String) : RoundImpl :=
  { a with
    code := round a.mm
    spSafe := spSafe
    depth := depth
    ctl := ctlOk_of_noLoad a.mxSafe
    correct := a.round_correct
    ct := a.round_ct
    suffix := suffix
    features := features
    arithFeatures := features }

def RoundImpl.name (v : RoundImpl) : String :=
  "vg_miller_rabin_round" ++ v.suffix

theorem RoundImpl.body_inlineOk (v : RoundImpl) : (body v.mm).InlineOk = true := v.toRoundArith.body_inlineOk

theorem RoundImpl.body_inline (v : RoundImpl) : (body v.mm).inline = body v.mont.mm := v.toRoundArith.body_inline

end VG.Proof.MillerRabin.X86_64
