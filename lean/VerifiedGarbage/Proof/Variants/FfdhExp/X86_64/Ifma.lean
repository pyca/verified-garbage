module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ExpImpl
import VerifiedGarbage.Proof.Framework.X86_64.ScrubFillG
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Ffdh.X86_64.Ifma.CT
import VerifiedGarbage.Proof.Bignum.X86_64.Template
import VerifiedGarbage.Proof.Ffdh.X86_64.Ifma.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.InstrBits
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ExpImpl
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Ifma.CT
meta import VerifiedGarbage.Proof.Bignum.X86_64.Template
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Ifma.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.InstrBits
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.ConvLit
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.ConvLit

/-!
# FFDH's exponentiation with AVX512_IFMA on x86-64

`Ifma.code` (`Proof/Ffdh/X86_64/Ifma/`): one lane of `CrtIfma`'s
exponentiation for the 2048-, 3072- and 4096-bit groups, else `Crt.expLoop`.
-/

@[expose] public section

namespace VG.Proof.Variants.FfdhExp.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum.X86_64 VG.Proof.Ffdh.X86_64
open VG.Proof.Bignum.X86_64 (inlineOk_seqs inline_seqs inline_of_noCalls map_inline_of_noCalls)

theorem ifma_ctX (M : Mont) : ExpCTL (Proof.Ffdh.X86_64.Ifma.expL M) sX sXl :=
  Proof.Ffdh.X86_64.Ifma.expL_ct M (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ (by taint_decide)
    (by taint_decide)

theorem ifma_ctE (M : Mont) : ExpCTL (Proof.Ffdh.X86_64.Ifma.expL M) sEp sEl :=
  Proof.Ffdh.X86_64.Ifma.expL_ct M (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ (by taint_decide)
    (by taint_decide)

theorem ok_seq {a b : Prog isa} (ha : a.InlineOk = true) (hb : b.InlineOk = true) :
    (Code.seq a b).InlineOk = true := (k_seq a b).trans (by rw [ha, hb]; rfl)

theorem ok_ite {c : Cond} {a b : Prog isa} (ha : a.InlineOk = true) (hb : b.InlineOk = true) :
    (Code.ite c a b).InlineOk = true := (k_ite c a b).trans (by rw [ha, hb]; rfl)

theorem in_seq {p : Instr → Bool} {a b : Prog isa} (ha : a.allInstrs p = true) (hb : b.allInstrs p = true) :
    (Code.seq a b).allInstrs p = true := (i_seq p a b).trans (by rw [ha, hb]; rfl)

theorem in_ite {p : Instr → Bool} {c : Cond} {a b : Prog isa} (ha : a.allInstrs p = true)
    (hb : b.allInstrs p = true) : (Code.ite c a b).allInstrs p = true := (i_ite p c a b).trans (by rw [ha, hb]; rfl)

/-- What the callers' templates need of a layout's code, decided for its slots. -/
def LOk (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (sp sl : Nat) : Prop :=
  (VG.Impl.Ffdh.X86_64.Ifma.exp l sp sl).all Code.noCalls = true ∧
    (Code.block (VG.Impl.Ffdh.X86_64.Ifma.fits l sl) : Prog isa).InlineOk = true ∧
    (seqs (VG.Impl.Ffdh.X86_64.Ifma.exp l sp sl)).InlineOk = true ∧
    (Code.block (VG.Impl.Ffdh.X86_64.Ifma.fits l sl) : Prog isa).allInstrs (fun i => !isa.writesSp i) = true ∧
    (seqs (VG.Impl.Ffdh.X86_64.Ifma.exp l sp sl)).allInstrs (fun i => !isa.writesSp i) = true ∧
    ctlOk (Code.block (VG.Impl.Ffdh.X86_64.Ifma.fits l sl) : Prog isa) = true ∧
    ctlOk (seqs (VG.Impl.Ffdh.X86_64.Ifma.exp l sp sl)) = true

/-- `Ifma.exp l sp sl`, unfolded: a statement the kernel evaluates names the
vector code `vec l`, so that it is read from its literal
(`Proof/Ffdh/X86_64/Ifma/Lit.lean`). -/
local macro "expU% " l:term:max sp:term:max sl:term:max : term =>
  `((([Code.block (VG.Impl.Ffdh.X86_64.Ifma.head $l $sl)] : List (Prog isa)) ++ CrtIfma.region $l 0 $sp $sl ++
    ([Code.block (VG.Impl.Ffdh.X86_64.Ifma.bases $l), VG.Impl.Ffdh.X86_64.Ifma.vec $l] : List (Prog isa)) ++
    CrtIfma.result $l 0 ++ ([Code.block (VG.Impl.Ffdh.X86_64.Ifma.tail $l)] : List (Prog isa))))

/-- `LOk`, from what the kernel evaluates of a layout's code: the tests of its
instructions in one walk, with one match for each instruction
(`Proof/Framework/X86_64/InstrBits.lean`). -/
theorem LOk.of_bits {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay} {sp sl : Nat}
    (h : (expU% l sp sl).all Code.noCalls = true ∧
      (Code.block (VG.Impl.Ffdh.X86_64.Ifma.fits l sl) : Prog isa).InlineOkB (bMx + bSp) = true ∧
      (seqs (expU% l sp sl)).InlineOkB (bMx + bSp) = true) : LOk l sp sl :=
  ⟨h.1, Code.inlineOk_of_B h.2.1, Code.inlineOk_of_B h.2.2,
    Code.sp_of_bits rfl (Code.allInstrs_of_inlineOkB h.2.1), Code.sp_of_bits rfl (Code.allInstrs_of_inlineOkB h.2.2),
    ctlOk_of_noLoad (Code.noMx_of_bits rfl (Code.allInstrs_of_inlineOkB h.2.1)),
    ctlOk_of_noLoad (Code.noMx_of_bits rfl (Code.allInstrs_of_inlineOkB h.2.2))⟩

/-- The tests of the three layouts' code, for the slots of both exponents:
in one declaration, so that the kernel evaluates each layout's vector code,
which is the same for both, once. -/
theorem loks :
    ((expU% PubIfma.pay2048 sX sXl).all Code.noCalls = true ∧
      (Code.block (VG.Impl.Ffdh.X86_64.Ifma.fits PubIfma.pay2048 sXl) : Prog isa).InlineOkB (bMx + bSp) = true ∧
      (seqs (expU% PubIfma.pay2048 sX sXl)).InlineOkB (bMx + bSp) = true) ∧
    ((expU% PubIfma.pay3072 sX sXl).all Code.noCalls = true ∧
      (Code.block (VG.Impl.Ffdh.X86_64.Ifma.fits PubIfma.pay3072 sXl) : Prog isa).InlineOkB (bMx + bSp) = true ∧
      (seqs (expU% PubIfma.pay3072 sX sXl)).InlineOkB (bMx + bSp) = true) ∧
    ((expU% PubIfma.pay4096 sX sXl).all Code.noCalls = true ∧
      (Code.block (VG.Impl.Ffdh.X86_64.Ifma.fits PubIfma.pay4096 sXl) : Prog isa).InlineOkB (bMx + bSp) = true ∧
      (seqs (expU% PubIfma.pay4096 sX sXl)).InlineOkB (bMx + bSp) = true) ∧
    ((expU% PubIfma.pay2048 sEp sEl).all Code.noCalls = true ∧
      (Code.block (VG.Impl.Ffdh.X86_64.Ifma.fits PubIfma.pay2048 sEl) : Prog isa).InlineOkB (bMx + bSp) = true ∧
      (seqs (expU% PubIfma.pay2048 sEp sEl)).InlineOkB (bMx + bSp) = true) ∧
    ((expU% PubIfma.pay3072 sEp sEl).all Code.noCalls = true ∧
      (Code.block (VG.Impl.Ffdh.X86_64.Ifma.fits PubIfma.pay3072 sEl) : Prog isa).InlineOkB (bMx + bSp) = true ∧
      (seqs (expU% PubIfma.pay3072 sEp sEl)).InlineOkB (bMx + bSp) = true) ∧
    ((expU% PubIfma.pay4096 sEp sEl).all Code.noCalls = true ∧
      (Code.block (VG.Impl.Ffdh.X86_64.Ifma.fits PubIfma.pay4096 sEl) : Prog isa).InlineOkB (bMx + bSp) = true ∧
      (seqs (expU% PubIfma.pay4096 sEp sEl)).InlineOkB (bMx + bSp) = true) := by
  lit_decide

theorem lok2048X : LOk PubIfma.pay2048 sX sXl := .of_bits loks.1
theorem lok3072X : LOk PubIfma.pay3072 sX sXl := .of_bits loks.2.1
theorem lok4096X : LOk PubIfma.pay4096 sX sXl := .of_bits loks.2.2.1
theorem lok2048E : LOk PubIfma.pay2048 sEp sEl := .of_bits loks.2.2.2.1
theorem lok3072E : LOk PubIfma.pay3072 sEp sEl := .of_bits loks.2.2.2.2.1
theorem lok4096E : LOk PubIfma.pay4096 sEp sEl := .of_bits loks.2.2.2.2.2

theorem lok {sp sl : Nat} (hs : ExpSlots sp sl) :
    LOk PubIfma.pay2048 sp sl ∧ LOk PubIfma.pay3072 sp sl ∧ LOk PubIfma.pay4096 sp sl := by
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨lok2048X, lok3072X, lok4096X⟩
  · exact ⟨lok2048E, lok3072E, lok4096E⟩

/-- Each layout's vector code touches no `rsp`, so that it can be called
(`Code.InlineOk`). -/
theorem vecs_free : (VG.Impl.Ffdh.X86_64.Ifma.vec PubIfma.pay2048).allInstrs (hasBits bFree) = true ∧
    (VG.Impl.Ffdh.X86_64.Ifma.vec PubIfma.pay3072).allInstrs (hasBits bFree) = true ∧
    (VG.Impl.Ffdh.X86_64.Ifma.vec PubIfma.pay4096).allInstrs (hasBits bFree) = true := by
  lit_decide

/-- `expC` inlines to `exp`. -/
theorem expC_inline {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay} {sp sl : Nat} (n : String)
    (h : (VG.Impl.Ffdh.X86_64.Ifma.exp l sp sl).all Code.noCalls = true) :
    @List.map (Code Instr Cond) (Prog isa) (@Code.inline Instr Cond) (VG.Impl.Ffdh.X86_64.Ifma.expC l n sp sl) =
      VG.Impl.Ffdh.X86_64.Ifma.exp l sp sl := by
  unfold VG.Impl.Ffdh.X86_64.Ifma.exp at h ⊢
  unfold VG.Impl.Ffdh.X86_64.Ifma.expC
  simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_eq_true, and_true] at h
  simp only [List.map_append, List.map_cons, List.map_nil, Code.inline, map_inline_of_noCalls h.1.1.1.2,
    map_inline_of_noCalls h.1.2]

/-- `expC` can be inlined where `exp` can and its vector code touches no `rsp`. -/
theorem expC_inlineOk {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay} {sp sl : Nat} (n : String)
    (h : (VG.Impl.Ffdh.X86_64.Ifma.exp l sp sl).all Code.noCalls = true)
    (hk : (seqs (VG.Impl.Ffdh.X86_64.Ifma.exp l sp sl)).InlineOk = true)
    (hv : (VG.Impl.Ffdh.X86_64.Ifma.vec l).allInstrs (hasBits bFree) = true) :
    (seqs (VG.Impl.Ffdh.X86_64.Ifma.expC l n sp sl)).InlineOk = true := by
  rw [inlineOk_seqs] at hk ⊢
  unfold VG.Impl.Ffdh.X86_64.Ifma.exp at h hk
  unfold VG.Impl.Ffdh.X86_64.Ifma.expC
  simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_eq_true, and_true] at h hk ⊢
  refine ⟨⟨⟨hk.1.1.1, hk.1.1.2.1, ?_⟩, hk.1.2⟩, hk.2⟩
  simp only [Code.InlineOk, Bool.and_eq_true]
  exact ⟨h.1.1.2.2, Code.rspFree_of_bits rfl hv⟩

theorem code_eq (mul : Nat → Nat → Nat → Prog isa) (sp sl : Nat) :
    VG.Impl.Ffdh.X86_64.Ifma.code mul sp sl =
      [.seq (.block (VG.Impl.Ffdh.X86_64.Ifma.fits PubIfma.pay2048 sl))
        (.ite .e (seqs (VG.Impl.Ffdh.X86_64.Ifma.exp PubIfma.pay2048 sp sl))
          (.seq (.block (VG.Impl.Ffdh.X86_64.Ifma.fits PubIfma.pay3072 sl))
            (.ite .e (seqs (VG.Impl.Ffdh.X86_64.Ifma.exp PubIfma.pay3072 sp sl))
              (.seq (.block (VG.Impl.Ffdh.X86_64.Ifma.fits PubIfma.pay4096 sl))
                (.ite .e (seqs (VG.Impl.Ffdh.X86_64.Ifma.exp PubIfma.pay4096 sp sl))
                  (seqs (Crt.expLoop mul Crt.tabSelect sp sl)))))))] := rfl

theorem codeC_eq (mul : Nat → Nat → Nat → Prog isa) (sp sl : Nat) :
    VG.Impl.Ffdh.X86_64.Ifma.codeC mul sp sl =
      [.seq (.block (VG.Impl.Ffdh.X86_64.Ifma.fits PubIfma.pay2048 sl))
        (.ite .e (seqs (VG.Impl.Ffdh.X86_64.Ifma.expC PubIfma.pay2048 "vg_ffdh_exp_ifma_2048" sp sl))
          (.seq (.block (VG.Impl.Ffdh.X86_64.Ifma.fits PubIfma.pay3072 sl))
            (.ite .e (seqs (VG.Impl.Ffdh.X86_64.Ifma.expC PubIfma.pay3072 "vg_ffdh_exp_ifma_3072" sp sl))
              (.seq (.block (VG.Impl.Ffdh.X86_64.Ifma.fits PubIfma.pay4096 sl))
                (.ite .e (seqs (VG.Impl.Ffdh.X86_64.Ifma.expC PubIfma.pay4096 "vg_ffdh_exp_ifma_4096" sp sl))
                  (seqs (Crt.expLoop mul Crt.tabSelect sp sl)))))))] := rfl

theorem ifma_inline (mul : Nat → Nat → Nat → Prog isa) (sp sl : Nat) (hs : ExpSlots sp sl) :
    @List.map (Code Instr Cond) (Prog isa) (@Code.inline Instr Cond) (VG.Impl.Ffdh.X86_64.Ifma.codeC mul sp sl) =
      VG.Impl.Ffdh.X86_64.Ifma.code (fun o a b => (mul o a b).inline) sp sl := by
  have hb := ExpImpl.base.inline mul sp sl hs
  simp only [ExpImpl.base] at hb
  obtain ⟨a, b, c⟩ := lok hs
  rw [codeC_eq, code_eq]
  simp only [List.map_cons, List.map_nil, Code.inline, inline_seqs, hb, expC_inline _ a.1,
    expC_inline _ b.1, expC_inline _ c.1]

theorem ifma_inlineOk (mul : Nat → Nat → Nat → Prog isa) (hm : ∀ o a b, (mul o a b).InlineOk = true)
    (sp sl : Nat) (hs : ExpSlots sp sl) : (VG.Impl.Ffdh.X86_64.Ifma.codeC mul sp sl).all Code.InlineOk = true := by
  have hb := ExpImpl.base.inlineOk mul hm sp sl hs
  simp only [ExpImpl.base] at hb
  obtain ⟨a, b, c⟩ := lok hs
  rw [codeC_eq, List.all_cons, List.all_nil, Bool.and_true]
  exact ok_seq a.2.1 (ok_ite (expC_inlineOk _ a.1 a.2.2.1 vecs_free.1) (ok_seq b.2.1
    (ok_ite (expC_inlineOk _ b.1 b.2.2.1 vecs_free.2.1) (ok_seq c.2.1
      (ok_ite (expC_inlineOk _ c.1 c.2.2.1 vecs_free.2.2) ((inlineOk_seqs _).trans hb))))))

theorem ifma_spSafe (mul : Nat → Nat → Nat → Prog isa)
    (hm : ∀ o a b, (mul o a b).allInstrs (fun i => !isa.writesSp i) = true) (sp sl : Nat) (hs : ExpSlots sp sl) :
    (VG.Impl.Ffdh.X86_64.Ifma.code mul sp sl).all (fun c => c.allInstrs (fun i => !isa.writesSp i)) = true := by
  have hb := ExpImpl.base.spSafe mul hm sp sl hs
  simp only [ExpImpl.base] at hb
  obtain ⟨a, b, c⟩ := lok hs
  rw [code_eq, List.all_cons, List.all_nil, Bool.and_true]
  exact in_seq a.2.2.2.1 (in_ite a.2.2.2.2.1 (in_seq b.2.2.2.1 (in_ite b.2.2.2.2.1 (in_seq c.2.2.2.1
    (in_ite c.2.2.2.2.1 ((all_seqs _ _).trans hb))))))

theorem ifma_ctl (mul : Nat → Nat → Nat → Prog isa)
    (hm : ∀ o a b, (mul o a b).allInstrs (fun i => !loadsMxcsr i) = true) (sp sl : Nat) (hs : ExpSlots sp sl) :
    (VG.Impl.Ffdh.X86_64.Ifma.code mul sp sl).all ctlOk = true := by
  have hb := ExpImpl.base.ctl mul hm sp sl hs
  simp only [ExpImpl.base] at hb
  obtain ⟨a, b, c⟩ := lok hs
  rw [code_eq, List.all_cons, List.all_nil, Bool.and_true]
  exact ctlOk_seq_of a.2.2.2.2.2.1 (ctlOk_ite_of a.2.2.2.2.2.2 (ctlOk_seq_of b.2.2.2.2.2.1
    (ctlOk_ite_of b.2.2.2.2.2.2 (ctlOk_seq_of c.2.2.2.2.2.1 (ctlOk_ite_of c.2.2.2.2.2.2 (ctlOk_seqs_of hb))))))

private theorem ifma_fill (mul : Nat → Nat → Nat → Prog isa) (k : Nat)
    (hm : ∀ o a b, X86_64.Scrub.calleeSide (mul o a b) k 8 = true) (sp sl : Nat) :
    List.Forall₂ (X86_64.Scrub.FillG k (fun _ => 8)) (VG.Impl.Ffdh.X86_64.Ifma.codeC stubMM sp sl)
      (VG.Impl.Ffdh.X86_64.Ifma.codeC mul sp sl) := by
  rw [codeC_eq, codeC_eq]
  unfold Crt.expLoop Crt.expLoopS Crt.expWin Crt.tabBuild Crt.tabBuildN
  fill_gen

private theorem ifma_stubX : (VG.Impl.Ffdh.X86_64.Ifma.codeC stubMM sX sXl).all
    (fun a => X86_64.Scrub.stubCalleeG a Impl.Scrub.X86_64.VecLevel.evex.level (fun _ => 8) 8) = true := by
  lit_decide

private theorem ifma_stubE : (VG.Impl.Ffdh.X86_64.Ifma.codeC stubMM sEp sEl).all
    (fun a => X86_64.Scrub.stubCalleeG a Impl.Scrub.X86_64.VecLevel.evex.level (fun _ => 8) 8) = true := by
  lit_decide

theorem ifma_side (mul : Nat → Nat → Nat → Prog isa) (k : Nat) (hk : Impl.Scrub.X86_64.VecLevel.evex.level ≤ k)
    (hm : ∀ o a b, X86_64.Scrub.calleeSide (mul o a b) k 8 = true) (sp sl : Nat) (hs : ExpSlots sp sl) :
    ∀ c ∈ VG.Impl.Ffdh.X86_64.Ifma.codeC mul sp sl, X86_64.Scrub.calleeSide c k 8 = true := by
  refine X86_64.Scrub.calleeSide_of_forall₂ (ifma_fill mul k hm sp sl) hk ?_
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ifma_stubX
  · exact ifma_stubE

def variant : ExpImpl where
  code := VG.Impl.Ffdh.X86_64.Ifma.codeC
  codeI := VG.Impl.Ffdh.X86_64.Ifma.code
  E := Proof.Ffdh.X86_64.Ifma.expL
  code_eq _ := rfl
  inline := ifma_inline
  inlineOk := ifma_inlineOk
  spSafe := ifma_spSafe
  ctl := ifma_ctl
  ctX := ifma_ctX
  ctE := ifma_ctE
  level := .evex
  side := ifma_side
  suffix := "_ifma"
  features := ["avx", "avx512f", "avx512ifma", "avx512vl"]

end VG.Proof.Variants.FfdhExp.X86_64.Ifma
