module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ExpImpl
public import VerifiedGarbage.Proof.Ffdh.X86_64.Ifma.CT
import VerifiedGarbage.Proof.Bignum.X86_64.Template
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ExpImpl
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Ifma.CT
meta import VerifiedGarbage.Proof.Bignum.X86_64.Template

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

theorem lok2048X : LOk PubIfma.pay2048 sX sXl := by unfold LOk; decide +kernel
theorem lok3072X : LOk PubIfma.pay3072 sX sXl := by unfold LOk; decide +kernel
theorem lok4096X : LOk PubIfma.pay4096 sX sXl := by unfold LOk; decide +kernel
theorem lok2048E : LOk PubIfma.pay2048 sEp sEl := by unfold LOk; decide +kernel
theorem lok3072E : LOk PubIfma.pay3072 sEp sEl := by unfold LOk; decide +kernel
theorem lok4096E : LOk PubIfma.pay4096 sEp sEl := by unfold LOk; decide +kernel

theorem lok {sp sl : Nat} (hs : ExpSlots sp sl) :
    LOk PubIfma.pay2048 sp sl ∧ LOk PubIfma.pay3072 sp sl ∧ LOk PubIfma.pay4096 sp sl := by
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨lok2048X, lok3072X, lok4096X⟩
  · exact ⟨lok2048E, lok3072E, lok4096E⟩

theorem code_eq (mul : Nat → Nat → Nat → Prog isa) (sp sl : Nat) :
    VG.Impl.Ffdh.X86_64.Ifma.code mul sp sl =
      [.seq (.block (VG.Impl.Ffdh.X86_64.Ifma.fits PubIfma.pay2048 sl))
        (.ite .e (seqs (VG.Impl.Ffdh.X86_64.Ifma.exp PubIfma.pay2048 sp sl))
          (.seq (.block (VG.Impl.Ffdh.X86_64.Ifma.fits PubIfma.pay3072 sl))
            (.ite .e (seqs (VG.Impl.Ffdh.X86_64.Ifma.exp PubIfma.pay3072 sp sl))
              (.seq (.block (VG.Impl.Ffdh.X86_64.Ifma.fits PubIfma.pay4096 sl))
                (.ite .e (seqs (VG.Impl.Ffdh.X86_64.Ifma.exp PubIfma.pay4096 sp sl))
                  (seqs (Crt.expLoop mul Crt.tabSelect sp sl)))))))] := rfl

theorem ifma_inline (mul : Nat → Nat → Nat → Prog isa) (sp sl : Nat) (hs : ExpSlots sp sl) :
    @List.map (Code Instr Cond) (Prog isa) (@Code.inline Instr Cond) (VG.Impl.Ffdh.X86_64.Ifma.code mul sp sl) =
      VG.Impl.Ffdh.X86_64.Ifma.code (fun o a b => (mul o a b).inline) sp sl := by
  have hb := ExpImpl.base.inline mul sp sl hs
  simp only [ExpImpl.base] at hb
  obtain ⟨a, b, c⟩ := lok hs
  rw [code_eq, code_eq]
  simp only [List.map_cons, List.map_nil, Code.inline, inline_seqs, hb, map_inline_of_noCalls a.1,
    map_inline_of_noCalls b.1, map_inline_of_noCalls c.1]

theorem ifma_inlineOk (mul : Nat → Nat → Nat → Prog isa) (hm : ∀ o a b, (mul o a b).InlineOk = true)
    (sp sl : Nat) (hs : ExpSlots sp sl) : (VG.Impl.Ffdh.X86_64.Ifma.code mul sp sl).all Code.InlineOk = true := by
  have hb := ExpImpl.base.inlineOk mul hm sp sl hs
  simp only [ExpImpl.base] at hb
  obtain ⟨a, b, c⟩ := lok hs
  rw [code_eq, List.all_cons, List.all_nil, Bool.and_true]
  exact ok_seq a.2.1 (ok_ite a.2.2.1 (ok_seq b.2.1 (ok_ite b.2.2.1 (ok_seq c.2.1
    (ok_ite c.2.2.1 ((inlineOk_seqs _).trans hb))))))

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

def variant : ExpImpl where
  code := VG.Impl.Ffdh.X86_64.Ifma.code
  E := Proof.Ffdh.X86_64.Ifma.expL
  code_eq _ := rfl
  inline := ifma_inline
  inlineOk := ifma_inlineOk
  spSafe := ifma_spSafe
  ctl := ifma_ctl
  ctX := ifma_ctX
  ctE := ifma_ctE
  suffix := "_ifma"
  features := ["avx", "avx512f", "avx512ifma", "avx512vl"]

end VG.Proof.Variants.FfdhExp.X86_64.Ifma
