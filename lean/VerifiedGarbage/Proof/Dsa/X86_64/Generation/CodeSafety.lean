module
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
public import VerifiedGarbage.Impl.Bignum.X86_64
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit


/-! # Compositional instruction-safety checks for generation code -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64

/-- Like `Code.allInstrs` of "neither loads MXCSR nor writes `rsp`", but a
called function need only satisfy `ctlOk` (it may load MXCSR where it restores
it) and never write `rsp`. -/
noncomputable def generationOk : Prog isa → Bool
  | .block is => List.rec (motive := fun _ => Bool) true (fun i _ ih => (!loadsMxcsr i && !isa.writesSp i) && ih) is
  | .seq a b => generationOk a && generationOk b
  | .ite _ t e => generationOk t && generationOk e
  | .loop b _ => generationOk b
  | .call _ b => ctlOk b && b.all (fun i => !isa.writesSp i)
  | .frame i b j => (!loadsMxcsr i && !isa.writesSp i) && generationOk b && (!loadsMxcsr j && !isa.writesSp j)
  | .icall i _ b n => (!loadsMxcsr i && !isa.writesSp i) && (ctlOk b && b.all (fun i => !isa.writesSp i)) &&
      generationOk n

def generationSafe (c : Prog isa) : Prop := generationOk c = true

theorem generationSafe.seq {a b : Prog isa} (ha : generationSafe a) (hb : generationSafe b) :
    generationSafe (.seq a b) := by
  change (_ && _) = true
  rw [ha, hb]; rfl

theorem generationSafe.ite {a b : Prog isa} (ha : generationSafe a) (hb : generationSafe b) (cc : Cond) :
    generationSafe (.ite cc a b) := by
  change (_ && _) = true
  rw [ha, hb]; rfl

theorem generationSafe.loop {b : Prog isa} (hb : generationSafe b) (cc : Cond) :
    generationSafe (.loop b cc) := hb

/-- A call of a function that restores MXCSR wherever it loads it. -/
theorem generationSafe.call_of {b : Prog isa} (hc : ctlOk b = true)
    (hs : b.all (fun i => !isa.writesSp i) = true) (name : String) : generationSafe (.call name b) := by
  change (_ && _) = true
  rw [hc, hs]; rfl

/-- Code `generationSafe` accepts satisfies `ctlC`. -/
theorem generationSafe.ctlC {c : Prog isa} (h : generationSafe c) : ctlC c = true := by
  unfold generationSafe at h
  induction c with
  | block is =>
    have h' : (Code.block is : Prog isa).allInstrs (fun i => !loadsMxcsr i && !isa.writesSp i) = true := h
    rw [Code.allInstrs_eq] at h'
    exact (KList.all_eq _ _).trans
      (List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h' i hi)).1)
  | seq _ _ iha ihb =>
    simp only [generationOk, Bool.and_eq_true] at h
    simp only [VG.X86_64.ctlC, iha h.1, ihb h.2, Bool.and_self]
  | ite _ _ _ iht ihe =>
    simp only [generationOk, Bool.and_eq_true] at h
    simp only [VG.X86_64.ctlC, iht h.1, ihe h.2, Bool.and_self]
  | loop _ _ ih => exact ih h
  | call _ _ _ =>
    simp only [generationOk, Bool.and_eq_true] at h
    exact h.1
  | frame _ _ _ ih =>
    simp only [generationOk, Bool.and_eq_true] at h
    simp only [VG.X86_64.ctlC, h.1.1.1, h.2.1, ih h.1.2, Bool.and_self]
  | icall _ _ _ _ _ ihn =>
    simp only [generationOk, Bool.and_eq_true] at h
    simp only [VG.X86_64.ctlC, h.1.1.1, h.1.2.1, ihn h.2, Bool.and_self]

theorem generationSafe.sp {c : Prog isa} (h : generationSafe c) :
    c.all (fun i => !isa.writesSp i) = true := by
  unfold generationSafe at h
  induction c with
  | block is =>
    have h' : (Code.block is : Prog isa).allInstrs (fun i => !loadsMxcsr i && !isa.writesSp i) = true := h
    rw [Code.allInstrs_eq] at h'
    exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h' i hi)).2
  | seq _ _ iha ihb =>
    simp only [generationOk, Bool.and_eq_true] at h
    simp only [Code.all, iha h.1, ihb h.2, Bool.and_self]
  | ite _ _ _ iht ihe =>
    simp only [generationOk, Bool.and_eq_true] at h
    simp only [Code.all, iht h.1, ihe h.2, Bool.and_self]
  | loop _ _ ih => exact ih h
  | call _ _ _ =>
    simp only [generationOk, Bool.and_eq_true] at h
    exact h.2
  | frame _ _ _ ih =>
    simp only [generationOk, Bool.and_eq_true] at h
    simp only [Code.all, h.1.1.2, h.2.2, ih h.1.2, Bool.and_self]
  | icall _ _ _ _ _ ihn =>
    simp only [generationOk, Bool.and_eq_true] at h
    simp only [Code.all, h.1.1.2, h.1.2.2, ihn h.2, Bool.and_self]

theorem generationSafe.call {b : Prog isa} (hb : generationSafe b) (name : String) :
    generationSafe (.call name b) :=
  generationSafe.call_of (ctlOk_of_ctlC hb.ctlC) hb.sp name

theorem generationSafe.mx {c : Prog isa} (h : generationSafe c) : ctlOk c = true :=
  ctlOk_of_ctlC h.ctlC

theorem generationOk_seqs (l : List (Prog isa)) :
    generationOk (VG.Impl.Bignum.X86_64.seqs l) = l.all generationOk := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => simp only [VG.Impl.Bignum.X86_64.seqs, List.all_cons, List.all_nil, Bool.and_true]
    | cons b l => simp only [VG.Impl.Bignum.X86_64.seqs, generationOk, List.all_cons] at ih ⊢; rw [ih]

/-- Code that neither loads MXCSR nor writes `rsp` is `generationSafe`. -/
theorem generationSafe_of_allInstrs {c : Prog isa}
    (h : c.allInstrs (fun i => !loadsMxcsr i && !isa.writesSp i) = true) : generationSafe c := by
  unfold generationSafe
  induction c with
  | block is => exact h
  | seq _ _ iha ihb =>
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [generationOk, iha h.1, ihb h.2, Bool.and_self]
  | ite _ _ _ iht ihe =>
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [generationOk, iht h.1, ihe h.2, Bool.and_self]
  | loop _ _ ih => exact ih h
  | call _ b _ =>
    have h' : b.allInstrs (fun i => !loadsMxcsr i && !isa.writesSp i) = true := h
    rw [Code.allInstrs_eq] at h'
    have hm : b.allInstrs (fun i => !loadsMxcsr i) = true := by
      rw [Code.allInstrs_eq]
      exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h' i hi)).1
    have hs : b.allInstrs (fun i => !isa.writesSp i) = true := by
      rw [Code.allInstrs_eq]
      exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h' i hi)).2
    simp only [generationOk, ctlOk_of_noLoad hm, Code.all_of_allInstrs hs, Bool.and_self]
  | frame _ _ _ ih =>
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [generationOk, h.1.1, h.2, ih h.1.2, Bool.and_self]
  | icall _ _ b _ _ ihn =>
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    have h' := h.1.2
    rw [Code.allInstrs_eq] at h'
    have hm : b.allInstrs (fun i => !loadsMxcsr i) = true := by
      rw [Code.allInstrs_eq]
      exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h' i hi)).1
    have hs : b.allInstrs (fun i => !isa.writesSp i) = true := by
      rw [Code.allInstrs_eq]
      exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h' i hi)).2
    simp only [generationOk, h.1.1, ctlOk_of_noLoad hm, Code.all_of_allInstrs hs, ihn h.2, Bool.and_self]

end VG.Proof.Dsa.X86_64.Generation
