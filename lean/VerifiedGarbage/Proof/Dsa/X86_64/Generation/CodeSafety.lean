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

def generationSafe (c : Prog isa) : Prop :=
  c.allInstrs (fun i => !loadsMxcsr i && !isa.writesSp i) = true

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

theorem generationSafe.call {b : Prog isa} (hb : generationSafe b) (name : String) :
    generationSafe (.call name b) := hb

theorem generationSafe.seqs (cs : List (Prog isa))
    (hc : ∀ c ∈ cs, generationSafe c) : generationSafe (Impl.Bignum.X86_64.seqs cs) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases cs with
    | nil => exact hc c (by simp)
    | cons d cs => exact (hc c (by simp)).seq (ih fun x hx => hc x (List.mem_cons_of_mem _ hx))

theorem generationSafe.sp {c : Prog isa} (h : generationSafe c) :
    c.all (fun i => !isa.writesSp i) = true := by
  apply Code.all_of_allInstrs
  rw [generationSafe, Code.allInstrs_eq] at h
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h i hi)).2

theorem generationSafe.mx {c : Prog isa} (h : generationSafe c) : ctlOk c = true := by
  have hn : c.all (fun i => !loadsMxcsr i) = true := by
    apply Code.all_of_allInstrs
    rw [generationSafe, Code.allInstrs_eq] at h
    rw [Code.allInstrs_eq]
    exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h i hi)).1
  clear h
  induction c with
  | icall _ _ _ _ ihb ihn =>
    simp only [Code.all, Bool.and_eq_true] at hn
    simp only [ctlOk, hn.1.1, ihb hn.1.2, ihn hn.2, Bool.and_self]
  | block is => simpa only [ctlOk, ← KList.all_eq, Code.all] using hn
  | seq a b iha ihb =>
    simp only [Code.all, Bool.and_eq_true] at hn
    simp only [ctlOk, iha hn.1, ihb hn.2, Bool.and_self, Bool.or_true]
  | ite cc a b iha ihb =>
    simp only [Code.all, Bool.and_eq_true] at hn
    simp only [ctlOk, iha hn.1, ihb hn.2, Bool.and_self]
  | loop b cc ih => exact ih hn
  | call name b ih => exact ih hn
  | frame i b j ih =>
    simp only [Code.all, Bool.and_eq_true] at hn
    simp only [ctlOk, hn.1.1, ih hn.1.2, hn.2, Bool.and_self]

end VG.Proof.Dsa.X86_64.Generation
