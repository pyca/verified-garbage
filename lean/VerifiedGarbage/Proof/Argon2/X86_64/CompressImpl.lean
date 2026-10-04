import VerifiedGarbage.Proof.Argon2.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
import VerifiedGarbage.Impl.Argon2.X86_64.Compressor

/-!
# Implementations of G that the derivation calls

The derivation (`vg_argon2`) calls an implementation of G: the baseline's
`vg_argon2_compress` or a variant (e.g. `vg_argon2_compress_avx2`, see
`Variants/Argon2Compress/X86_64/`). Its proofs use only what `CompressImpl`
states of it: that it meets `compressLocal` (the contract of
`vg_argon2_compress` on x86-64) and is constant time, uses no stack, never
writes `rsp`, and keeps MXCSR's control bits (`ctlOk`: it may load MXCSR
between Intel's MCDT prologue and epilogue). The code that calls it finds it
as the instance `Impl.Argon2.X86_64.Compressor`.
-/

namespace VG.Proof.Argon2.X86_64

open VG VG.X86_64

/-- An implementation of G, named `vg_argon2_compress` with `suffix`, which
needs the CPU features `features`. -/
class CompressImpl where
  suffix : String
  features : List String
  code : Prog isa
  correct : ∀ s, compressLocal.pre s →
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ compressLocal.post s t
  ct : ConstantTime isa compressLocal.pre compressLocal.pub code
  noSp : NoSp code
  depth : code.depth = 0
  ctl : ctlOk code = true
  spSafe : code.all (fun i => !isa.writesSp i) = true

/-- MXCSR's control bits are those of a state with the same MXCSR. -/
theorem ctl_eq_of {a b : BitVec 32} (h : a = b) : ctl a = ctl b := congrArg ctl h

/-- `WP.mono_mx`, adding that MXCSR is unchanged to the postcondition. -/
theorem WP.with_mx {c : Prog isa} (hc : c.allInstrs (fun i => !loadsMxcsr i) = true) {s : State}
    {Q : State → Prop} (h : WP isa c s Q) : WP isa c s fun t => Q t ∧ t.mxcsr = s.mxcsr :=
  WP.mono_mx hc h fun _ q m => ⟨q, m⟩

/-- Code none of whose instructions writes `rsp` (checked by evaluation). -/
theorem noSp_of_allInstrs {c : Prog isa}
    (h : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true) : NoSp c := by
  rw [Code.allInstrs_eq, List.all_eq_true] at h
  intro i hi
  simpa only [Bool.not_eq_true'] using h i hi

/-- Code that never loads MXCSR satisfies `ctlOk`. -/
theorem ctlOk_of_allInstrs {c : Prog isa} (h : c.allInstrs (fun i => !loadsMxcsr i) = true) :
    ctlOk c = true := by
  induction c with
  | block _ => rw [Code.allInstrs_eq] at h; exact h
  | seq _ _ iha ihb =>
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [ctlOk, iha h.1, ihb h.2, Bool.and_self, Bool.or_true]
  | ite _ _ _ iht ihe =>
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [ctlOk, iht h.1, ihe h.2, Bool.and_self]
  | loop _ _ ih => exact ih h
  | call _ _ ih => exact ih h
  | frame _ _ _ ih =>
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [ctlOk, h.1.1, h.2, ih h.1.2, Bool.and_self]

/-- Code that never loads MXCSR satisfies `ctlC`. -/
theorem ctlC_of_allInstrs {c : Prog isa} (h : c.allInstrs (fun i => !loadsMxcsr i) = true) :
    ctlC c = true := by
  induction c with
  | block _ => rw [Code.allInstrs_eq] at h; exact h
  | seq _ _ iha ihb =>
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [ctlC, iha h.1, ihb h.2, Bool.and_self]
  | ite _ _ _ iht ihe =>
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [ctlC, iht h.1, ihe h.2, Bool.and_self]
  | loop _ _ ih => exact ih h
  | call _ _ _ => exact ctlOk_of_allInstrs h
  | frame _ _ _ ih =>
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [ctlC, h.1.1, h.2, ih h.1.2, Bool.and_self]

instance [c : CompressImpl] : Impl.Argon2.X86_64.Compressor :=
  ⟨Spec.Argon2.compressApi.name ++ c.suffix, c.code⟩

theorem compressor_spSafe [CompressImpl] :
    (Impl.Argon2.X86_64.Compressor.code : Prog isa).all (fun i => !isa.writesSp i) = true :=
  CompressImpl.spSafe

theorem compressor_ctl [CompressImpl] : ctlOk (Impl.Argon2.X86_64.Compressor.code : Prog isa) = true :=
  CompressImpl.ctl

end VG.Proof.Argon2.X86_64
