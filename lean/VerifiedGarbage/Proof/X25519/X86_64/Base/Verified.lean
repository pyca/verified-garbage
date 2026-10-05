import VerifiedGarbage.Proof.X25519.X86_64.Base.CT
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified
import VerifiedGarbage.Proof.Framework.Contract

/-! Fixed-base X25519 satisfies the reviewed contract, with either field backend. -/
namespace VG.Proof.X25519.X86_64.Base
open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.X25519.X86_64.Base
open VG.Proof.Ed25519.X86_64
variable {fld : Arith} [EdArith fld]

theorem engine_public (base k : Addr) :
    RelCT isa (fun x y => BaseEnginePre base k x ∧ BaseEnginePre base k y)
      (engine fld) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi, .rsi]) _ (by fld_taint_decide)
  intro x y h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.rdi.trans h.2.1.rdi.symm
  · exact h.1.2.1.trans h.2.2.1.symm

theorem x25519Base_ok (s : State) (hs : baseLocal.pre s) :
    ∃ tr t, Exec isa (x25519Base fld) s tr t ∧ abiPreserved s t ∧ baseLocal.post s t := by
  obtain ⟨tr, t, he, h⟩ := x25519Base_correct (fld := fld) hs
  exact ⟨tr, t, he, abiPreserved_of_exec (by fld_lit_decide) he h.1, h.2⟩

theorem x25519Base_verified : Verified X86_64.target (x25519Base fld)
    (Spec.X25519.x25519BaseContract X86_64.abi) :=
  Verified.of_correct x25519Base_ok (x25519Base_ct engine_public) (by
    sig_implies [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
      X86_64.abi, X86_64.argRegs, baseLocal]
      [baseSatState] using baseSatState)

end VG.Proof.X25519.X86_64.Base
