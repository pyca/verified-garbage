import VerifiedGarbage.Proof.X25519.X86_64.Base.Verified
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.ScalarBase

/-!
# Fixed-base X25519 with AVX512_IFMA: `Verified`

`x25519BaseIfma` is `x25519Base adx` with Ed25519's comb with AVX512_IFMA
(`Proof.Ed25519.X86_64.Ifma.combOk`); MXCSR's control bits kept, as the comb
loads MXCSR only between saving it in `r11` and loading it back (`ctlOk`).
-/

namespace VG.Proof.X25519.X86_64.Base

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.X25519.X86_64.Base VG.Proof.Ed25519.X86_64

/-- The engine with the comb with AVX512_IFMA. -/
abbrev engineIfma : Prog isa :=
  engineOf Impl.X25519.X86_64.adx (Impl.Ed25519.X86_64.Ifma.combMultiply Impl.X25519.X86_64.adx)

theorem engineIfma_ok : UEngineOk engineIfma := engineOf_ok Ifma.combOk

theorem engineIfma_public (base k T : Addr) :
    RelCT isa (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y) engineIfma
      (fun _ _ => True) := by
  apply taintSymFld (Taint.ofRegs [.rdi, .rsi]) _ (by exact ⟨_, by taint_decide⟩)
  intro x y h
  refine ⟨Taint.agree_ofRegs fun r hr => ?_, fun n hn => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.rdi.trans h.2.1.rdi.symm
    · exact h.1.2.1.trans h.2.2.1.symm
  · simp only [List.mem_singleton] at hn; subst hn
    exact h.1.2.2.2.2.1.sym.trans h.2.2.2.2.2.1.sym.symm

theorem x25519BaseIfma_ok (s : State) (hs : baseLocal.pre s) :
    ∃ tr t, Exec isa x25519BaseIfma s tr t ∧ abiPreserved s t ∧ baseLocal.post s t := by
  obtain ⟨tr, t, he, h⟩ := x25519BaseWith_correct _ engineIfma_ok hs
  exact ⟨tr, t, he, abiPreserved_of_ctl (by lit_decide) he h.1, h.2⟩

theorem x25519BaseIfma_verified : Verified X86_64.target x25519BaseIfma
    (Spec.X25519.x25519BaseContract (X86_64.abi.withConsts combConsts)) :=
  Verified.of_correct x25519BaseIfma_ok (x25519BaseWith_ct _ engineIfma_ok engineIfma_public) base_implies

end VG.Proof.X25519.X86_64.Base
