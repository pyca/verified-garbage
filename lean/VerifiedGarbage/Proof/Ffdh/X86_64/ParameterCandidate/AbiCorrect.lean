module
import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Core
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Contract
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Correct
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH parameter generation on x86-64: preserve the complete System V ABI -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 (saved)
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64

private theorem ret_frame {c : Prog isa} {s t : State} {tr : List Leak}
    (h : pcPre s) (hs : SpSafe c) (hd : c.x86_64Depth ≤ 128) (he : Exec isa c s tr t) :
    t.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  obtain ⟨_, _, _, hwr, _, _, _, _, _, _, _, _, _, hro, hru, _, hrs, _⟩ := h
  have hf := Exec.stackFrame hs he (by omega_using [hd])
  refine hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hro, hru, hrs]
  · simp only [List.mem_singleton] at hr; subst r
    exact Offset.base_disjoint_below _ (by omega_using [hd])

theorem pc_correct (M : Mont) (R : R2Impl M) (K : Kernel)
    (hs : SpSafe (VG.Impl.Ffdh.X86_64.ParameterCandidate.code M.mm R.code K.run))
    (hd : (VG.Impl.Ffdh.X86_64.ParameterCandidate.code M.mm R.code K.run).x86_64Depth ≤ 128)
    (hmx : (VG.Impl.Ffdh.X86_64.ParameterCandidate.code M.mm R.code K.run).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : pcContract.pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.X86_64.ParameterCandidate.code M.mm R.code K.run) s tr t ∧
      abiPreserved s t ∧ pcContract.post s t := by
  obtain ⟨tr, t, he, hp, hregs, k⟩ := correct_ok M R K (pcCtx_of h)
  have hg : gprPreserved s t := by
    refine ⟨?_, ret_frame h hs hd he⟩
    intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hregs _ (by decide)
    · exact hregs _ (by decide)
    · exact k.gpr (by decide)
    · exact hregs _ (by decide)
    · exact hregs _ (by decide)
    · exact hregs _ (by decide)
    · exact hregs _ (by decide)
  exact ⟨tr, t, he, abiPreserved_of_exec hmx he hg, hp⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
