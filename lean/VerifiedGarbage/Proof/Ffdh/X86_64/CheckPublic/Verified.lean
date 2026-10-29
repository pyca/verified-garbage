module

public import VerifiedGarbage.Impl.Ffdh.X86_64.Domain
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Spec.Ffdh.Contract

import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.CT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Contract
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Body
import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
/-! # FFDH public-key validation on x86-64: verified -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/CheckPublic/Correct.lean`, which only this module imported.
section

/-! # FFDH public-key validation on x86-64: full correctness and ABI -/

section

namespace VG.Proof.Ffdh.X86_64.CheckPublic

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem cp_correct (M : Mont) (E : CrtExpL M) (R : R2Impl M)
    (hmx : (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.code M.mm E.code (.seq (.block r2Head) R.code)).allInstrs
      (fun i => !loadsMxcsr i) = true) (s : State) (h : cpContract.pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.code M.mm E.code (.seq (.block r2Head) R.code)) s tr t ∧
      abiPreserved s t ∧ cpContract.post s t := by
  have c := cpCtx_of h
  obtain ⟨_, _, _, _, _, _, _, _, hRetScr, _⟩ := h
  suffices hw : WP isa (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.code M.mm E.code (.seq (.block r2Head) R.code)) s
      fun t => gprPreserved s t ∧ cpContract.post s t by
    obtain ⟨tr, t, he, hg, hp⟩ := hw
    exact ⟨tr, t, he, abiPreserved_of_exec hmx he hg, hp⟩
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckPublic.code
  refine WP.seq (WP.mono (cp_body_ok M E R c) fun u ⟨hp, hdi, hf, hsaved, k₁⟩ => ?_)
  have hZ := c.hZ
  have hk := c.k1
  refine WP.mono (exit_ok (c.hs.congr k₁.2.2) hdi (by omega) hsaved)
    fun t ⟨hRestore, hm, k₂⟩ => ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact (k₂.gpr (by decide)).trans (k₁.gpr (by decide))
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
  · rw [hm]
    apply Mem.readW_congr
    intro i hi
    exact hf _ (out_scr hRetScr (contains_byte (s.gpr .rsp) hi (by decide)))
  · change cpPost s t
    unfold cpPost
    rw [k₂.gpr (show .rax ∉ saved by decide)]
    exact hp

end VG.Proof.Ffdh.X86_64.CheckPublic
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPublic

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.Ffdh.X86_64.Domain

theorem cp_verified (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sEp sEl)
    (hmx : (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.code M.mm E.code (.seq (.block r2Head) R.code)).allInstrs
      (fun i => !loadsMxcsr i) = true) :
    Verified target (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.code M.mm E.code (.seq (.block r2Head) R.code))
      (Spec.Ffdh.checkPublicContract abi) := by
  exact Verified.of_correct (cp_correct M E R hmx) (cp_constantTime M E R hE) cp_implies

end VG.Proof.Ffdh.X86_64.CheckPublic
