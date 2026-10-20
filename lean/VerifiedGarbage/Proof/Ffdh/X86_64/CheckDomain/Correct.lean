module
public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckDomain
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Contract

import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Body
import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH domain validation on x86-64: full correctness and ABI -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem cd_correct (M : Mont) (E : CrtExpL M) (R : R2Impl M)
    (hmx : (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.code M.mm E.code (.seq (.block r2Head) R.code)).allInstrs
      (fun i => !loadsMxcsr i) = true) (s : State) (h : cdContract.pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.code M.mm E.code (.seq (.block r2Head) R.code)) s tr t ∧
      abiPreserved s t ∧ cdContract.post s t := by
  have c := cdCtx_of h
  obtain ⟨_, _, _, _, _, _, hRetScr, _⟩ := h
  suffices hw : WP isa (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.code M.mm E.code (.seq (.block r2Head) R.code)) s
      fun t => gprPreserved s t ∧ cdContract.post s t by
    obtain ⟨tr, t, he, hg, hp⟩ := hw
    exact ⟨tr, t, he, abiPreserved_of_exec hmx he hg, hp⟩
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckDomain.code
  refine WP.seq (WP.mono (cd_body_ok M E R c) fun u ⟨hp, hdi, hf, hsaved, k₁⟩ => ?_)
  have hZ := c.hZ
  have hk := c.k1
  refine WP.mono (exit_ok (c.scr.congr k₁.2.2) hdi (by omega) hsaved)
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
  · change cdPost s t
    unfold cdPost
    rw [k₂.gpr (show .rax ∉ saved by decide)]
    exact hp

end VG.Proof.Ffdh.X86_64.CheckDomain
