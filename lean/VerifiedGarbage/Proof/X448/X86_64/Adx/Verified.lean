module

import VerifiedGarbage.Proof.X448.X86_64.Adx.Sqr
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.X448.X86_64.Verified
import VerifiedGarbage.Proof.Framework.LitShare
public import VerifiedGarbage.Proof.X448.X86_64.Main
import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
public import VerifiedGarbage.Impl.X448.X86_64.Adx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X448.X86_64.Lit
meta import VerifiedGarbage.Proof.X448.X86_64.Adx.Sqr
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.X448.X86_64.Verified
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.X448.X86_64.Main
meta import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
meta import VerifiedGarbage.Impl.X448.X86_64.Adx
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X448.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# X448 on x86-64 with BMI2 and ADX: `Verified`

The proof of `vg_x448` (`Proof/X448/X86_64/Verified.lean`) for the field
multiplications `adx` (`adx_ok`): correctness from `correct`, constant time by
taint tracking (the only branches are on the loop counters, and every address
is an argument plus a constant or a counter), satisfiability, and the shared
contract.
-/

@[expose] public section

namespace VG.Proof.X448.X86_64

open VG VG.X86_64

theorem x448Adx_ok (s : State) (hs : Proof.X448.x448X86_64.pre s) :
    ∃ t s', Exec isa Impl.X448.X86_64.x448Adx.inline s t s' ∧ abiPreserved s s' ∧
      Proof.X448.x448X86_64.post s s' := by
  have hc : WP isa Impl.X448.X86_64.x448Adx.inline s
      (fun u => gprPreserved s u ∧ Proof.X448.x448X86_64.post s u) := by
    change WP isa (Impl.X448.X86_64.x448Of Impl.X448.X86_64.adx (Impl.X448.X86_64.ladder Impl.X448.X86_64.adx)
      (Impl.X448.X86_64.invertCallWith Impl.X448.X86_64.adx ("vg_gf448_r64_pow223" ++ "_adx")).inline) s _
    exact correct_of adx_ok (fun h => ladder_post adx_ok h)
      (fun h => invertCallWith_post adx_ok _ (keep := []) (by simp) h) (Pre.of s hs)
  obtain ⟨t, s', he, h⟩ := hc
  exact ⟨t, s', he, abiPreserved_of_exec (by rw [Code.allInstrs_inline]; lit_decide) he h.1, h.2⟩

/-- The code without its displacements: from a taint that knows no region
bases, the analysis does not read them (`Proof/Framework/X86_64/TaintErase.lean`),
and the field arithmetic is then the same few blocks, each a constant
(`materialize_shared`) whose analysis from the same taint the kernel evaluates
once. -/
def x448AdxErased : Prog isa := Code.erase Impl.X448.X86_64.x448Adx

materialize_shared x448AdxErased

/-- Constant time by the analysis of the code without its displacements (`x448AdxErased`). -/
theorem x448Adx_ct : ConstantTime isa Proof.X448.x448X86_64.pre Proof.X448.x448X86_64.pub
    Impl.X448.X86_64.x448Adx := by
  refine VG.Taint.constantTime_mapBlocks (c' := x448AdxErased) taintS_eraseInv
    (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) rfl ?_ rfl (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem x448Adx_verified :
    Verified X86_64.target Impl.X448.X86_64.x448Adx (Spec.X448.x448Contract X86_64.abi 8) :=
  Verified.of_inline_ct (by lit_decide) x448Adx_ok x448Adx_ct x448_implies8
    (fun _ h => Sig.clear_of_pre h) x448_patch

end VG.Proof.X448.X86_64
