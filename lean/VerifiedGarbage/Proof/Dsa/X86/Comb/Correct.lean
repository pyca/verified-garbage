module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.Body


import VerifiedGarbage.Proof.Dsa.X86.Comb.BodyWide

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Lit

/-! The comb helpers' scratch regions fit in their layout. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86

theorem scratch_fits {n e : Nat} (h : Supported n e) (prepare : Bool) :
    ∀ r ∈ scratch prepare n, r.1+r.2≤(layout n e).size := by
  cases prepare <;>
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide

end VG.Proof.Dsa.X86.Comb
