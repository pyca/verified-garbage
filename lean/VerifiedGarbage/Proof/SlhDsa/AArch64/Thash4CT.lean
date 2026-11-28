module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.Thash4Contract
public import VerifiedGarbage.Impl.SlhDsa.AArch64.Thash4
public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
import VerifiedGarbage.Proof.SlhDsa.AArch64.Thash4Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.SlhDsa.AArch64.Thash4Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint

-- separate module: it builds in parallel with the proof of correctness (`Thash4Correct`).

/-!
# SLH-DSA on AArch64: `thash4`, constant time

The taint analysis of the vector registers (`VectorTaint`, which follows the
public registers the two-way permutation in general registers keeps in
vector registers) proves every `thash4` constant time from its pointers,
`stride` and `len` (`x0`–`x4`), with the permutation's code in it.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Thash4

open VG VG.AArch64

theorem taint (n : Nat) (hn : n = 16 ∨ n = 24 ∨ n = 32) (sha3 : Bool) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4])
      (Impl.SlhDsa.AArch64.Thash4.thash4 n sha3) h).isSome = true := by
  rcases hn with rfl | rfl | rfl <;> cases sha3
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

theorem ct (n : Nat) (hn : n = 16 ∨ n = 24 ∨ n = 32) (sha3 : Bool) :
    ConstantTime isa (thash4Contract n).pre (thash4Contract n).pub (Impl.SlhDsa.AArch64.Thash4.thash4 n sha3) :=
  Taint.constantTime_of_exists (A := VectorTaint.taint) (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ h => ⟨⟨h.2.2.2.2.2, fun r hr => by
      simp only [VectorTaint.ofRegs, Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2.1
      · exact h.2.2.2.1
      · exact h.2.2.2.2.1⟩, fun v hv => by simp [VectorTaint.ofRegs] at hv⟩) (taint n hn sha3)

end VG.Proof.SlhDsa.AArch64.Thash4
