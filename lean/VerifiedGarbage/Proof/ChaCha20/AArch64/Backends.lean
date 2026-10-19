module

public import VerifiedGarbage.Proof.ChaCha20.AArch64.Variant
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Variant
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.ChaCha20.AArch64.XorContract
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.XorContract
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64

open VG VG.AArch64

theorem keeps_of_check {c : Prog isa} {rs : List Reg}
    (h : (c.allInstrs fun i => rs.all fun r => !clobbers i r) = true) :
    ∀ r ∈ rs, ∀ i ∈ instrs c, clobbers i r = false := by
  rw [Code.allInstrs_eq] at h
  intro r hr i hi
  have h' := List.all_eq_true.mp (List.all_eq_true.mp h i hi) r hr
  simpa using h'

namespace BlockImpl

def scalar : BlockImpl where
  callee := .scalar
  features := []
  ok := block_correct
  noFrames := by lit_decide
  keeps := keeps_of_check (by lit_decide)
  xorKeeps := keeps_of_check (by lit_decide)
  xorKeepsV := by lit_decide
  xorNoFrames := by lit_decide
  xorTaint := by exact ⟨_, by taint_decide⟩

end BlockImpl
end VG.Proof.ChaCha20.AArch64
