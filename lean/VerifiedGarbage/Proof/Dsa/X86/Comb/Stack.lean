module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.X86.Call

/-! Both helpers use workspace scratch instead of a stack arena.
These are structural bounds, separate from arithmetic and ABI preservation. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb

theorem body_noSp {n e : Nat} (h : Supported n e) (prepare : Bool) :
    NoSp (body prepare n e) := by
  apply NoSp.of_all
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    cases prepare <;> decide +kernel

theorem body_stack {n e : Nat} (h : Supported n e) (prepare : Bool) :
    stackUse (body prepare n e) = 0 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    cases prepare <;> decide +kernel

end VG.Proof.Dsa.X86.Comb
