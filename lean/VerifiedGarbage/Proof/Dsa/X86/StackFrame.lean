module

public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Impl.Dsa.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.TCB.X86.State
import VerifiedGarbage.TCB.X86.Isa

/-! # Workspace frames that account for helper-call stack writes

Inside DSA's workspace only the listed ranges may change. Outside it,
changes are confined to the 32 bytes below the caller's stack pointer.
-/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Impl.Dsa.Layout

def callStack (sp : BitVec 32) : Region := ⟨(sp - 32#32).setWidth 64, 32⟩

def StackOuts (base : Addr) (sp : BitVec 32) (rs : List (Nat × Nat)) (m m' : Mem) : Prop :=
  ∀ x, (∀ r ∈ rs, ofs base x < r.1 ∨ r.1 + r.2 ≤ ofs base x) →
    (ofs base x < usedBytes ∨ ¬ (callStack sp).Contains x 1) → m' x = m x

/-- The helper needs twelve bytes for arguments/return and twenty for its
arithmetic workspace invariant. -/
def Pow.Room (sp : BitVec 32) (base : Addr) (size : Nat) : Prop :=
  32 ≤ sp.toNat ∧ (sp.toNat ≤ base.toNat ∨ base.toNat + size + 32 ≤ sp.toNat)

namespace StackOuts

theorem of_outs {base sp rs m m'} (O : Outs base rs m m') : StackOuts base sp rs m m' :=
  fun x h _ => O x h

theorem refl (base sp rs m) : StackOuts base sp rs m m := fun _ _ _ => rfl

theorem trans {base sp rs m₁ m₂ m₃} (A : StackOuts base sp rs m₁ m₂)
    (B : StackOuts base sp rs m₂ m₃) : StackOuts base sp rs m₁ m₃ :=
  fun x h hs => (B x h hs).trans (A x h hs)

theorem mono {base sp rs rs' m m'} (O : StackOuts base sp rs m m')
    (H : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) :
    StackOuts base sp rs' m m' := by
  intro x hx hs
  apply O x _ hs
  intro r hr
  obtain ⟨r', hr', lo, hi⟩ := H r hr
  have := hx r' hr'
  omega

theorem workspace {base sp rs m m'} (O : StackOuts base sp rs m m') :
    Outs base (rs ++ [(usedBytes, 2 ^ 64 - usedBytes)]) m m' := by
  intro x hx
  apply O x (fun r hr => hx r (List.mem_append_left _ hr))
  have H := hx (usedBytes, 2 ^ 64 - usedBytes) (List.mem_append_right _ (List.mem_singleton_self _))
  have B : ofs base x < 2 ^ 64 := (x - base).isLt
  exact .inl (by change ofs base x < 15712 ∨ 18446744073709551616 ≤ ofs base x at H; change ofs base x < 15712; omega)

theorem val32 {base sp rs m m'} (O : StackOuts base sp rs m m') {d k : Nat}
    (H : ∀ r ∈ rs, d + 4 * k ≤ r.1 ∨ r.1 + r.2 ≤ d) (hb : d + 4 * k ≤ usedBytes) :
    VG.Proof.Mont.val32 m' base d k = VG.Proof.Mont.val32 m base d k := by
  apply O.workspace.val32
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact H r hr
    · rw [List.mem_singleton.mp hr]; exact .inl hb
  · change d + 4 * k ≤ 15712 at hb
    omega

end StackOuts
end VG.Proof.Dsa.X86
