module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

/-!
# Calls of code proven in the caller (PPC64LE)

Untrusted: everything here is checked by Lean. `WP.callOf` runs a call
from what its callee's code does from the call's entry (`State.callEntry`),
for an internal function whose proof is its caller's: the callee must leave
the link register as the call left it, which `WP.keepLr` gives of code with
no call or frame that writes it only around `adrSym` (`lrSafe`).
-/

@[expose] public section

namespace VG.PPC64LE

/-- A call of code that keeps the link register. -/
theorem WP.callOf {name : String} {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa c s.callEntry fun s₂ => s₂.lr = s.callEntry.lr ∧ Q s₂) : WP isa (.call name c) s Q := by
  obtain ⟨t, s₂, he, hlr, hq⟩ := h
  refine ⟨_, _, Exec.call (call_callEntry s) he ?_, hq⟩
  simp only [isa, ret]
  exact ite_eq_left_of_eq_true _ _ (eq_true hlr)

/-- Code that `lrSafe` accepts keeps the link register. -/
theorem WP.keepLr {c : Prog isa} {s : State} {Q : State → Prop} (hc : lrSafe c = true) (h : WP isa c s Q) :
    WP isa c s fun t => t.lr = s.lr ∧ Q t := by
  obtain ⟨tr, t, he, hq⟩ := h
  exact ⟨tr, t, he, Exec.lr_safe he hc, hq⟩

/-- A call of code that `lrSafe` accepts. -/
theorem WP.callSafe {name : String} {c : Prog isa} {s : State} {Q : State → Prop} (hc : lrSafe c = true)
    (h : WP isa c s.callEntry Q) : WP isa (.call name c) s Q :=
  WP.callOf (WP.keepLr hc h)

end VG.PPC64LE
