module
public import VerifiedGarbage.Proof.Rsa.X86.RvMontGeometry
import Mathlib.Tactic.Finiteness.Attr
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp


/-! # Recovering Montgomery readiness from the tracked workspace -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat} {m : Nat}

theorem KS.montReady (h : KS g s0 A live AW liveW V ls s)
    (hm : mBase ∈ live) (hi : sInv ∈ ls) (value : A mBase = m)
    (bound : m < 2 ^ (64 * g.n)) (inverse : (m * V sInv + 1) % 2 ^ 32 = 0) : MR g m s := by
  refine ⟨h.ws, by have := h.lower; omega, (h.arrs mBase hm).trans value, bound, ?_⟩
  change (m * slot s.mem g.B sInv + 1) % 2 ^ 32 = 0
  rw [h.sl sInv hi]
  exact inverse

theorem KS.trackInverse (h : KS g s0 A live AW liveW V ls s) (mr : MR g m s)
    (fresh : sInv ∉ ls) :
    ∃ I, KS g s0 A live AW liveW (upd V sInv I) (sInv :: ls) s ∧
      (m * I + 1) % 2 ^ 32 = 0 := by
  refine ⟨slot s.mem g.B sInv, ⟨h.ws, h.lower, h.upper, h.frame, h.rest,
    h.arrs, h.arrsW, ?_, h.live_lt, h.liveW_lt, ?_⟩, mr.inverse⟩
  · intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · rw [upd_self]
    · rw [upd_ne _ _ (show d ≠ sInv from fun eq => fresh (eq ▸ hd))]
      exact h.sl d hd
  · intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · decide
    · exact h.ls_ok d hd

end
end VG.Proof.Rsa.X86.Recover
