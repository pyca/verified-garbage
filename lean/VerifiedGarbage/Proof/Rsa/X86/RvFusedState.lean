module

import VerifiedGarbage.Proof.Rsa.X86.RvFusedSmall
public import VerifiedGarbage.Proof.Rsa.RecoverFused
import VerifiedGarbage.Proof.Rsa.X86.RvOps
import VerifiedGarbage.Proof.Rsa.X86.RvScalarOps
public import VerifiedGarbage.Proof.Rsa.RecoverExp
public import VerifiedGarbage.Proof.Rsa.X86.RvMont
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass

/-! State tracked by the fused pass. The saved root may be stale when the
success flag is clear; it is always a bounded Montgomery representation. -/
@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (b2n)

abbrev fusedKeep : List Nat := [0,mY] ++ liveM
abbrev fusedKeepSlots : List Nat := [sInv,sCnt,sTc,sCand,sWin,sDone,sOk]

/-- Observing a scratch array does not read or change the machine. -/
theorem KS.observe_w {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {live liveW ls : List Nat}
    (h : KS g s0 A live AW liveW V ls s) (j : Nat) (hj : j < nArr) :
    KS g s0 (upd A j (num s.mem g.B g.w j)) (j::live) AW liveW V ls s := by
  refine {h with arrs := ?_, live_lt := ?_}
  · intro i hi
    by_cases e : i = j
    · subst e; rw [upd_self]
    · rw [upd_ne _ _ e]
      exact h.arrs i ((List.mem_cons.mp hi).resolve_left e)
  · intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact hj
    · exact h.live_lt i hi

def fusedV (V : Nat → Nat) (st : VG.Proof.Rsa.Fused.State) : Nat → Nat :=
  upd (upd V sDone (b2n st.done)) sOk (b2n st.root.isSome)

def fusedA (A : Nat → Nat) (n R y z : Nat) : Nat → Nat :=
  upd (upd A 0 (z*R % n)) mY (y*R % n)

def FI (g : Geo) (s0 : State) (A AW V : Nat → Nat) (n : Nat)
    (st : VG.Proof.Rsa.Fused.State) (s : State) : Prop :=
  ∃ z, z < n ∧ (∀ r, st.root = some r → z = r) ∧
    KS g s0 (fusedA A n (2^(64*g.n)) st.value z) fusedKeep AW [wRc,wR]
      (fusedV V st) fusedKeepSlots s

end VG.Proof.Rsa.X86.Recover
