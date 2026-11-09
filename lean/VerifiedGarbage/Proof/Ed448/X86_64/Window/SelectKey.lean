module

import VerifiedGarbage.Proof.Ed448.X86_64.Window.DirectKey
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Memory
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import VerifiedGarbage.Impl.Ed448.X86_64.WindowRegister
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Mask

/-! Constant-time selection from the runtime projective table. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Window

open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window VG.Proof.Ed448.X86_64
open VG.Proof.Ed448 (pt)
open VG.Proof.X448.X86_64 (Scr Index Env E F Keep mask cswapE opSwap)
open VG.Impl.X448.X86_64 (slot)

theorem coord_keep {base : Addr} {s u : State} (h : Keep base s u) {i c : Nat}
    (hi : i < 17) (hc : c < 3) : F u.mem base (tabOffset i c) = F s.mem base (tabOffset i c) := by
  unfold F
  rw [h.mem.fe (by simp only [tabOffset, TAB]; omega) (by simp only [tabOffset, TAB]; omega)]

def KeyKeeps (e e' : Env) : Prop :=
  ∀ j : Index, j ≠ 3 → j ≠ 4 → j ≠ 5 → j ≠ 8 → j ≠ 9 → j ≠ 10 → e' j = e j

end VG.Proof.Ed448.X86_64.Window
