module

import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseEngine
meta import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseEngine
public import VerifiedGarbage.Proof.Ed25519.AArch64.CTSupport
public import VerifiedGarbage.Impl.Ed25519.AArch64.ScalarBase
public import VerifiedGarbage.Proof.Ed25519.AArch64.CombSelect
meta import VerifiedGarbage.Proof.Ed25519.AArch64.CTSupport
import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Ed25519.AArch64.BitByte
import VerifiedGarbage.Proof.Ed25519.AArch64.Bits
import VerifiedGarbage.Proof.Ed25519.AArch64.CombDigit
import VerifiedGarbage.Proof.Ed25519.AArch64.CombEntry
import VerifiedGarbage.Proof.Ed25519.AArch64.CombLoop
import VerifiedGarbage.Proof.Ed25519.AArch64.Freeze
import VerifiedGarbage.Proof.Ed25519.AArch64.PointLoop
import VerifiedGarbage.Proof.Ed25519.AArch64.PointSelect
import VerifiedGarbage.Proof.Ed25519.AArch64.Swap
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.Field64
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.Csub
import VerifiedGarbage.Proof.Mont.AArch64.Rounds
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Add
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Cmadd
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Exec
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Mul
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Mux
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Sqr
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Sub
import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Flags
import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Formula
import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Step
import VerifiedGarbage.Proof.X25519.AArch64.Ladder
meta import VerifiedGarbage.Proof.Ed25519.AArch64.BitByte
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Bits
meta import VerifiedGarbage.Proof.Ed25519.AArch64.CombDigit
meta import VerifiedGarbage.Proof.Ed25519.AArch64.CombEntry
meta import VerifiedGarbage.Proof.Ed25519.AArch64.CombLoop
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Freeze
meta import VerifiedGarbage.Proof.Ed25519.AArch64.PointLoop
meta import VerifiedGarbage.Proof.Ed25519.AArch64.PointSelect
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Swap
meta import VerifiedGarbage.Proof.Ed25519.Bytes
meta import VerifiedGarbage.Proof.Ed25519.Field64
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.BitByte
meta import VerifiedGarbage.Proof.Framework.Pratt
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.AArch64.Blocks
meta import VerifiedGarbage.Proof.Mont.AArch64.Chain
meta import VerifiedGarbage.Proof.Mont.AArch64.Csub
meta import VerifiedGarbage.Proof.Mont.AArch64.Rounds
meta import VerifiedGarbage.Proof.X25519.AArch64.Alt.Add
meta import VerifiedGarbage.Proof.X25519.AArch64.Alt.Cmadd
meta import VerifiedGarbage.Proof.X25519.AArch64.Alt.Exec
meta import VerifiedGarbage.Proof.X25519.AArch64.Alt.Mul
meta import VerifiedGarbage.Proof.X25519.AArch64.Alt.Mux
meta import VerifiedGarbage.Proof.X25519.AArch64.Alt.Sqr
meta import VerifiedGarbage.Proof.X25519.AArch64.Alt.Sub
meta import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Flags
meta import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Formula
meta import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Step
meta import VerifiedGarbage.Proof.X25519.AArch64.Ladder

/-! Expanding the secret scalar's bits, the comb and the encoding have a public
trace. The loops' counters (`x19`, and `x1` for the doublings) and the table index are
public, every address is the workspace pointer `x0` plus a constant or a counter, or the
static's address plus a constant and the counter, and the digits only reach masks. Each part
has its own taint check, so that X25519's fixed-base engine shares the comb's
(`combMultiply_ct`). -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def BaseEnginePre (base k T : Addr) (s : State) : Prop :=
  Scr s base ∧ s.gpr .x1 = k ∧
    (∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1) ∧
    (∀ q < 32, 8192 ≤ ofs base (off k q)) ∧ TblAt s base T ∧ s.syms combSym = T

/-- The comb, from the workspace pointer `x0` and the static's address: `x0` is the same in both
runs after it. -/
theorem combMultiply_ct (base T : Addr) :
    CT (fun x y => (Scr x base ∧ x.syms combSym = T) ∧ (Scr y base ∧ y.syms combSym = T))
      combMultiply (fun x y => ∀ r ∈ [Reg.x0], x.gpr r = y.gpr r) := by
  apply CT.taintSRegs (L := [combSym]) (τ := Taint.ofRegs [.x0]) _ [.x0] (by taint_decide)
  intro x y h
  refine ⟨agree_ofRegs fun r hr => ?_, fun n hn => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h.1.1.x0.trans h.2.1.x0.symm
  · simp only [List.mem_singleton] at hn
    subst hn
    exact h.1.2.trans h.2.2.symm

/-- The comb of a scalar whose bits 0–2 are clear (`combMultiplyClamped`), as `combMultiply_ct`. -/
theorem combMultiplyClamped_ct (base T : Addr) :
    CT (fun x y => (Scr x base ∧ x.syms combSym = T) ∧ (Scr y base ∧ y.syms combSym = T))
      combMultiplyClamped (fun x y => ∀ r ∈ [Reg.x0], x.gpr r = y.gpr r) := by
  apply CT.taintSRegs (L := [combSym]) (τ := Taint.ofRegs [.x0]) _ [.x0] (by taint_decide)
  intro x y h
  refine ⟨agree_ofRegs fun r hr => ?_, fun n hn => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h.1.1.x0.trans h.2.1.x0.symm
  · simp only [List.mem_singleton] at hn
    subst hn
    exact h.1.2.trans h.2.2.symm

/-- The preparation: a public trace, and the comb's start in each run. -/
theorem scalarBasePrepare_ct (base k T : Addr) :
    CT (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y) scalarBasePrepare
      (fun x y => (Scr x base ∧ x.syms combSym = T) ∧ (Scr y base ∧ y.syms combSym = T)) := by
  have hc : CT (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y) scalarBasePrepare
      (fun _ _ => True) := by
    apply CT.taintS (L := [combSym]) (Taint.ofRegs [.x0, .x1]) _ (by taint_decide)
    intro x y h
    refine ⟨agree_ofRegs fun r hr => ?_, fun n hn => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1.1.x0.trans h.2.1.x0.symm
      · exact h.1.2.1.trans h.2.2.1.symm
    · simp only [List.mem_singleton] at hn
      subst hn
      exact h.1.2.2.2.2.2.trans h.2.2.2.2.2.2.symm
  have hw : ∀ s, BaseEnginePre base k T s →
      WP isa scalarBasePrepare s (fun t => Scr t base ∧ t.syms combSym = T) := fun s h =>
    WP.mono_syms (scalarBasePrepare_ok h.1 h.2.1 h.2.2.1 h.2.2.2.1) fun _ ⟨kt, _, _⟩ syt =>
      ⟨kt.scratch h.1, by rw [syt]; exact h.2.2.2.2.2⟩
  exact (hc.wp fun x y h => ⟨hw x h.1, hw y h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- The engine: the preparation, the comb (`combMultiply_ct`) and the encoding, each with a
public trace. -/
theorem scalarBaseEngine_ct (base k T : Addr) :
    CT (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y)
      scalarBaseEngine (fun _ _ => True) := by
  rw [scalarBaseEngine]
  refine CT.seq (scalarBasePrepare_ct base k T) (CT.seq (combMultiply_ct base T) ?_)
  exact CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_ofRegs h) (by taint_decide)

end VG.Proof.Ed25519.AArch64
