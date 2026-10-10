import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseEngine
import VerifiedGarbage.Proof.Ed25519.AArch64.CTSupport

/-! Expanding the secret scalar's bits, the comb and the encoding have a public
trace. The loops' counters (`x19`, and `x1` for the doublings) and the table index are
public, every address is the workspace pointer `x0` plus a constant or a counter, or the
static's address plus a constant and the counter, and the digits only reach masks. Each part
has its own taint check, so that X25519's fixed-base engine shares the comb's
(`combMultiply_ct`). -/

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
