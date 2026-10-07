import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseEngine
import VerifiedGarbage.Proof.Ed25519.AArch64.CTSupport

/-! Expanding the secret scalar's bits, the comb and the encoding have a public
trace. The loops' counters (`x19`, and `x1` for the doublings) and the table index are
public, every address is the workspace pointer `x0` plus a constant or a counter, or the
static's address plus a constant and the counter, and the digits only reach masks: one taint
check covers the whole engine. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def BaseEnginePre (base k T : Addr) (s : State) : Prop :=
  Scr s base ∧ s.gpr .x1 = k ∧
    (∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1) ∧
    (∀ q < 32, 8192 ≤ ofs base (off k q)) ∧ TblAt s base T ∧ s.syms combSym = T

theorem scalarBaseEngine_ct (base k T : Addr) :
    CT (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y)
      scalarBaseEngine (fun _ _ => True) := by
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

end VG.Proof.Ed25519.AArch64
