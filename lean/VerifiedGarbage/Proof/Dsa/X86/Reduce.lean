module

public import VerifiedGarbage.Impl.Dsa.X86.Reduce
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
public import VerifiedGarbage.Proof.Mont.X86.PowerLoop

/-! # The residue invariant for streaming big-endian input -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic VG.Impl.Dsa.X86

theorem context_add_ok {n size m o a b : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (ho : o < 9) (ha : a < 9) (hb : b < 9)
    (ho0 : o ≠ 0) (ho1 : o ≠ 1) (ho2 : o ≠ 2) (ha2 : a ≠ 2) (hb2 : b ≠ 2)
    (hAB : wordsVal s.mem base (slot n a) n + wordsVal s.mem base (slot n b) n < 2 * m) :
    WP isa (.block (add (contextMod n) (slot n 2) (slot n o) (slot n a) (slot n b))) s fun t =>
      Context n m base size t ∧ OpKeep (contextMod n) base (slot n 2) (slot n o) s t ∧
      wordsVal t.mem base (slot n o) n =
        (wordsVal s.mem base (slot n a) n + wordsVal s.mem base (slot n b) n) % m := by
  refine WP.mono (VG.Proof.Mont.X86.Dynamic.add_ok h.scr h.modulus
    (context_opLay h.size_le ho ha hb ho2 ha2 hb2 ho1) hAB) fun t ⟨K, V⟩ => ?_
  exact ⟨h.keep ho0 K, K, V⟩

theorem doubles_ok {n size m : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (hv : wordsVal s.mem base (slot n 6) n < m) :
    ∀ k, WP isa (.block (doubles n (slot n 6) k)) s fun t =>
      Context n m base size t ∧ OpKeep (contextMod n) base (slot n 2) (slot n 6) s t ∧
      wordsVal t.mem base (slot n 6) n = 2 ^ k * wordsVal s.mem base (slot n 6) n % m
  | 0 => by
    refine WP.block_nil ⟨h, ⟨fun _ _ => rfl, rfl, rfl, Outs.refl _ _ _⟩, ?_⟩
    rw [Nat.pow_zero, Nat.one_mul, Nat.mod_eq_of_lt hv]
  | k + 1 => by
    rw [doubles]
    refine WP.block_append (WP.mono (doubles_ok h hv k) fun u ⟨cu, Ku, Vu⟩ => ?_)
    have hu : wordsVal u.mem base (slot n 6) n < m := by
      rw [Vu]; exact Nat.mod_lt _ (by have := h.gt_one; omega)
    refine WP.mono (context_add_ok cu (o := 6) (a := 6) (b := 6)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by omega)) fun t ⟨ct, Kt, Vt⟩ => ?_
    refine ⟨ct, ⟨fun r hr => (Kt.gpr r hr).trans (Ku.gpr r hr), Kt.rd.trans Ku.rd, Kt.wr.trans Ku.wr,
      Ku.mem.trans Kt.mem⟩, ?_⟩
    rw [Vt, ← Nat.two_mul, Vu, double_residue]

theorem reduceStep_ok {n size m : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (hv : wordsVal s.mem base (slot n 6) n < m)
    (hb : wordsVal s.mem base (slot n 7) n < m) :
    WP isa (.block (reduceStep n)) s fun t =>
      Context n m base size t ∧ OpKeep (contextMod n) base (slot n 2) (slot n 6) s t ∧
      wordsVal t.mem base (slot n 6) n =
        (256 * wordsVal s.mem base (slot n 6) n + wordsVal s.mem base (slot n 7) n) % m := by
  unfold reduceStep
  refine WP.block_append (WP.mono (doubles_ok h hv 8) fun u ⟨cu, Ku, Vu⟩ => ?_)
  have bu := context_slot_val h (i := 7) (by decide) (by decide) (by decide) (by decide) Ku
  have vu : wordsVal u.mem base (slot n 6) n < m := by
    rw [Vu]; exact Nat.mod_lt _ (by have := h.gt_one; omega)
  refine WP.mono (context_add_ok cu (o := 6) (a := 6) (b := 7)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [bu]; omega)) fun t ⟨ct, Kt, Vt⟩ => ?_
  refine ⟨ct, ⟨fun r hr => (Kt.gpr r hr).trans (Ku.gpr r hr), Kt.rd.trans Ku.rd, Kt.wr.trans Ku.wr,
    Ku.mem.trans Kt.mem⟩, ?_⟩
  rw [Vt, Vu, bu, Nat.mod_add_mod]

end VG.Proof.Dsa.X86
