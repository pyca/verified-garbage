module

public import VerifiedGarbage.Impl.Dsa.X86.Reduce
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.DynamicAdd
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The residue invariant for streaming big-endian input -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic VG.Impl.Dsa.X86

theorem context_add_ok {n size m o a b : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (ho : o < 9) (ha : a < 9) (hb : b < 9)
    (ho0 : o ≠ 0) (ho1 : o ≠ 1) (ho2 : o ≠ 2) (ha2 : a ≠ 2) (hb2 : b ≠ 2)
    (hAB : wordsVal s.mem base (slot n a) n + wordsVal s.mem base (slot n b) n < 2 * m) :
    WP isa (addW (contextMod n) (slot n 2) (slot n o) (slot n a) (slot n b)) s fun t =>
      Context n m base size t ∧ OpKeep (contextMod n) base (slot n 2) (slot n o) s t ∧
      wordsVal t.mem base (slot n o) n =
        (wordsVal s.mem base (slot n a) n + wordsVal s.mem base (slot n b) n) % m ∧
      Outs base [(slot n o, 8 * n), (slot n 1, 8 * n), (slot n 2, 8 * n + 4)] s.mem t.mem ∧
      t.gpr .ebx = s.gpr .ebx := by
  refine WP.mono (VG.Proof.Mont.X86.Dynamic.add_ok h.scr h.modulus
    (context_opLay h.size_le ho ha hb ho2 ha2 hb2 ho1) hAB) fun t ⟨K, V, F, B⟩ => ?_
  refine ⟨h.keep ho0 K, K, V, ?_, B⟩
  simpa only [contextMod, words, show 4 * (2 * n + 1) = 8 * n + 4 by omega] using F

theorem doubles_ok {n size m : Nat} {base : Addr} : ∀ (k : Nat) {s : State},
    Context n m base size s → wordsVal s.mem base (slot n 6) n < m →
    WP isa (doubles n k) s fun t =>
      Context n m base size t ∧ OpKeep (contextMod n) base (slot n 2) (slot n 6) s t ∧
      wordsVal t.mem base (slot n 6) n = 2 ^ k * wordsVal s.mem base (slot n 6) n % m ∧
      t.gpr .ebx = s.gpr .ebx
  | 0, s, h, hv => WP.block_nil ⟨h, OpKeep.of (Keeps.refl [] s) (by decide) (Outs.refl _ _ _),
      by rw [Nat.pow_zero, Nat.one_mul, Nat.mod_eq_of_lt hv], rfl⟩
  | k + 1, s, h, hv => by
    have m1 := h.gt_one
    refine WP.seq (WP.mono (context_add_ok h (o := 6) (a := 6) (b := 6)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by omega)) fun u ⟨cu, Ku, Vu, _, Bu⟩ => ?_)
    have hvu : wordsVal u.mem base (slot n 6) n < m := by rw [Vu]; exact Nat.mod_lt _ (by omega)
    refine WP.mono (doubles_ok k cu hvu) fun t ⟨ct, Kt, Vt, Bt⟩ => ⟨ct, ?_, ?_, Bt.trans Bu⟩
    · exact ⟨fun r hr => (Kt.gpr r hr).trans (Ku.gpr r hr), Kt.rd.trans Ku.rd, Kt.wr.trans Ku.wr,
        Ku.mem.trans Kt.mem⟩
    · rw [Vt, Vu, ← Nat.two_mul, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc, ← Nat.pow_succ]

theorem reduceStep_ok {n size m : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (hv : wordsVal s.mem base (slot n 6) n < m)
    (hb : wordsVal s.mem base (slot n 7) n < m) :
    WP isa (reduceStep n) s fun t =>
      Context n m base size t ∧ OpKeep (contextMod n) base (slot n 2) (slot n 6) s t ∧
      wordsVal t.mem base (slot n 6) n =
        (256 * wordsVal s.mem base (slot n 6) n + wordsVal s.mem base (slot n 7) n) % m ∧
      t.gpr .ebx = s.gpr .ebx := by
  unfold reduceStep
  refine WP.seq (WP.mono (doubles_ok 8 h hv) fun u ⟨cu, Ku, Vu, Bu⟩ => ?_)
  have bu := context_slot_val h (o := 6) (i := 7) (by decide) (by decide) (by decide) (by decide) Ku
  have vu : wordsVal u.mem base (slot n 6) n < m := by
    rw [Vu]; exact Nat.mod_lt _ (by have := h.gt_one; omega)
  refine WP.mono (context_add_ok cu (o := 6) (a := 6) (b := 7)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [bu]; omega)) fun t ⟨ct, Kt, Vt, _, Bt⟩ => ?_
  refine ⟨ct, ⟨fun r hr => (Kt.gpr r hr).trans (Ku.gpr r hr), Kt.rd.trans Ku.rd, Kt.wr.trans Ku.wr,
    Ku.mem.trans Kt.mem⟩, ?_, Bt.trans Bu⟩
  rw [Vt, Vu, bu, Nat.mod_add_mod]

end VG.Proof.Dsa.X86
