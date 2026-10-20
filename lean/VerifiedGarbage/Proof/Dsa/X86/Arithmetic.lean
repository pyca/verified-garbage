module

public import VerifiedGarbage.Impl.Dsa.X86.Arithmetic
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
import VerifiedGarbage.Proof.Mont.X86.ContextMul
import VerifiedGarbage.Proof.Mont.X86.ExponentInitMath
import VerifiedGarbage.Proof.Dsa.X86.Reduce
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Dsa.Arithmetic

/-! # Products and sums of ordinary DSA residues -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic VG.Impl.Dsa.X86

def productRanges (n : Nat) : List (Nat × Nat) :=
  [(slot n 7, 8 * n), (slot n 6, 8 * n), (slot n 1, 8 * n), (slot n 2, 16 * n + 4)]

theorem ordinaryMul_ok {n size m : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (hr2 : wordsVal s.mem base (slot n 4) n = 2 ^ (128 * n) % m) :
    WP isa (ordinaryMul n) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base (slot n 6) n =
        wordsVal s.mem base (slot n 5) n * wordsVal s.mem base (slot n 8) n % m ∧
      Outs base (productRanges n) s.mem t.mem ∧ Keeps clob s t := by
  unfold ordinaryMul
  refine WP.seq (WP.mono (context_mul_ok h (o := 7) (a := 5) (b := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hr2]; exact Nat.mod_lt _ (by have := h.gt_one; omega))) fun u ⟨cu, Ku, ltu, Vu⟩ => ?_)
  have Au : wordsVal u.mem base (slot n 7) n = wordsVal s.mem base (slot n 5) n * 2 ^ (64 * n) % m :=
    mont_encode h.coprime ltu (by rw [Vu, hr2])
  have Bu := context_slot_val h (i := 8) (by decide) (by decide) (by decide) (by decide) Ku
  refine WP.mono (context_mul_ok cu (o := 6) (a := 8) (b := 7)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ltu)
    fun t ⟨ct, Kt, ltt, Vt⟩ => ?_
  refine ⟨ct, ?_, ?_, (OpKeep.keeps Ku).trans (OpKeep.keeps Kt)⟩
  · have v := VG.Proof.Dsa.mont_scale (out := wordsVal t.mem base (slot n 6) n)
      (input := wordsVal s.mem base (slot n 8) n) (c := wordsVal s.mem base (slot n 5) n)
      h.coprime (by rw [Vt, Au, Bu])
    rw [Nat.mod_eq_of_lt ltt, Nat.mul_comm] at v
    exact v
  · have ou : Outs base (productRanges n) s.mem u.mem := Ku.mem.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [productRanges, contextMod, accLen, words] <;> omega)
    have ot : Outs base (productRanges n) u.mem t.mem := Kt.mem.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [productRanges, contextMod, accLen, words] <;> omega)
    exact ou.trans ot

theorem ordinaryAdd_ok {n size m : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (ha : wordsVal s.mem base (slot n 5) n < m)
    (hb : wordsVal s.mem base (slot n 8) n < m) :
    WP isa (ordinaryAdd n) s fun t =>
      Context n m base size t ∧ OpKeep (contextMod n) base (slot n 2) (slot n 6) s t ∧
      wordsVal t.mem base (slot n 6) n =
        (wordsVal s.mem base (slot n 5) n + wordsVal s.mem base (slot n 8) n) % m :=
  WP.mono (context_add_ok h (o := 6) (a := 5) (b := 8) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by omega)) fun _ ⟨c, K, V, _⟩ => ⟨c, K, V⟩

end VG.Proof.Dsa.X86
