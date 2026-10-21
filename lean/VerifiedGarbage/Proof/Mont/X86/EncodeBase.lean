module

public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
import VerifiedGarbage.Proof.Mont.X86.ContextMul
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.ExponentInitMath
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
public import VerifiedGarbage.Proof.Framework.Semantics

/-! Shared Montgomery initialization for ordinary powers and fixed-base combs. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86

def encodeRanges (n : Nat) : List (Nat × Nat) :=
  [(slot n 5, 8*n), (slot n 6, 8*n), (slot n 1, 8*n), (slot n 2, 16*n+4)]

theorem encodeRanges_val32 {n i k : Nat} {base : Addr} {s t : State}
    (O : Outs base (encodeRanges n) s.mem t.mem) (hi : i < 9) (hk : k ≤ 2*n)
    (h1 : i ≠ 1) (h2 : i ≠ 2) (h5 : i ≠ 5) (h6 : i ≠ 6) (hn : contextBytes n ≤ 2^64) :
    val32 t.mem base (slot n i) k = val32 s.mem base (slot n i) k := by
  apply O.val32
  · intro r hr
    simp only [encodeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    have a := slot_sep (n := n) h1
    have b := slot_sep (n := n) h2
    have c := slot_sep (n := n) h5
    have d := slot_sep (n := n) h6
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [stride] at * <;> omega
  · have bound := slot_bound (n := n) hi
    unfold stride at bound
    omega

theorem encodeBase_ok {n size m : Nat} {base : Addr} {s : State}
    (C : Context n m base size s)
    (one : wordsVal s.mem base (slot n 3) n = 1)
    (r2 : wordsVal s.mem base (slot n 4) n = 2^(128*n) % m) :
    WP isa (encodeBase n) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base (slot n 6) n = 2^(64*n) % m ∧
      wordsVal t.mem base (slot n 5) n = wordsVal s.mem base (slot n 5) n * 2^(64*n) % m ∧
      Outs base (encodeRanges n) s.mem t.mem ∧ Keeps clob s t := by
  unfold encodeBase
  refine WP.seq (WP.mono (context_mul_ok C (o := 6) (a := 4) (b := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [one]; exact C.gt_one)) fun u ⟨Cu, Ku, ltu, Vu⟩ => ?_)
  have Yu : wordsVal u.mem base (slot n 6) n = 2^(64*n) % m :=
    mont_one C.coprime ltu (by rw [Vu, one, r2, Nat.mul_one, Nat.mod_mod])
  have Ru : wordsVal u.mem base (slot n 4) n = 2^(128*n) % m := by
    rw [context_slot_val C (by decide) (by decide) (by decide) (by decide) Ku, r2]
  have Bu := context_slot_val C (i := 5) (by decide) (by decide) (by decide) (by decide) Ku
  refine WP.mono (context_mul_ok Cu (o := 5) (a := 5) (b := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [Ru]; exact Nat.mod_lt _ (by have := C.gt_one; omega))) fun t ⟨Ct, Kt, ltt, Vt⟩ => ?_
  refine ⟨Ct, ?_, mont_encode C.coprime ltt (by rw [Vt, Ru, Bu]), ?_, (OpKeep.keeps Ku).trans (OpKeep.keeps Kt)⟩
  · rw [context_slot_val Cu (by decide) (by decide) (by decide) (by decide) Kt, Yu]
  · have frame {a b : State} {o : Nat} (ho : o = 5 ∨ o = 6)
        (K : OpKeep (contextMod n) base (slot n 2) (slot n o) a b) :
        Outs base (encodeRanges n) a.mem b.mem := K.mem.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> rcases ho with rfl | rfl <;>
        simp [encodeRanges, contextMod, accLen, words] <;> omega)
    exact (frame (.inr rfl) Ku).trans (frame (.inl rfl) Kt)

end VG.Proof.Mont.X86.Dynamic
