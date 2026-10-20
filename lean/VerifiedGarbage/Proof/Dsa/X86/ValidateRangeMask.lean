module
public import VerifiedGarbage.Impl.Dsa.X86.Validate
public import VerifiedGarbage.Proof.Dsa.X86.Checks

import VerifiedGarbage.Proof.Dsa.X86.ValidateLower
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # Range masks for private scalars and public group elements -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem validation_tmp_whole {s t : State} {base : Addr} {n i : Nat}
    (O : Outs base [(slot n i, 8 * n), (Layout.field .mask, 4)] s.mem t.mem) (hi : i < 9) :
    Outs base [(0, contextBytes n), (Layout.field .mask, 4)] s.mem t.mem := by
  have b := slot_bound (n := n) hi
  simp only [stride] at b
  intro x hx
  apply O x
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have H := hx (0, contextBytes n) (by simp)
    omega
  · exact hx _ (by simp)

theorem rangeMask_ok {s : State} {base : Addr} {size n : Nat}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size) (hn : 0 < n) (hn48 : n ≤ 48)
    (aboveOne : Bool) :
    WP isa (.seq (checkRange n (slot n 5) (slot n 0) (Layout.field .mask))
      (if aboveOne then Validate.lowerTwo n else .block [])) s fun t =>
      flagW base (Layout.field .mask) t = flagW base (Layout.field .mask) s &&&
        mask32 ((if aboveOne then 1 else 0) < wordsVal s.mem base (slot n 5) n ∧
          wordsVal s.mem base (slot n 5) n < wordsVal s.mem base (slot n 0) n) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧
      Outs base [(0, contextBytes n), (Layout.field .mask, 4)] s.mem t.mem := by
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn48
  have hsize : 8256 ≤ size := hz
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have b5 := slot_bound (n := n) (i := 5) (by decide)
  simp only [stride] at b0 b5
  refine WP.seq (WP.mono (VG.Proof.Dsa.X86.checkRange_ok n (Layout.field .mask) hs hn
    (by omega) (by omega) (by change 8248 ≤ size; omega)) fun u ⟨Vu, Ku, Ou⟩ => ?_)
  cases aboveOne with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    exact WP.block_nil ⟨Vu, Ku, Outs.of_outside Ou (by simp)⟩
  | true =>
    simp only [ite_true]
    refine WP.mono (lowerTwo_ok (hs.of_keeps Ku (by decide)) hz hn hn48) fun t ⟨Vt, Kt, Ot⟩ => ?_
    refine ⟨?_, Ku.trans (Kt.mono (by decide)), (Outs.of_outside Ou (by simp)).trans (validation_tmp_whole Ot (by decide))⟩
    rw [Vt, Vu, Ou.wordsVal (.inl (by change slot n 5 + 8 * n ≤ 8244; omega)) (by omega),
      BitVec.and_assoc, mask32_and]
    have he : ((0 < wordsVal s.mem base (slot n 5) n ∧
        wordsVal s.mem base (slot n 5) n < wordsVal s.mem base (slot n 0) n) ∧
        2 ≤ wordsVal s.mem base (slot n 5) n) ↔
      (1 < wordsVal s.mem base (slot n 5) n ∧ wordsVal s.mem base (slot n 5) n < wordsVal s.mem base (slot n 0) n) := by omega
    simp only [mask32, he]

end VG.Proof.Dsa.X86
