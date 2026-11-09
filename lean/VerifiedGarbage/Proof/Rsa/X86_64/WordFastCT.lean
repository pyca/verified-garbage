module

public import VerifiedGarbage.Proof.Rsa.X86_64.WordFast
public import VerifiedGarbage.Proof.Rsa.X86_64.WordInitCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.WordFast
meta import VerifiedGarbage.Proof.Rsa.X86_64.WordInitCT

/-! # Constant-time normalization and remainder computation -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.WordDivide

open VG VG.X86_64 VG.Impl.Rsa.X86_64.WordDivide
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def FastPre (p : Pub) (s : State) : Prop := Ws s p.B p.Z p.W ∧ slot p.W 17 ≤ p.Z ∧ 4 ≤ p.W

theorem fast_ct : RelCT isa (Two FastPre) (.seq (.block normalize) code) fun _ _ => True := by
  refine RelCT.seq (R := Two Pre) ?_ code_ct
  unfold normalize
  rw [List.append_assoc]
  refine ws_block_ct Pub.B Pub.Z Pub.W (fun _ _ h => h.1) (by taint_decide) ?_
  intro p s h
  have hn := h.1.scr.nowrap
  have hm := h.1.sl (j := aM) (by decide)
  refine WP.mono (normalize_ok h.1 h.2.2) fun t ⟨mt, kt⟩ => ?_
  have ot : Outside p.B (slot p.W aM + 8 * (p.W / 2 - 1)) 8 s.mem t.mem := by
    rw [mt]; exact writeW_outside _ _ _ (by omega_arith)
  have ft : Frm p.B [(slot p.W aM, 8 * (p.W + 2))] s.mem t.mem := by
    apply cover (Frm.of_outside ot (by simp : (slot p.W aM + 8 * (p.W / 2 - 1), 8) ∈
      [(slot p.W aM + 8 * (p.W / 2 - 1), 8)]))
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact ⟨(slot p.W aM, 8 * (p.W + 2)), by simp, by omega_arith, by omega_arith⟩
  refine ⟨h.1.congr ft (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact Mut.ofSlot _ _ _)
    kt (by decide), h.2.1, h.2.2, ?_⟩
  rw [mt, word_writeW_self]; exact high_or _

end VG.Proof.Rsa.X86_64.WordDivide
