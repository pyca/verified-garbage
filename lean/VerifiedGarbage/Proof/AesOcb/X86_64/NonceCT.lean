import VerifiedGarbage.Proof.AesOcb.X86_64.CTBase
import VerifiedGarbage.Proof.AesOcb.X86_64.Nonce

/-!
# AES-OCB on x86-64: `Offset_0` is constant time

Untrusted: everything here is checked by Lean. The nonce block and the
stretch pass the taint analysis from the public slots (`rel_taintC`); the
call of `vg_aes_encrypt_blocks` has the same arguments in both runs
(`callBlocks_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.Impl.AesOcb.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)

theorem nonce_rel (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) (hn : n ≤ 2 ^ 64)
    (h1 : 1 ≤ nl) (h15 : nl ≤ 15) (ht : tl < 2 ^ 64) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → One K W SP R N A D nl n tl s₁ ∧ One K W SP R N A D nl n tl s₂ ∧
      Buf W SP s₁ N nl ∧ Buf W SP s₂ N nl) :
    RelCT isa P (nonce (callees v)) fun _ _ => True := by
  have step : ∀ s, One K W SP R N A D nl n tl s → Buf W SP s N nl →
      WP isa nonceBlock s (One K W SP R N A D nl n tl) := fun s o hB =>
    WP.mono (nonceBlock_ok L o.env o.sl.nonce o.sl.nlen o.sl.tl h1 h15 ht hB) fun s' Q =>
      o.step L hDW (o.env.keep (fun r hr => Q.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
        (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
        (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
        Q.rd Q.wr) Q.wr (Q.frame.sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
          · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_wB (by decide) (by decide)⟩)
  have a := (rel_taintC [] [] hDW hn (fun s₁ s₂ h => Both.of (hP s₁ s₂ h).1 (hP s₁ s₂ h).2.1)
    (c := nonceBlock) ⟨_, by taint_decide⟩).wp (F₁ := One K W SP R N A D nl n tl) (F₂ := One K W SP R N A D nl n tl)
    fun s₁ s₂ h => ⟨step s₁ (hP s₁ s₂ h).1 (hP s₁ s₂ h).2.2.1, step s₂ (hP s₁ s₂ h).2.1 (hP s₁ s₂ h).2.2.2⟩
  have call : ∀ s, One K W SP R N A D nl n tl s →
      WP isa (callBlocks (callees v).enc (oneBlock tmpO)) s (One K W SP R N A D nl n tl) := fun s o =>
    WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encDepth L o.env hR o.sl.rounds
      (oneBlock_ok o.env.r15 tmpO (by decide)) (dstW L o.env.perm (d := tmpO) (n := 1) (by decide))) fun s' Q => by
      have E' := o.env.of_saved Q.saved Q.rd Q.wr
      refine o.step L hDW E' Q.wr (Q.frame.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
      · exact ⟨_, by simp, sub_wC (by decide) (by decide)⟩
      · rw [o.env.rsp]; exact ⟨_, by simp, fun _ h => h⟩
  have b := (callBlocks_rel (b := (callees v).enc) v.encOk v.encCt L hR hDW hn [] [] (args := oneBlock tmpO) ⟨_, by taint_decide⟩
    (D' := W + BitVec.ofNat 64 tmpO) (k := 1)
    (P := fun s₁ s₂ => True ∧ One K W SP R N A D nl n tl s₁ ∧ One K W SP R N A D nl n tl s₂) fun s₁ s₂ h =>
      ⟨Both.of h.2.1 h.2.2, oneBlock_ok h.2.1.env.r15 tmpO (by decide), oneBlock_ok h.2.2.env.r15 tmpO (by decide),
        dstW L h.2.1.env.perm (by decide), dstW L h.2.2.env.perm (by decide)⟩).wp
    (F₁ := One K W SP R N A D nl n tl) (F₂ := One K W SP R N A D nl n tl)
    fun s₁ s₂ h => ⟨call s₁ h.2.1, call s₂ h.2.2⟩
  have c := rel_taintC [] [] hDW hn (fun s₁ s₂ (h : True ∧ One K W SP R N A D nl n tl s₁ ∧ One K W SP R N A D nl n tl s₂) =>
    Both.of h.2.1 h.2.2) (c := .block offset0) ⟨_, by taint_decide⟩
  exact RelCT.seq a (RelCT.seq b c)

end VG.Proof.AesOcb.X86_64
