import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.OpenCrypt

/-!
# ChaCha20 and Poly1305 together (x86-64): `openStitched` is correct

As `open_correct`, with `cryptO` (`cryptO_ok`) in place of `open`'s
`macPadLengths` and `crypt`, which it does at once.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.ChaCha20Poly1305 (pad16 macData polyKeyGen)

theorem openStitched_correct (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre false s₀) :
    WP isa (openStitched v.callee v.poly) s₀ fun s' => abiPreserved s₀ s' ∧ openX86_64.post s₀ s' := by
  have hL' := (Nat.le_of_lt (s₀.gpr .r9).isLt)
  refine WP.seq (WP.mono_mx (by decide +kernel) (entry_ok hp) fun s₀' e₀ mx₀ => ?_)
  subst e₀
  refine WP.seq (WP.mono_mx (prologue_mx v) (prologue_ok v hp) fun s₁ h₁ mx₁ => ?_)
  have hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.fine (by rdisj_all) (Nat.le_of_lt (s₀.gpr .rcx).isLt)
  refine WP.seq (WP.mono (macPad_ok v.poly hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩ (srcA hp)
    h₁.inv.r15 h₁.inv.rsp h₁.inv.rd h₁.inv.wr h₁.rbx (by rw [h₁.rbp]; exact hRDX s₀))
    fun s₂ ⟨cs₂, rd₂, wr₂, f₂, mx₂, r₂⟩ => ?_)
  have i₂ := mac_inv hp h₁.inv cs₂ rd₂ wr₂ f₂
  have D₂ : bytesAt s₂.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame f₂ (by rdisj_all) hL', bytesAt_frame h₁.fine (by rdisj_all) hL']
  refine WP.seq (WP.mono_mx (by decide +kernel) (lengths_ok hp i₂ (by rw [cs₂ _ (by simp [calleeSaved]),
    h₁.rbp])) fun s₃ ⟨i₃, _, f₃, len₃⟩ mx₃ => ?_)
  have D₃ : bytesAt s₃.mem (dp s₀) (L s₀) = D s₀ := by rw [bytesAt_frame f₃ (by rdisj_all) hL', D₂]
  have st₃ : stateAt s₃.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame f₃ (by rdisj_all), stateAt_frame f₂ (by rdisj_all), h₁.st]
  have hM := Nat.le_trans (mOf_le v.callee.fold (L s₀)) v.fold_le
  have ks₃ := ks_frame f₃ (by rdisj_all) hM (ks_frame f₂ (by rdisj_all) hM h₁.ks)
  have R₃ := Repr.frame f₃ (by rdisj_all) (r₂ (otk s₀) [] h₁.poly)
  refine WP.seq (WP.mono (cryptO_ok v hp i₃ st₃ ks₃ R₃) fun s₆ ⟨i₆, f₆, pt₆, R₆, mx₆⟩ => ?_)
  refine WP.seq (WP.mono_mx (by decide +kernel) (finalizeTo_ok hp i₆ (out := 48) (.inl (by omega_using [])))
    fun s₇ ⟨cs₇, rd₇, wr₇, rdi₇, rcx₇, f₇, tag₇⟩ mx₇ => ?_)
  refine WP.block_append (WP.mono_mx (by decide +kernel) (compare_ok hp rcx₇
    (by rw [cs₇ _ (by simp [calleeSaved]), i₆.r12]) (by rw [rd₇, i₆.rd])
    (by rw [wr₇, i₆.wr])) fun s₈ ⟨rax₈, g₈, m₈, rd₈, wr₈⟩ mx₈ => ?_)
  refine WP.mono_mx (by decide +kernel) (restore_ok hp (by rw [g₈ _ (by decide) (by decide), rdi₇])
    (by rw [m₈]; exact i₆.saved.frame f₇ (by rdisj_all))
    (by rw [g₈ _ (by decide) (by decide), cs₇ _ calleeSaved_rsp, i₆.rsp])
    (by rw [rd₈, rd₇, i₆.rd]) (by rw [wr₈, wr₇, i₆.wr])) fun s₉ ⟨cs₉, rax₉, m₉⟩ mx₉ => ?_
  -- The tag computed, and the one received.
  have T₇ := tag₇ _ _ R₆
  have L₃ : bytesAt s₃.mem (off (cx s₀) 592) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := len₃
  have T0₇ : bytesAt s₇.mem (tp s₀) 16 = T0 s₀ := by
    rw [bytesAt_frame f₇ (by rdisj_all) (by lit_omega), bytesAt_frame i₆.frame (by rdisj_all) (by lit_omega)]
  have P₉ : bytesAt s₉.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
    rw [m₉, m₈, bytesAt_frame f₇ (by rdisj_all) hL', pt₆, D₃]
  rw [L₃, D₃, hA] at T₇
  refine ⟨⟨cs₉, by rw [m₉, m₈]; exact ret_kept hp i₆.frame (hp.ret_c.sub_right (sub_ctx _ (by lit_omega))) f₇,
    by rw [mx₉, mx₈, mx₇, mx₆, mx₃, mx₂, mx₁, mx₀]⟩, ?_⟩
  have hm : mac (otk s₀) (macData (A s₀) (D s₀)) = bytesAt s₇.mem (off (cx s₀) 48) 16 := by
    rw [T₇]
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt]
  rw [openX86_64, Contract.post_mk]
  rw [rax₉, rax₈]
  split
  next pt hpt =>
    obtain ⟨hmac, rfl⟩ := decrypt_eq_some hpt
    exact ⟨ite_eq_left (hm.symm.trans (hmac.trans T0₇.symm)), P₉⟩
  next hn => exact ite_eq_right fun he => decrypt_eq_none hn ((hm.trans he).trans T0₇)

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
