module

import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Split.Crypt
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.SealSplit
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Split.Pre
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.LitSplit
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# ChaCha20-Poly1305 with the data's first bytes from `src`, x86-64: correctness

`sealSplitBody` is `seal` but for `cryptSplit`: from a state satisfying
`SPre`, it writes to the data the encryption of `PTs` (the data, but for its
bytes `[mm, src_len)`, from `src`) and its tag (`sealSplitBody_correct`), as
`seal_correct` proves of `seal`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Split

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.SealSplit
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt keystream)
open VG.Spec.ChaCha20Poly1305 (pad16 macData polyKeyGen)

/-- The bytes encrypted survive a frame apart from the data and `src`. -/
theorem PTs_frame {s₀ : State} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (dR s₀).Disjoint r) (hs : ∀ r ∈ rs, (spR s₀).Disjoint r) (hT : SPre s₀) :
    PTs s₀ m' = PTs s₀ m := by
  have hp := hT.hp
  simp only [PTs]
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.mp hk
  split
  · rename_i h
    exact hf _ fun r hr hc => hs r hr _ (Offset.contains_base _ (by omega) (by have := hT.wrap_s; omega)) hc
  · exact hf _ fun r hr hc => hd r hr _ (byte_dR hk') hc

theorem cryptSplit_mx : cryptSplit.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

/-- An implementation for the AVX-512 implementations of `vg_poly1305_blocks`
already has `bigCallee`'s `fold`, `pass` and `wide`. -/
theorem big_fold {v : Proof.ChaCha20.X86_64.XorImpl} (h : v.poly = .avx512 ∨ v.poly = .ifma) :
    v.callee.fold = 960 := by
  rcases v.fold_poly with ⟨_, _, _, hp⟩ | ⟨_, _, _, hp⟩ | ⟨hf, _, _, _⟩
  · rcases h with h | h <;> rw [hp] at h <;> cases h
  · rcases h with h | h <;> rw [hp] at h <;> cases h
  · exact hf

theorem bigCallee_eq {v : Proof.ChaCha20.X86_64.XorImpl} (h : v.poly = .avx512 ∨ v.poly = .ifma) :
    bigCallee v.callee = v.callee := by
  rcases v.fold_poly with ⟨_, _, _, hp⟩ | ⟨_, _, _, hp⟩ | ⟨hf, hpa, hw, _⟩
  · rcases h with h | h <;> rw [hp] at h <;> cases h
  · rcases h with h | h <;> rw [hp] at h <;> cases h
  · unfold bigCallee; rw [← hf, ← hpa, ← hw]

theorem sealSplitBody_correct (v : Proof.ChaCha20.X86_64.XorImpl) (b : Impl.Poly1305.X86_64.Blocks)
    (hvb : v.poly = b) (hb : b = .avx512 ∨ b = .ifma) {s₀ : State}
    (hT : SPre s₀) :
    WP isa (sealSplitBody v.callee b) s₀ fun s' => abiPreserved s₀ s' ∧
      Spec.ChaCha20Poly1305.encrypt (K s₀) (N s₀) (A s₀) (PTs s₀ s₀.mem) =
        (bytesAt s'.mem (dp s₀) (L s₀), bytesAt s'.mem (tp s₀) 16) := by
  have hp := hT.hp
  have hL' := (Nat.le_of_lt (s₀.gpr .r9).isLt)
  have hcal : bigCallee v.callee = v.callee := bigCallee_eq (hvb ▸ hb)
  have hA2 : ∀ {rs : List Region} {m m' : Mem}, Frame rs m m' → (∀ r ∈ rs, (arg2R s₀).Disjoint r) →
      ∀ j, j = 2 ∨ j = 3 → m'.readW (stackArgAddr s₀ j) 64 = m.readW (stackArgAddr s₀ j) 64 :=
    fun hf hd _ hj => arg_frame hj hf hd
  refine WP.seq (WP.mono_mx (by decide +kernel) (entry_ok hp) fun s₀' e₀ mx₀ => ?_)
  subst e₀
  refine WP.seq (WP.mono_mx (hcal ▸ prologue_mx v) (hcal ▸ prologue_ok v hp) fun s₁ h₁ mx₁ => ?_)
  have hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.fine (by rdisj_all) (Nat.le_of_lt (s₀.gpr .rcx).isLt)
  refine WP.seq (WP.mono (macPad_ok b hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩ (srcA hp)
    h₁.inv.r15 h₁.inv.rsp h₁.inv.rd h₁.inv.wr h₁.rbx (by rw [h₁.rbp]; exact hRDX s₀))
    fun s₂ ⟨cs₂, rd₂, wr₂, f₂, mx₂, r₂⟩ => ?_)
  have i₂ := mac_inv hp h₁.inv cs₂ rd₂ wr₂ f₂
  refine WP.seq (WP.mono_mx (by decide +kernel) (lengths_ok hp i₂ (by rw [cs₂ _ (by simp [calleeSaved]), h₁.rbp]))
    fun s₃ ⟨i₃, _, f₃, len₃⟩ mx₃ => ?_)
  have st₃ : stateAt s₃.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame f₃ (by rdisj_all), stateAt_frame f₂ (by rdisj_all), h₁.st]
  have hM := Nat.le_trans (mOf_le 960 1024 (L s₀)) (le_refl 960)
  have ks₃ := ks_frame f₃ (by rdisj_all) hM (ks_frame f₂ (by rdisj_all) hM h₁.ks)
  -- The stack arguments and `src`, as on entry.
  have g₀ : ∀ r ∈ [workR s₀, dR s₀, stkR s₀], (arg2R s₀).Disjoint r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hT.g_c.sub_right (fun _ h => sub_ctx s₀ (by lit_omega) _ h), hT.g_d, hT.g_k⟩
  have S₃ : ∀ j, j = 2 ∨ j = 3 → s₃.mem.readW (stackArgAddr s₀ j) 64 = stackArg s₀ j :=
    fun j hj => (hA2 i₃.frame g₀ j hj).trans rfl
  have sm : ∀ r ∈ macR s₀, (spR s₀).Disjoint r := by
    simp only [macR, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hT.s_c.sub_right (sub_ctx s₀ (by lit_omega)), hT.s_k⟩
  have P₃ : PTs s₀ s₃.mem = PTs s₀ s₀.mem := by
    rw [PTs_frame f₃ (by rdisj_all) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hT.s_c.sub_right (sub_ctx s₀ (by lit_omega))) hT,
      PTs_frame f₂ (by rdisj_all) sm hT,
      PTs_frame h₁.fine (by rdisj_all) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hT.s_c.sub_right (fun _ h => sub_ctx s₀ (by lit_omega) _ h)
        · exact hT.s_k) hT]
  refine WP.seq (WP.mono_mx cryptSplit_mx (cryptSplit_ok hT i₃ st₃ ks₃ (S₃ 2 (.inl rfl))
    (S₃ 3 (.inr rfl))) fun s₄ ⟨i₄, _, f₄, ct₄⟩ mx₄ => ?_)
  rw [P₃] at ct₄
  refine WP.seq (WP.mono (macPadLengths_ok b hp (p := .r14) (n := .r13) ⟨.inr rfl, .inr rfl⟩ (srcD hp) i₄
    i₄.r14 (by rw [i₄.r13]; exact hL s₀))
    fun s₆ ⟨i₆, _, f₆, mx₆, r₆⟩ => ?_)
  refine WP.seq (WP.mono_mx (by decide +kernel) (finalizeTag_ok hp i₆)
    fun s₇ ⟨cs₇, rd₇, wr₇, rdi₇, f₇, tag₇⟩ mx₇ => ?_)
  refine WP.mono_mx (by decide +kernel) (restore_ok hp rdi₇ (i₆.saved.frame f₇ (by rdisj_all))
    (by rw [cs₇ _ calleeSaved_rsp, i₆.rsp])
    (by rw [rd₇, i₆.rd]) (by rw [wr₇, i₆.wr])) fun s₈ ⟨cs₈, _, m₈⟩ mx₈ => ?_
  have R₄ := Repr.frame f₄ (by rdisj_all) (Repr.frame f₃ (by rdisj_all) (r₂ (otk s₀) [] h₁.poly))
  have T₇ := tag₇ _ _ (r₆ _ _ R₄)
  have L₄ : bytesAt s₄.mem (off (cx s₀) 592) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame f₄ (by rdisj_all) (by lit_omega), len₃]
  have C₈ : bytesAt s₈.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (PTs s₀ s₀.mem) := by
    rw [m₈, bytesAt_frame f₇ (by rdisj_all) hL', bytesAt_frame f₆ (by rdisj_all) hL', ct₄]
  refine ⟨⟨cs₈, by rw [m₈]; exact ret_kept hp i₆.frame hp.ret_t f₇,
    by rw [mx₈, mx₇, mx₆, mx₄, mx₃, mx₂, mx₁, mx₀]⟩, ?_⟩
  rw [C₈, m₈, T₇, L₄, ct₄, hA]
  simp only [Spec.ChaCha20Poly1305.encrypt, macData, List.nil_append,
    List.append_assoc, VG.Proof.Poly1305.length_bytesAt, length_encrypt, length_PTs]

end VG.Proof.ChaCha20Poly1305.X86_64.Split
