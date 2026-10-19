module

public import VerifiedGarbage.Proof.Mont.X86.MulAtRow
public import VerifiedGarbage.Proof.Mont.X86.DynamicOps
public import VerifiedGarbage.Proof.Mont.X86.WindowCopy
import VerifiedGarbage.Proof.Framework.Omega

/-! # The callable multiplication's arithmetic

`mulAt_ok`: `mulAt` leaves in the low words of the accumulator the
Montgomery product of the number at the argument `a` and the number at `b`,
as `mul_ok` writes it to `o`. `copyIn_ok` copies a number from `esi` into the
working space, as `copyOut_ok` copies one out.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Dynamic

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Mont VG.Proof.Mont
open VG.Proof.Mont.X86

/-- The `k` words at `esi` (at `src`) to the `k` words at `dst`. -/
theorem copyIn_ok {s : State} {base : Addr} {size k src dst : Nat} (hs : Scr s base size)
    (hk : 0 < k) (hsrc : src + 4 * k ≤ size) (hdst : dst + 4 * k ≤ size)
    (apart : dst + 4 * k ≤ src ∨ src + 4 * k ≤ dst)
    (he : s.gpr .esi = s.gpr .edi + BitVec.ofNat 32 src) :
    WP isa (copyIn k dst) s fun t =>
      val32 t.mem base dst k = val32 s.mem base src k ∧
      Outside base dst (4 * k) s.mem t.mem ∧
      t.gpr .esi = t.gpr .edi + BitVec.ofNat 32 (src + 4 * k) ∧
      Keeps [.eax, .edx, .ebp, .esi] s t := by
  have hn := hs.nowrap
  unfold copyIn
  refine wordLoop_ok (fun j t => Keeps [.eax, .edx, .ebp, .esi] s t ∧
      Outside base dst (4 * j) s.mem t.mem ∧ val32 t.mem base dst j = val32 s.mem base src j ∧
      t.gpr .esi = t.gpr .edi + BitVec.ofNat 32 (src + 4 * j)) hk
    (by have := hs.size_lt; omega)
    (fun j u u' ⟨K, O, V, E⟩ ⟨hm, hr, hw, hg⟩ =>
      ⟨⟨fun r h => (hg r (by simp_all) (by simp_all)).trans (K.1 r h), hr.trans K.2.1, hw.trans K.2.2⟩,
        hm ▸ O, hm ▸ V, by rw [hg _ (by decide) (by decide), hg _ (by decide) (by decide)]; exact E⟩)
    ⟨Keeps.refl _ _, VG.Proof.Mont.Outside.refl _ _ _ _, rfl, by simpa only [Nat.mul_zero, Nat.add_zero] using he⟩
    (fun j hj t ⟨K, O, V, E⟩ ej => ?_) (fun u ⟨K, O, V, E⟩ => ⟨V, O, E, K⟩)
  have ht := hs.of_keeps K (by decide)
  refine wp_movS (readSrc_ptr ht E (by omega)) fun s₁ u₁ _ => ?_
  have hs₁ := ht.of_keeps u₁.keeps (by decide)
  have ej₁ : s₁.gpr .ebp = s₁.gpr .edi + BitVec.ofNat 32 (4 * j) := by
    rw [u₁.other _ (by decide), u₁.other _ (by decide)]; exact ej
  refine wp_storeS (hs₁.ea_at' ej₁ (d := dst) (by omega)) (hs₁.write (d := dst + 4 * j) (n := 4) (by omega))
    fun s₂ m₂ => ?_
  refine wp_addS rfl fun u u₃ _ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact (K.trans (u₁.keeps.mono (by decide))).trans ((m₂.keeps _).trans (u₃.keeps.mono (by decide)))
  · rw [u₃.mem, m₂.mem, u₁.mem]
    exact (O.mono (Nat.le_refl _) (by omega)).trans
      ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))
  · rw [u₃.mem, m₂.mem, u₁.mem, val32_store hn (by omega), V, u₁.gpr, val32_succ]
    exact congrArg (val32 s.mem base src j + 2 ^ (32 * j) * ·)
      (O.w32 (d := src + 4 * j) (by omega) (by omega))
  · rw [u₃.gpr, u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), E, esi_step]
    congr 2
  · rw [u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide)]
  · rw [u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide)]

/-- The accumulator's low words are the Montgomery product of the number at
the argument `a` and the number at `b`. -/
theorem mulAt_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : Modulus M size m s.mem base) {inv acc a b : Nat}
    (hv : inv + 4 ≤ size) (hsepInv : inv + 4 ≤ acc ∨ acc + accLen M ≤ inv)
    (hinv : (m * w32 s.mem base inv + 1) % 2 ^ 32 = 0)
    (hacc : acc + accLen M ≤ size) (haL : a + 8 * M.n ≤ size) (hbL : b + 8 * M.n ≤ size)
    (l₁ : acc + accLen M ≤ a ∨ a + 8 * M.n ≤ acc) (l₂ : acc + accLen M ≤ b ∨ b + 8 * M.n ≤ acc)
    (l₃ : acc + accLen M ≤ M.mo ∨ M.mo + 8 * M.n ≤ acc) (l₄ : acc + accLen M ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ acc)
    (hB : wordsVal s.mem base b M.n < m)
    (hta : a + 8 * M.n ≤ M.tmp ∨ M.tmp + 4 ≤ a) (htb : b + 8 * M.n ≤ M.tmp ∨ M.tmp + 4 ≤ b)
    (hti : inv + 4 ≤ M.tmp ∨ M.tmp + 4 ≤ inv)
    (hA : readSrc s (.mem argA) = some (BitVec.ofNat 32 a)) (hf : ArgFar s base size argA) :
    WP isa (mulAt M inv acc b) s fun s' =>
      Keeps clob s s' ∧ Outs base [(M.tmp, 8 * M.n), (acc, accLen M)] s.mem s'.mem ∧
      wordsVal s'.mem base acc M.n < m ∧
      wordsVal s'.mem base acc M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  have hn := hs.nowrap
  obtain ⟨N, hNw⟩ : ∃ N, words M = N := ⟨_, rfl⟩
  have hN2 : N = 2 * M.n := hNw ▸ rfl
  have hacc' : accLen M = 4 * (2 * N + 1) := by rw [accLen, hNw]
  have moL := hM.mo; have tL := hM.tmp; have n0 := hM.n0; have mt := hM.sep
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun hz => by
    simp only [hz, Nat.zero_mul, Nat.zero_add] at hinv
    contradiction
  simp only [mulAt, hNw]
  have hmv : val32 s.mem base M.mo N = m := by
    rw [hN2, ← wordsVal_eq_val32]; exact hM.val
  have hBv : val32 s.mem base b N < m := by
    rw [hN2, ← wordsVal_eq_val32]; exact hB
  have hML : MulLay N size acc a b M.mo := ⟨by omega_using [hacc, hacc'], by omega_using [haL, hN2],
    by omega_using [hbL, hN2], by omega_using [moL, hN2], by omega_using [l₁, hN2, hacc'],
    by omega_using [l₂, hN2, hacc'], by omega_using [l₃, hN2, hacc']⟩
  have hX : MultLay N size acc a b M.mo inv M.tmp := ⟨by omega_using [tL, n0], by omega_using [l₄, hacc', n0],
    by omega_using [hta, hN2], by omega_using [htb, hN2], by omega_using [mt, hN2, n0], hti⟩
  have hsi : inv + 4 ≤ acc ∨ acc + 4 * (2 * N + 1) ≤ inv := hacc' ▸ hsepInv
  refine WP.seq (WP.mono (zerosW_ok hs (k := 2 * N + 1) (by omega_using []) (by omega_using [hacc, hacc']))
    fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
  refine WP.seq (wp_movS rfl fun s₂ u₂ _ => WP.block_nil ?_)
  have k₂ : Keeps clobW s s₂ := (K₁.mono (by decide)).widen u₂.keeps
  have hs₂ := hs.of_keeps k₂ (by decide)
  have mem₂ : s₂.mem = s₁.mem := u₂.mem
  have O₂ : Outside base acc (4 * (2 * N + 1)) s.mem s₂.mem := mem₂ ▸ O₁
  have hm₂ : val32 s₂.mem base M.mo N = m := by
    rw [O₂.val32 (by omega_using [l₃, hN2, hacc']) (by omega_using [moL, hN2, hn]), hmv]
  have hB₂ : val32 s₂.mem base b N < m := by
    rw [O₂.val32 (by omega_using [l₂, hN2, hacc']) (by omega_using [hbL, hN2, hn])]; exact hBv
  have I₀ : LoopInvW base N acc a b m M.tmp 0 s₂ s₂ := by
    refine ⟨?_, Outs.refl _ _ _, Keeps.refl _ _, ?_, ⟨0, ?_⟩⟩
    · rw [u₂.gpr, u₂.other _ (by decide), K₁.1 _ (by decide), Nat.mul_zero]; exact (BitVec.add_zero _).symm
    · rw [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, mem₂, V₁]; omega_using [hB₂]
    · rw [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, mem₂, V₁]; simp [val32]
  have hinv₂ : (m * w32 s₂.mem base inv + 1) % 2 ^ 32 = 0 := by
    rw [O₂.w32 hsi (by omega_using [hv, hn])]; exact hinv
  have hrs : ∀ r ∈ [(acc, 4 * (2 * N + 1))], r.1 + r.2 ≤ size := by
    intro r hr; rw [List.mem_singleton.mp hr]; dsimp only; omega_using [hacc, hacc']
  have hA₂ : readSrc s₂ (.mem argA) = some (BitVec.ofNat 32 a) := by
    rw [readSrc_keep hf (Outs.of_outside O₂ (List.mem_singleton_self _)) hrs (k₂.1 _ (by decide)) k₂.2.1 k₂.2.2]
    exact hA
  have hf₂ : ArgFar s₂ base size argA := hf.keep (k₂.1 _ (by decide))
  refine WP.seq (WP.mono (loopAt_ok hs₂ hML hX hv hsi (by omega_using [hN2, n0]) hm₂ hinv₂ hB₂ hA₂ hf₂ I₀)
    fun t I => ?_)
  have ht := hs₂.of_keeps I.keeps (by decide)
  have hmt : val32 t.mem base M.mo N = m := by
    rw [outs2_val32 I.out (by omega_using [l₃, hN2, hacc']) (by omega_using [mt, hN2, n0])
      (by omega_using [moL, hN2, hn]), hm₂]
  have hlt := I.lt
  rw [show 2 * N + 1 - N = N + 1 by omega_using []] at hlt
  refine WP.mono (csubW_ok ht hNw (src := acc + 4 * N) (o := acc) (by omega_using [hN2, n0])
      (by omega_using [hacc, hacc']) (by omega_using [hacc, hacc', hN2]) (by omega_using [tL, hN2])
      (by omega_using [moL, hN2]) (by omega_using [l₄, hacc', hN2]) (by omega_using [mt, hN2])
      (.inl (by omega_using [])) (by omega_using [l₄, hacc', hN2]) hmt hlt) fun u ⟨O, V, K⟩ => ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨fun r hr => ?_, by rw [K.2.1, I.keeps.2.1, k₂.2.1], by rw [K.2.2, I.keeps.2.2, k₂.2.2]⟩
    rw [K.1 r (fun h => hr (by simp_all [clob])), I.keeps.1 r (by simp_all [clobW, clob]),
      k₂.1 r (by simp_all [clobW, clob])]
  · have O₂' : Outs base [(M.tmp, 8 * M.n), (acc, accLen M)] s.mem s₂.mem :=
      Outs.of_outside (hacc' ▸ O₂) (by simp)
    have It : Outs base [(M.tmp, 8 * M.n), (acc, accLen M)] s₂.mem t.mem := fun x hx =>
      I.out x (by
        have h₁ := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        have h₂ := hx _ (List.mem_cons_self ..)
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · simp only at h₁ ⊢; omega_using [h₁, hacc']
        · simp only at h₂ ⊢; omega_using [h₂, n0])
    refine (O₂'.trans It).trans ?_
    intro x hx
    apply O x
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have h₁ := hx _ (List.mem_cons_self ..)
    have h₂ := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    rcases hr with rfl | rfl
    · simp only at h₁ ⊢; omega_using [h₁, hN2]
    · simp only at h₂ ⊢; omega_using [h₂, hN2, hacc']
  · rw [wordsVal_eq_val32, ← hN2, V]; exact Nat.mod_lt _ hm0
  · obtain ⟨U, hU⟩ := I.cong
    rw [show 2 * N + 1 - N = N + 1 by omega_using []] at hU
    rw [wordsVal_eq_val32, wordsVal_eq_val32, wordsVal_eq_val32, ← hN2, V,
      show 64 * M.n = 32 * N by omega_using [hN2],
      ← O₂.val32 (d := a) (by omega_using [l₁, hN2, hacc']) (by omega_using [haL, hN2, hn]),
      ← O₂.val32 (d := b) (by omega_using [l₂, hN2, hacc']) (by omega_using [hbL, hN2, hn]), Nat.mod_mul_mod,
      Nat.mul_comm, hU, Nat.add_mul_mod_self_right]

end VG.Proof.Mont.X86.Dynamic
