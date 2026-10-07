import VerifiedGarbage.Proof.P256.VerifySparse.Correct

/-! The existing Montgomery setup/round and addition-chain proofs are reused here.
Only their final conditional subtraction is replaced with the sparse P-256 proof. -/
namespace VG.Proof.P256.VerifySparse
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)

def sparseMul (M : Mod) (o a b : Nat) : List Instr :=
  mulSetup M b ++ ((List.range M.n).flatMap (round M a b) ++
    (Impl.P256.VerifySparse.correct ((List.range M.n).map (win M.n M.n)) (win M.n M.n M.n) ++
      stores ((List.range M.n).map (win M.n M.n)) o))

def sparseAdd (M : Mod) (o a b : Nat) : List Instr :=
  zero7 :: loads (low M.n) a ++ chain (.adds .x) (.adcs .x) (low M.n) b ++
    [.adc .x (top M.n) .x7 .x7] ++ Impl.P256.VerifySparse.correct (low M.n) (top M.n) ++ stores (low M.n) o

theorem mul_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} (hME : M=Impl.P256.VerifySparse.M)
    (hM : ModOkW M size p s.mem base) (h10 : M.n < 10) (hA : ModA M) {o a b : Nat} (ho : o + 8 * M.n ≤ size)
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hb8 : b % 8 = 0) (hB : wordsVal s.mem base b M.n < p) :
    WP isa (.block (sparseMul M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < p ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % p =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % p := by
  have h7 := h10
  rw [sparseMul, WP.block_append_iff]
  refine WP.mono (setup_ok hs h7 hb hb8) fun s₁ ⟨z₁, hBR₁, h6₁, h0, k₁⟩ => ?_
  have hacc := acc_regs_lt _ h7
  have hs₁ := hs.of_keeps k₁ (fun h => by
    simp only [List.mem_cons] at h
    rcases h with h | h | h | h | h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact (hacc _ h) (by simp))
  have hmem₁ : s₁.mem = s.mem := k₁.mem
  rw [WP.block_append_iff]
  refine WP.mono (rounds_ok h7 ha hb hM.mo ha8 hb8 hA.mo hM.inv hM.red M.n (Nat.le_refl _) hs₁ z₁
    (by rw [hmem₁]; exact hM.val) hBR₁ h6₁ (by rw [hmem₁]; exact hB) h0)
    fun s₂ ⟨⟨U, eU⟩, hT, k₂, _⟩ => ?_
  have nk : ∀ r ∈ [Reg.x0, .x7], r ∉ Reg.x1 :: Reg.x2 :: Reg.x3 :: acc M.n := by
    intro r hr h
    by_cases hr' : r ∈ acc M.n
    · have := hacc _ hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr h
    rcases hr with rfl | rfl <;> simp_all
  have hs₂ := hs₁.of_keeps k₂ (nk .x0 (by simp))
  have hz₂ : s₂.gpr .x7 = 0 := by rw [k₂.gpr .x7 (nk .x7 (by simp)), z₁]
  have hmem₂ : s₂.mem = s.mem := by rw [k₂.mem, hmem₁]
  rw [hmem₁] at eU
  -- The accumulator's value as `csub` sees it: its top word is zero.
  have hsplit := wins_split M.n M.n
  have hmX : p < 2 ^ (64 * M.n) := hM.val ▸ wordsVal_lt _ _ _ _
  have hlowlen : ((List.range M.n).map (win M.n M.n)).length = M.n := by simp
  have hV : regsVal s₂ ((List.range M.n).map (win M.n M.n)) +
      2 ^ (64 * M.n) * (s₂.gpr (win M.n M.n M.n)).toNat = regsVal s₂ (wins M.n M.n) := by
    rw [hsplit, regsVal_append, hlowlen]
    simp only [regsVal, Nat.mul_zero, Nat.add_zero]
    have hT' := hT
    rw [hsplit, regsVal_append, hlowlen] at hT'
    simp only [regsVal, Nat.mul_zero, Nat.add_zero] at hT'
    have : (s₂.gpr (win M.n M.n (M.n + 1))).toNat = 0 := by
      by_contra hne
      have : 2 ^ (64 * M.n) * 2 ^ 64 ≤ 2 ^ (64 * M.n) * ((s₂.gpr (win M.n M.n M.n)).toNat +
          2 ^ 64 * (s₂.gpr (win M.n M.n (M.n + 1))).toNat) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    rw [this, Nat.mul_zero, Nat.add_zero]
  rw [WP.block_append_iff]
  have hlow_acc : ∀ r ∈ (List.range M.n).map (win M.n M.n), r ∈ acc M.n := fun r hr =>
    wins_sub_acc h7 M.n r (by rw [hsplit]; exact List.mem_append_left _ hr)
  refine WP.mono (correctP_ok hs₂ (M := M) hME hlowlen hM.n0 h7 (fresh_low M.n h7) hM.mo
    hA.mo hz₂ (by rw [hmem₂]; exact hM.val) (by rw [hV]; exact hT)) fun s₃ ⟨e₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (fun h => x0_not_clob M.n (csubR_keep h7 hlow_acc _ h))
  refine WP.mono (stores_ok _ hs₃ (o := o) (by rw [hlowlen]; omega) ho8 (fresh_low' M.n h7).1)
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  rw [hlowlen] at e₄ O₄
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_, fun x hx hx' => ?_⟩, ?_, ?_⟩
  · obtain ⟨hr₁, hr₂⟩ := not_mem_of_clob hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr₁
    rw [k₄.gpr r (by simp), k₃.gpr r (fun h => hr (csubR_keep h7 hlow_acc r h)),
      k₂.gpr r (by simp only [List.mem_cons, not_or]; exact ⟨hr₁.1, hr₁.2.1, hr₁.2.2.1, hr₂⟩),
      k₁.gpr r (by simp only [List.mem_cons, not_or]; exact ⟨hr₁.2.2.2.1, hr₁.2.2.2.2.1,
        hr₁.2.2.2.2.2.1, hr₁.2.2.2.2.2.2.1, hr₁.2.2.2.2.2.2.2.1, hr₁.2.2.2.2.2.2.2.2, hr₂⟩)]
  · rw [k₄.rd, k₃.rd, k₂.rd, k₁.rd]
  · rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr]
  · rw [k₄.sp, k₃.sp, k₂.sp, k₁.sp]
  · rw [O₄ x hx, k₃.mem, hmem₂]
  · rw [e₄, e₃, hV]; exact Nat.mod_lt _ (m_pos hB)
  · rw [e₄, e₃, hV, Nat.mod_mul_mod, Nat.mul_comm, eU]
    simp only [Nat.add_mul_mod_self_right]

theorem add_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} (hME : M=Impl.P256.VerifySparse.M)
    (hM : ModOkW M size p s.mem base) (h10 : M.n < 10) (hA : ModA M) {o a b : Nat} (ho : o + 8 * M.n ≤ size)
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hb8 : b % 8 = 0)
    (hAB : wordsVal s.mem base a M.n + wordsVal s.mem base b M.n < 2 * p) :
    WP isa (.block (sparseAdd M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + wordsVal s.mem base b M.n) % p := by
  have hn := hs.nowrap
  have h7 := h10
  have hf := fresh_top_low_lt M.n h7
  have hl := low_len_lt M.n h7
  obtain ⟨t, ts, hts⟩ := low_ne_nil h7 hM.n0
  have nf : ∀ r ∈ top M.n :: low M.n, r ∉ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17, .x24, .x25] :=
    hf.2
  have hsub : ∀ r ∈ top M.n :: low M.n, r ∈ acc M.n := low_sub_acc_lt _ h7
  rw [sparseAdd, show zero7 :: loads (low M.n) a = [zero7] ++ loads (low M.n) a from rfl]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero7_ok s) fun s₀ ⟨z₀, k₀⟩ => ?_
  have hs₀ := hs.of_keeps k₀ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok (low M.n) hs₀ (a := a) (by omega) ha8 hf.tail) fun s₁ ⟨e₁, k₁, _⟩ => ?_
  have hs₁ := hs₀.of_keeps k₁ (fun h => nf _ (List.mem_cons_of_mem _ h) (by simp))
  have hz₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr _ (fun h => nf _ (List.mem_cons_of_mem _ h) (by simp)), z₀]
  rw [WP.block_append_iff, hts]
  refine WP.mono (chainAdds_ok hs₁ (b := b) (by rw [← hts]; omega) hb8 (hts ▸ hf.tail))
    fun s₃ ⟨e₃, k₃⟩ => ?_
  rw [← hts] at e₃ k₃ ⊢
  have nk₃ : ∀ r ∈ [Reg.x0, .x7], r ∉ Reg.x2 :: low M.n := by
    intro r hr h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases List.mem_cons.mp h with h | h
    · rcases hr with rfl | rfl <;> exact absurd h (by decide)
    · exact nf _ (List.mem_cons_of_mem _ h) (by rcases hr with rfl | rfl <;> simp)
  have hs₃ := hs₁.of_keeps k₃ (nk₃ .x0 (by simp))
  have hz₃ : s₃.gpr .x7 = 0 := by rw [k₃.gpr _ (nk₃ .x7 (by simp)), hz₁]
  rw [WP.block_append_iff]
  refine WP.mono (adcZero_ok s₃ (top M.n) hz₃) fun s₄ ⟨e₄, k₄⟩ => ?_
  have htop := nf _ (List.mem_cons_self ..)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at htop
  have hs₄ := hs₃.of_keeps k₄ (by simp [Ne.symm htop.1])
  have hz₄ : s₄.gpr .x7 = 0 := by rw [k₄.gpr _ (by simp [Ne.symm htop.2.2.2.2.2.2.2.1]), hz₃]
  have hR₄ : regsVal s₄ (low M.n) = regsVal s₃ (low M.n) :=
    regsVal_congr fun q hq => k₄.gpr q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => (List.nodup_cons.mp hf.1).1 (h ▸ hq))
  have hmem₄ : s₄.mem = s.mem := by rw [k₄.mem, k₃.mem, k₁.mem, k₀.mem]
  rw [hl, e₁, k₀.mem] at e₃
  have hV : regsVal s₄ (low M.n) + 2 ^ (64 * M.n) * (s₄.gpr (top M.n)).toNat =
      wordsVal s.mem base a M.n + wordsVal s.mem base b M.n := by rw [hR₄, e₄, e₃, k₁.mem, k₀.mem, hl]
  rw [WP.block_append_iff]
  have hlow : ∀ r ∈ low M.n, r ∈ acc M.n := fun r h => hsub r (List.mem_cons_of_mem _ h)
  refine WP.mono (correctP_ok hs₄ (M := M) hME hl hM.n0 h7 hf hM.mo hA.mo hz₄
    (by rw [hmem₄]; exact hM.val) (by rw [hV]; exact hAB)) fun s₅ ⟨e₅, k₅⟩ => ?_
  have hs₅ := hs₄.of_keeps k₅ (fun h => x0_not_clob M.n (csubR_keep h7 hlow _ h))
  refine WP.mono (stores_ok _ hs₅ (o := o) (by rw [hl]; omega) ho8 hf.tail.1) fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  rw [hl] at e₆ O₆
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_, fun x hx hx' => ?_⟩, ?_⟩
  · obtain ⟨hr₁, hr₂⟩ := not_mem_of_clob hr
    have hr' : r ∉ top M.n :: low M.n := fun h => hr₂ (hsub r h)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr₁ hr'
    rw [k₆.gpr r (by simp), k₅.gpr r (fun h => hr (csubR_keep h7 hlow r h)),
      k₄.gpr r (by simpa using hr'.1),
      k₃.gpr r (by simp only [List.mem_cons, not_or]; exact ⟨hr₁.2.1, hr'.2⟩),
      k₁.gpr r hr'.2, k₀.gpr r (by simpa using hr₁.2.2.2.2.2.2.1)]
  · rw [k₆.rd, k₅.rd, k₄.rd, k₃.rd, k₁.rd, k₀.rd]
  · rw [k₆.wr, k₅.wr, k₄.wr, k₃.wr, k₁.wr, k₀.wr]
  · rw [k₆.sp, k₅.sp, k₄.sp, k₃.sp, k₁.sp, k₀.sp]
  · rw [O₆ x hx, k₅.mem, hmem₄]
  · rw [e₆, e₅, hV]


end VG.Proof.P256.VerifySparse
