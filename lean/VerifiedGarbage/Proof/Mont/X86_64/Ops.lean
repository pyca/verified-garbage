import VerifiedGarbage.Proof.Mont.X86_64.MulP

/-!
# Montgomery arithmetic on x86-64: the operations

For a modulus `m` of any number of words in the working space (`ModOkW`):
`mul o a b` writes `[a] [b] R⁻¹ mod m` to `[o]` (`mul_ok`), `add` writes
`[a] + [b] mod m` (`add_ok`) and `sub` writes `[a] - [b] mod m` (`sub_ok`),
for `[a]`, `[b]` below `m`, and `[o]`, `[a]`, `[b]` apart from the
temporary area. Each changes only the registers `clob n`, the result and the
temporary area (`OpKeep`). With at most six words they are the operations
with the accumulator in registers (`mulR_ok`, …, `OpsReg.lean`); with more,
those with the accumulator in the temporary area (`mulW_ok`, …, here), but
the multiplication for P-521's `p`, by columns (`mulP_ok`, `MulP.lean`).
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- The registers the operations with the accumulator in memory use are
among `clob n`. -/
theorem wide_clob {n : Nat} (hn : 0 < n) : ∀ r ∈ [Reg.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10], r ∈ clob n := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  intro r hr
  simp only [clob, acc, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rw [show n' + 1 + 2 = n' + 3 by omega]
  simp only [List.take_succ_cons, List.mem_cons]
  rcases hr with h | h | h | h | h | h | h <;> simp [h]

theorem in_wide {r : Reg} {l : List Reg} (hl : ∀ q ∈ l, q ∈ [Reg.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10])
    (h : r ∈ l) : r ∈ [Reg.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10] := hl r h

/-! ## The operations with the accumulator in memory -/

/-- `[o] = [a] [b] R⁻¹ mod m`, for any number of words. -/
theorem mulW_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) {o a b : Nat} (ho : o + 8 * M.n ≤ size)
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size)
    (hoT : o + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ o) (haT : a + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ a)
    (hbT : b + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ b) (hoM : o + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ o)
    (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (mulW M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  have hnw := hs.nowrap
  have hn := hM.n0
  have hmo := hM.mo
  have htmp := hM.tmp
  have hsep := hM.sep
  have hmX : m < 2 ^ (64 * M.n) := hM.val ▸ wordsVal_lt _ _ _ _
  have hcl := wide_clob hn
  rw [mulW, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (zeroWords_ok hs htmp) fun s₁ ⟨z₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff, show ([.mov32 .r9 (.imm 0), .mov32 .r10 (.imm 0)] : List Instr) =
    zeros [.r9, .r10] from rfl]
  refine WP.mono (zeros_ok s₁ [.r9, .r10]) fun s₂ ⟨z₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have hm₂ : s₂.mem = s₁.mem := k₂.2.1
  have hmo₂ : wordsVal s₂.mem base M.mo M.n = m := by
    rw [hm₂, O₁.wordsVal hsep (by omega), hM.val]
  have hB₂ : wordsVal s₂.mem base b M.n = wordsVal s.mem base b M.n := by
    rw [hm₂, O₁.wordsVal hbT (by omega)]
  have hA₂ : wordsVal s₂.mem base a M.n = wordsVal s.mem base a M.n := by
    rw [hm₂, O₁.wordsVal haT (by omega)]
  have h0 : accW s₂ base M = 0 := by
    simp only [accW, hm₂, z₁, z₂ .r9 (by simp), z₂ .r10 (by simp)]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (roundsW_ok hn ha hb hmo htmp haT hbT hsep hM.inv M.n (Nat.le_refl _) hs₂ hmo₂
    (by rw [hB₂]; exact hB) h0 (z₂ .r10 (by simp))) fun s₃ ⟨⟨U, eU⟩, hT, h10, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [hA₂, hB₂] at eU
  have hT' : accW s₃ base M = wordsVal s₃.mem base M.tmp M.n + 2 ^ (64 * M.n) * (s₃.gpr .r9).toNat := by
    simp only [accW, h10]; rfl
  have hmo₃ : wordsVal s₃.mem base M.mo M.n = m := by rw [O₃.wordsVal hsep (by omega), hmo₂]
  refine WP.mono (csubW_ok hs₃ hn hmo htmp ho hoT hoM hmo₃ (by rw [← hT']; exact hT))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  rw [← hT'] at e₄
  refine ⟨⟨fun r hr => ?_, ?_, ?_, fun x hx hx' => ?_⟩, ?_, ?_⟩
  · rw [k₄.gpr r (fun h => hr (hcl r (in_wide (by decide) h))),
      k₃.gpr r (fun h => hr (hcl r (in_wide (by decide) h))),
      k₂.1 r (fun h => hr (hcl r (in_wide (by decide) h))),
      k₁.gpr r (fun h => hr (hcl r (in_wide (by decide) h)))]
  · rw [k₄.rd, k₃.rd, k₂.2.2.1, k₁.rd]
  · rw [k₄.wr, k₃.wr, k₂.2.2.2, k₁.wr]
  · rw [O₄ x hx, O₃ x hx', hm₂, O₁ x hx']
  · rw [e₄]; exact Nat.mod_lt _ (m_pos hB)
  · rw [e₄, Nat.mod_mul_mod, Nat.mul_comm, eU]
    simp only [Nat.add_mul_mod_self_right]

/-- `[o] = [a] + [b] mod m`, for any number of words. -/
theorem addW_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) {o a b : Nat} (ho : o + 8 * M.n ≤ size)
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size)
    (hoT : o + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ o) (haT : a + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ a)
    (hbT : b + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ b) (hoM : o + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ o)
    (hAB : wordsVal s.mem base a M.n + wordsVal s.mem base b M.n < 2 * m) :
    WP isa (.block (addW M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + wordsVal s.mem base b M.n) % m := by
  have hnw := hs.nowrap
  have hn := hM.n0
  have htmp := hM.tmp
  have hmo := hM.mo
  have hcl := wide_clob hn
  rw [addW, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (mov32zero_ok s .r9) fun s₁ ⟨z₁, _, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (chainWAdd_ok M.n hs₁ (op := .add) (c := false) (.inl ⟨rfl, rfl⟩) (.inl hn)
    (t := M.tmp) (a := a) (b := b) htmp ha hb (by unfold Near; omega) (by unfold Near; omega))
    fun s₂ ⟨c, c₂, e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (adcZero_ok s₂ .r9 c₂ (by rw [k₂.gpr .r9 (by decide), z₁])) fun s₃ ⟨e₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  rw [hm₁] at e₂
  simp only [Bool.toNat_false, Nat.add_zero] at e₂
  have hV : wordsVal s₃.mem base M.tmp M.n + 2 ^ (64 * M.n) * (s₃.gpr .r9).toNat =
      wordsVal s.mem base a M.n + wordsVal s.mem base b M.n := by rw [k₃.2.1, e₃, e₂]
  have hmo₃ : wordsVal s₃.mem base M.mo M.n = m := by
    rw [k₃.2.1, O₂.wordsVal hM.sep (by omega), hm₁, hM.val]
  refine WP.mono (csubW_ok hs₃ hn hM.mo htmp ho hoT hoM hmo₃ (by rw [hV]; exact hAB))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_, fun x hx hx' => ?_⟩, by rw [e₄, hV]⟩
  · rw [k₄.gpr r (fun h => hr (hcl r (in_wide (by decide) h))),
      k₃.1 r (fun h => hr (hcl r (in_wide (by decide) h))),
      k₂.gpr r (fun h => hr (hcl r (in_wide (by decide) h))),
      k₁.1 r (fun h => hr (hcl r (in_wide (by decide) h)))]
  · rw [k₄.rd, k₃.2.2.1, k₂.rd, k₁.2.2.1]
  · rw [k₄.wr, k₃.2.2.2, k₂.wr, k₁.2.2.2]
  · rw [O₄ x hx, k₃.2.1, O₂ x hx', hm₁]

/-- `[o] = [a] - [b] mod m`, for any number of words. -/
theorem subW_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) {o a b : Nat} (ho : o + 8 * M.n ≤ size)
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size)
    (hoT : o + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ o) (haT : a + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ a)
    (hbT : b + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ b) (hoM : o + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ o)
    (hA : wordsVal s.mem base a M.n < m) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (subW M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + m - wordsVal s.mem base b M.n) % m := by
  have hnw := hs.nowrap
  have hn := hM.n0
  have htmp := hM.tmp
  have hmo := hM.mo
  have hcl := wide_clob hn
  have hmX : m < 2 ^ (64 * M.n) := hM.val ▸ wordsVal_lt _ _ _ _
  rw [subW, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (chainWSub_ok M.n hs (op := .sub) (c := false) (.inl ⟨rfl, rfl⟩) (.inl hn)
    (t := M.tmp) (a := a) (b := b) htmp ha hb (by unfold Near; omega) (by unfold Near; omega))
    fun s₁ ⟨c, c₁, e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sbbMask_ok s₁ c₁) fun s₂ ⟨x₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (masked_ok M.n c hs₂ (mo := M.mo) (tmp := o) hM.mo ho (by omega) x₂)
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  refine WP.mono (chainWAdd_ok M.n hs₃ (op := .add) (c := false) (.inl ⟨rfl, rfl⟩) (.inl hn)
    (t := o) (a := M.tmp) (b := o) ho htmp ho (by unfold Near; omega) (by unfold Near; omega))
    fun s₄ ⟨c', _, e₄, k₄, O₄⟩ => ?_
  have hmo₂ : wordsVal s₂.mem base M.mo M.n = m := by
    rw [k₂.2.1, O₁.wordsVal hM.sep (by omega), hM.val]
  have hD₃ : wordsVal s₃.mem base M.tmp M.n = wordsVal s₁.mem base M.tmp M.n := by
    rw [O₃.wordsVal (by omega) (by omega), k₂.2.1]
  rw [e₃, hD₃, hmo₂] at e₄
  simp only [Bool.toNat_false, Nat.add_zero] at e₁ e₄
  refine ⟨⟨fun r hr => ?_, ?_, ?_, fun x hx hx' => ?_⟩, ?_⟩
  · rw [k₄.gpr r (fun h => hr (hcl r (in_wide (by decide) h))),
      k₃.gpr r (fun h => hr (hcl r (in_wide (by decide) h))),
      k₂.1 r (fun h => hr (hcl r (in_wide (by decide) h))),
      k₁.gpr r (fun h => hr (hcl r (in_wide (by decide) h)))]
  · rw [k₄.rd, k₃.rd, k₂.2.2.1, k₁.rd]
  · rw [k₄.wr, k₃.wr, k₂.2.2.2, k₁.wr]
  · rw [O₄ x hx, O₃ x hx, k₂.2.1, O₁ x hx']
  · have hD := wordsVal_lt s₁.mem base M.tmp M.n
    have hO := wordsVal_lt s₄.mem base o M.n
    cases c <;> cases c' <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero,
      Nat.mul_one, Nat.add_zero, Bool.false_eq_true, ite_false, ite_true] at e₁ e₄
    · rw [show wordsVal s.mem base a M.n + m - wordsVal s.mem base b M.n =
        (wordsVal s.mem base a M.n - wordsVal s.mem base b M.n) + m by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
      omega
    · omega
    · omega
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega

/-! ## The operations -/

/-- Below seven words, the operations are the register ones. -/
theorem mul_of_lt {M : Mod} (h : M.n < 7) (o a b : Nat) : mul M o a b = mulR M o a b := by
  simp only [mul, h, ↓reduceIte]

theorem add_of_lt {M : Mod} (h : M.n < 7) (o a b : Nat) : add M o a b = addR M o a b := by
  simp only [add, h, ↓reduceIte]

theorem sub_of_lt {M : Mod} (h : M.n < 7) (o a b : Nat) : sub M o a b = subR M o a b := by
  simp only [sub, h, ↓reduceIte]

/-- `[o] = [a] [b] R⁻¹ mod m`. -/
theorem mul_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) {o a b : Nat} (ho : o + 8 * M.n ≤ size)
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size)
    (hoT : o + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ o) (haT : a + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ a)
    (hbT : b + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ b) (hoM : o + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ o)
    (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (mul M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  rw [mul]; split
  · exact mulR_ok hs (hM.toModOk ‹_›) ho ha hb hB
  · split
    · exact mulP_ok hs hM ‹_› ho ha hb hoT haT hbT hoM hB
    · exact mulW_ok hs hM ho ha hb hoT haT hbT hoM hB

/-- `[o] = [a] + [b] mod m`. -/
theorem add_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) {o a b : Nat} (ho : o + 8 * M.n ≤ size)
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size)
    (hoT : o + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ o) (haT : a + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ a)
    (hbT : b + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ b) (hoM : o + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ o)
    (hAB : wordsVal s.mem base a M.n + wordsVal s.mem base b M.n < 2 * m) :
    WP isa (.block (add M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + wordsVal s.mem base b M.n) % m := by
  rw [add]; split
  · exact addR_ok hs (hM.toModOk ‹_›) ho ha hb hAB
  · exact addW_ok hs hM ho ha hb hoT haT hbT hoM hAB

/-- `[o] = [a] - [b] mod m`. -/
theorem sub_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) {o a b : Nat} (ho : o + 8 * M.n ≤ size)
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size)
    (hoT : o + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ o) (haT : a + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ a)
    (hbT : b + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ b) (hoM : o + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ o)
    (hA : wordsVal s.mem base a M.n < m) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (sub M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + m - wordsVal s.mem base b M.n) % m := by
  rw [sub]; split
  · exact subR_ok hs (hM.toModOk ‹_›) ho ha hb hA hB
  · exact subW_ok hs hM ho ha hb hoT haT hbT hoM hA hB

end VG.Proof.Mont.X86_64
