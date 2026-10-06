import VerifiedGarbage.Proof.Mont.X86.Step

/-!
# Montgomery arithmetic on x86 (32-bit): a row

`mulRow acc b N` adds `ecx · [b]` (`N` words) to the window of the
accumulator at `[ebp + acc]`, `w` bytes into the working space (`ebp` is
`edi + 4i`, `w = 4i + acc`): the steps (`steps_ok`) add it to the window's
low `N` words, leaving the carry word in `ebx`, which `carryUp` adds to
words `N` and `N + 1` (`carryUp_ok`); the sum must fit the `N + 2` words
(`mulRow_ok`). Only the window's bytes change.
-/

namespace VG.Proof.Mont.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont

/-- The first `k` steps of a row. -/
def steps (acc b k : Nat) : List Instr := (List.range k).flatMap (mulStep acc b)

theorem steps_succ (acc b k : Nat) : steps acc b (k + 1) = steps acc b k ++ mulStep acc b k := by
  simp only [steps, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

/-- The window's low `k` words `+= ecx · [b] + ebx`, the carry word to `ebx`. -/
theorem steps_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {acc b i w : Nat}
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i)) (hw : 4 * i + acc = w) :
    ∀ {k : Nat}, b + 4 * k ≤ size → w + 4 * k ≤ size → (b + 4 * k ≤ w ∨ w + 4 * k ≤ b) →
    WP isa (.block (steps acc b k)) s fun u =>
      Outside base w (4 * k) s.mem u.mem ∧
      val32 u.mem base w k + 2 ^ (32 * k) * (u.gpr .ebx).toNat =
        val32 s.mem base w k + (s.gpr .ecx).toNat * val32 s.mem base b k + (s.gpr .ebx).toNat ∧
      Keeps [.eax, .ebx, .edx] s u
  | 0, _, _, _ => WP.block_nil ⟨VG.Proof.Mont.Outside.refl _ _ _ _, by simp only [val32, Nat.mul_zero, Nat.pow_zero,
      Nat.one_mul, Nat.zero_add], Keeps.refl ..⟩
  | k + 1, hb, hwk, hsep => by
    have hn := hs.nowrap
    rw [steps_succ]
    refine WP.block_append (WP.mono (steps_ok hs hp hw (k := k) (by omega) (by omega) (by omega))
      fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    have hs₁ := hs.of_keeps K₁ (by decide)
    have hp₁ : s₁.gpr .ebp = s₁.gpr .edi + BitVec.ofNat 32 (4 * i) := by
      rw [K₁.1 _ (by decide), K₁.1 _ (by decide)]; exact hp
    refine WP.mono (mulStep_ok hs₁ hp₁ (j := k) (by omega) (by omega)) fun u ⟨m₂, b₂, K₂⟩ => ?_
    have e : 4 * i + (acc + 4 * k) = w + 4 * k := by omega
    rw [e] at m₂ b₂
    have ecx₁ : s₁.gpr .ecx = s.gpr .ecx := K₁.1 _ (by decide)
    have bk : w32 s₁.mem base (b + 4 * k) = w32 s.mem base (b + 4 * k) := O₁.w32 (by omega) (by omega)
    have tk : w32 s₁.mem base (w + 4 * k) = w32 s.mem base (w + 4 * k) := O₁.w32 (by omega) (by omega)
    rw [ecx₁, bk, tk] at m₂ b₂
    have W := writeW32_outside s₁.mem base (d := w + 4 * k)
      (BitVec.ofNat 32 ((s.gpr .ecx).toNat * w32 s.mem base (b + 4 * k) + (s₁.gpr .ebx).toNat +
        w32 s.mem base (w + 4 * k))) (by omega)
    rw [← m₂] at W
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (W.mono (by omega) (by omega)), ?_, K₁.trans K₂⟩
    have hlow : val32 u.mem base w k = val32 s₁.mem base w k := W.val32 (by omega) (by omega)
    have htop : w32 u.mem base (w + 4 * k) = ((s.gpr .ecx).toNat * w32 s.mem base (b + 4 * k) +
        (s₁.gpr .ebx).toNat + w32 s.mem base (w + 4 * k)) % 2 ^ 32 := by
      rw [m₂, w32_write_self, BitVec.toNat_ofNat]
    rw [val32_succ, val32_succ, val32_succ, hlow, htop, b₂, pow32_succ]
    generalize hxd : (s.gpr .ecx).toNat * w32 s.mem base (b + 4 * k) + (s₁.gpr .ebx).toNat +
      w32 s.mem base (w + 4 * k) = x at *
    have hx := Nat.div_add_mod x (2 ^ 32)
    generalize 2 ^ (32 * k) = P at *
    grind

/-- The carry word `ebx` added to the window's words `N` and `N + 1`, when
the sum fits them. -/
theorem carryUp_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {acc i w N : Nat}
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i)) (hw : 4 * i + acc = w)
    (hN : w + 4 * N + 8 ≤ size)
    (hlt : val32 s.mem base (w + 4 * N) 2 + (s.gpr .ebx).toNat < 2 ^ 64) :
    WP isa (.block (carryUp acc N)) s fun u =>
      Outside base (w + 4 * N) 8 s.mem u.mem ∧
      val32 u.mem base (w + 4 * N) 2 = val32 s.mem base (w + 4 * N) 2 + (s.gpr .ebx).toNat ∧
      Keeps [.eax] s u := by
  have hn := hs.nowrap
  have e₀ : 4 * i + (acc + 4 * N) = w + 4 * N := by omega
  have e₁ : 4 * i + (acc + 4 * N + 4) = w + 4 * N + 4 := by omega
  simp only [carryUp]
  refine wp_movS (readSrc_at hs hp (d := acc + 4 * N) (by omega)) fun s₁ u₁ cf₁ => ?_
  refine wp_addS rfl fun s₂ u₂ c₂ => ?_
  have k₂ : Keeps [.eax] s s₂ := ⟨fun r hr => by
      rw [u₂.other _ (by simpa using hr), u₁.other _ (by simpa using hr)],
    by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  have hs₂ := hs.of_keeps k₂ (by decide)
  have hp₂ : s₂.gpr .ebp = s₂.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [k₂.1 _ (by decide), k₂.1 _ (by decide)]; exact hp
  refine wp_storeS (hs₂.ea_at hp₂ (d := acc + 4 * N) (by omega)) (hs₂.write (n := 4) (by omega))
    fun s₃ m₃ => ?_
  have k₃ : Keeps [.eax] s s₃ := ⟨fun r hr => by rw [m₃.gpr]; exact k₂.1 r hr, by rw [m₃.rd, k₂.2.1],
    by rw [m₃.wr, k₂.2.2]⟩
  have hs₃ := hs.of_keeps k₃ (by decide)
  have hp₃ : s₃.gpr .ebp = s₃.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [k₃.1 _ (by decide), k₃.1 _ (by decide)]; exact hp
  refine wp_movS (readSrc_at hs₃ hp₃ (d := acc + 4 * N + 4) (by omega)) fun s₄ u₄ cf₄ => ?_
  refine wp_adcS rfl (by rw [cf₄, m₃.cf]; exact c₂) fun s₅ u₅ _ => ?_
  have k₅ : Keeps [.eax] s s₅ := ⟨fun r hr => by
      rw [u₅.other _ (by simpa using hr), u₄.other _ (by simpa using hr)]; exact k₃.1 r hr,
    by rw [u₅.rd, u₄.rd, k₃.2.1], by rw [u₅.wr, u₄.wr, k₃.2.2]⟩
  have hs₅ := hs.of_keeps k₅ (by decide)
  have hp₅ : s₅.gpr .ebp = s₅.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [k₅.1 _ (by decide), k₅.1 _ (by decide)]; exact hp
  refine wp_storeS (hs₅.ea_at hp₅ (d := acc + 4 * N + 4) (by omega)) (hs₅.write (n := 4) (by omega))
    fun s₆ m₆ => WP.block_nil ?_
  rw [e₀] at m₃
  rw [e₁] at m₆
  have hm₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have hm₅ : s₅.mem = s₃.mem := by rw [u₅.mem, u₄.mem]
  rw [hm₂] at m₃
  rw [hm₅, m₃.mem] at m₆
  have W₀ := writeW32_outside s.mem base (d := w + 4 * N) (s₂.gpr .eax) (by omega)
  have W₁ := writeW32_outside (s.mem.writeW (off base (w + 4 * N)) (s₂.gpr .eax)) base
    (d := w + 4 * N + 4) (s₅.gpr .eax) (by omega)
  rw [← m₆.mem] at W₁
  refine ⟨(W₀.mono (Nat.le_refl _) (by omega)).trans (W₁.mono (by omega) (by omega)), ?_,
    ⟨fun r hr => by rw [m₆.gpr]; exact k₅.1 r hr, by rw [m₆.rd, k₅.2.1], by rw [m₆.wr, k₅.2.2]⟩⟩
  -- The words.
  have a₂ : s₂.gpr .eax = s.mem.readW (off base (w + 4 * N)) 32 + s.gpr .ebx := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), e₀]
  have h0 : ∀ x : BitVec 32, x + 0 = x := BitVec.add_zero
  have a₅ : s₅.gpr .eax = s₃.mem.readW (off base (w + 4 * N + 4)) 32 +
      (BitVec.ofBool (decide (2 ^ 32 ≤ (s₁.gpr .eax).toNat + (s₁.gpr .ebx).toNat))).setWidth 32 := by
    rw [u₅.gpr, u₄.gpr, e₁, h0]
  have t₁ : w32 s₃.mem base (w + 4 * N + 4) = w32 s.mem base (w + 4 * N + 4) := by
    rw [m₃.mem]; exact w32_write_ne hn (by omega) (by omega) (by omega) _
  rw [u₁.gpr, u₁.other _ (by decide), e₀, m₃.mem] at a₅
  simp only [val32, Nat.mul_zero, Nat.add_zero]
  rw [m₆.mem, w32_write_ne hn (by omega) (by omega) (by omega), w32_write_self, w32_write_self,
    a₂, a₅, BitVec.toNat_add, BitVec.toNat_add, ofBool_toNat]
  simp only [val32, Nat.mul_zero, Nat.add_zero] at hlt
  rw [m₃.mem] at t₁
  simp only [w32] at t₁ hlt ⊢
  rw [t₁]
  have := (s.mem.readW (off base (w + 4 * N)) 32).isLt
  have := (s.gpr .ebx).isLt
  by_cases hc : 2 ^ 32 ≤ (s.mem.readW (off base (w + 4 * N)) 32).toNat + (s.gpr .ebx).toNat <;>
    simp only [hc, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

theorem pow32_add (a b : Nat) : 2 ^ (32 * (a + b)) = 2 ^ (32 * a) * 2 ^ (32 * b) := by
  rw [Nat.mul_add, Nat.pow_add]

/-- The window `+= ecx · [b]` (`N` words), when the sum fits its `N + 2`
words. -/
theorem mulRow_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {acc b i w N : Nat}
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i)) (hw : 4 * i + acc = w)
    (hb : b + 4 * N ≤ size) (hwN : w + 4 * N + 8 ≤ size) (hsep : b + 4 * N ≤ w ∨ w + 4 * N + 8 ≤ b)
    (hlt : val32 s.mem base w (N + 2) + (s.gpr .ecx).toNat * val32 s.mem base b N < 2 ^ (32 * (N + 2))) :
    WP isa (.block (mulRow acc b N)) s fun u =>
      Outside base w (4 * N + 8) s.mem u.mem ∧
      val32 u.mem base w (N + 2) = val32 s.mem base w (N + 2) + (s.gpr .ecx).toNat * val32 s.mem base b N ∧
      Keeps [.eax, .ebx, .edx] s u := by
  have hn := hs.nowrap
  simp only [mulRow, List.cons_append]
  refine wp_movS rfl fun s₀ u₀ _ => ?_
  have k₀ : Keeps [.eax, .ebx, .edx] s s₀ := ⟨fun r hr => u₀.other r (by simp_all), u₀.rd, u₀.wr⟩
  have hs₀ := hs.of_keeps k₀ (by decide)
  have hp₀ : s₀.gpr .ebp = s₀.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [k₀.1 _ (by decide), k₀.1 _ (by decide)]; exact hp
  refine WP.block_append (WP.mono (steps_ok hs₀ hp₀ hw (k := N) hb (by omega) (by omega))
    fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
  have k₁ := k₀.trans K₁
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hp₁ : s₁.gpr .ebp = s₁.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [k₁.1 _ (by decide), k₁.1 _ (by decide)]; exact hp
  have z : (0 : BitVec 32).toNat = 0 := rfl
  rw [u₀.gpr, u₀.mem, u₀.other _ (by decide), z, Nat.add_zero] at V₁
  rw [u₀.mem] at O₁
  have hhi : val32 s₁.mem base (w + 4 * N) 2 = val32 s.mem base (w + 4 * N) 2 := O₁.val32 (by omega) (by omega)
  have hsplit : val32 s.mem base w (N + 2) = val32 s.mem base w N + 2 ^ (32 * N) * val32 s.mem base (w + 4 * N) 2 :=
    val32_append _ _ _ _ _
  rw [pow32_add, show 32 * 2 = 64 by rfl] at hlt
  have hP : 0 < 2 ^ (32 * N) := Nat.two_pow_pos _
  have hlt₁ : val32 s₁.mem base (w + 4 * N) 2 + (s₁.gpr .ebx).toNat < 2 ^ 64 := by
    rw [hhi]
    rw [hsplit] at hlt
    refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (32 * N)) ?_
    rw [Nat.mul_add]
    omega
  refine WP.mono (carryUp_ok hs₁ hp₁ hw hwN hlt₁) fun u ⟨O₂, V₂, K₂⟩ => ⟨?_, ?_, k₁.trans (K₂.mono (by simp))⟩
  · exact (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))
  · rw [val32_append, V₂, (O₂.val32 (d := w) (k := N) (by omega) (by omega)), hhi, hsplit, Nat.mul_add]
    omega

end VG.Proof.Mont.X86
