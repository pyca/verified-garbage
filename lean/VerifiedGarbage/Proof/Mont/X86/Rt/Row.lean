module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Step
public import VerifiedGarbage.Proof.Mont.X86.Rt.Args
public import VerifiedGarbage.Proof.Mont.X86.Row
import VerifiedGarbage.Proof.Framework.Omega

/-! # A row of the run-time width multiplication

`mulRow x`: the window at `ebp` `+= [edi + multOff] ·` the number at the
offset argument `x`, of `N` words, `N = 2 n`: `ecx` at the number, `esi`
counting `4 N` bytes down, a step a word (`mulStep_ok`), then the carry into
the window's top two words and `ebp` back (`carry_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Rt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt VG.Proof.Mont VG.Proof.Mont.X86

/-- The carry `ebx` into the two words at `ebp = W + y`. -/
theorem carry_ok {s : State} {W : Addr} {L : Nat} (hw : Ws s W L) {y : Nat}
    (hp : PtrAt s W .ebp y) (hy : y + 8 ≤ L)
    (hlt : val32 s.mem W y 2 + (s.gpr .ebx).toNat < 2 ^ 64) :
    WP isa (.block carryWords) s fun u =>
      Outside W y 8 s.mem u.mem ∧
      val32 u.mem W y 2 = val32 s.mem W y 2 + (s.gpr .ebx).toNat ∧
      Keeps [.eax] s u := by
  have hn := hw.nowrap
  simp only [carryWords]
  refine wp_movS (readSrc_ptr hw hp (d := 0) (by omega)) fun s₁ u₁ _ => ?_
  refine wp_addS rfl fun s₂ u₂ c₂ => ?_
  have k₂ : Keeps [.eax] s s₂ := (u₁.keeps.trans u₂.keeps)
  have hw₂ := hw.of_keeps k₂
  have hp₂ : PtrAt s₂ W .ebp y := by rw [PtrAt, k₂.1 _ (by decide)]; exact hp
  refine wp_storeS (ea_ptr hw₂ hp₂ (d := 0) (by omega)) (ws_write hw₂ (y := y + 0) (n := 4) (by omega))
    fun s₃ m₃ => ?_
  have k₃ : Keeps [.eax] s s₃ := k₂.widen (m₃.keeps [])
  have hw₃ := hw.of_keeps k₃
  have hp₃ : PtrAt s₃ W .ebp y := by rw [PtrAt, k₃.1 _ (by decide)]; exact hp
  refine wp_movS (readSrc_ptr hw₃ hp₃ (d := 4) (by omega)) fun s₄ u₄ cf₄ => ?_
  refine wp_adcS rfl (by rw [cf₄, m₃.cf]; exact c₂) fun s₅ u₅ _ => ?_
  have k₅ : Keeps [.eax] s s₅ := (k₃.trans u₄.keeps).trans u₅.keeps
  have hw₅ := hw.of_keeps k₅
  have hp₅ : PtrAt s₅ W .ebp y := by rw [PtrAt, k₅.1 _ (by decide)]; exact hp
  refine wp_storeS (ea_ptr hw₅ hp₅ (d := 4) (by omega)) (ws_write hw₅ (y := y + 4) (n := 4) (by omega))
    fun s₆ m₆ => WP.block_nil ?_
  rw [Nat.add_zero] at m₃
  have hm₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have hm₅ : s₅.mem = s₃.mem := by rw [u₅.mem, u₄.mem]
  rw [hm₂] at m₃
  rw [hm₅, m₃.mem] at m₆
  have W₀ := writeW32_outside s.mem W (d := y) (s₂.gpr .eax) (by omega)
  have W₁ := writeW32_outside (s.mem.writeW (off W y) (s₂.gpr .eax)) W (d := y + 4) (s₅.gpr .eax) (by omega)
  rw [← m₆.mem] at W₁
  refine ⟨(W₀.mono (Nat.le_refl _) (by omega)).trans (W₁.mono (by omega) (by omega)), ?_,
    k₅.widen (m₆.keeps [])⟩
  have a₂ : s₂.gpr .eax = s.mem.readW (off W y) 32 + s.gpr .ebx := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), Nat.add_zero]
  have h0 : ∀ x : BitVec 32, x + 0 = x := BitVec.add_zero
  have a₅ : s₅.gpr .eax = s₃.mem.readW (off W (y + 4)) 32 +
      (BitVec.ofBool (decide (2 ^ 32 ≤ (s₁.gpr .eax).toNat + (s₁.gpr .ebx).toNat))).setWidth 32 := by
    rw [u₅.gpr, u₄.gpr, h0]
  have t₁ : w32 s₃.mem W (y + 4) = w32 s.mem W (y + 4) := by
    rw [m₃.mem]; exact w32_write_ne hn (by omega) (by omega) (by omega) _
  rw [u₁.gpr, u₁.other _ (by decide), Nat.add_zero, m₃.mem] at a₅
  simp only [val32, Nat.mul_zero, Nat.add_zero]
  rw [m₆.mem, w32_write_ne hn (by omega) (by omega) (by omega), w32_write_self, w32_write_self,
    a₂, a₅, BitVec.toNat_add, BitVec.toNat_add, ofBool_toNat]
  simp only [val32, Nat.mul_zero, Nat.add_zero] at hlt
  rw [m₃.mem] at t₁
  simp only [w32] at t₁ hlt ⊢
  rw [t₁]
  have := (s.mem.readW (off W y) 32).isLt
  have := (s.gpr .ebx).isLt
  simp only [Nat.add_zero]
  by_cases hc : 2 ^ 32 ≤ (s.mem.readW (off W y) 32).toNat + (s.gpr .ebx).toNat <;>
    simp only [hc, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

/-- What a row changes. -/
abbrev clob6 : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

/-- `8 n` bytes in `4 N` words (`N = 2 n`), below `2³²`. -/
theorem len_ok {A : Nat → BitVec 32} {N : Nat} (hn : (A 2).toNat * 8 = 4 * N) (hN32 : 4 * N < 2 ^ 32) :
    (A 2).toNat * 2 ^ (3 + 0) % 2 ^ 32 = 4 * N := by
  rw [show 2 ^ (3 + 0) = 8 from rfl, hn, Nat.mod_eq_of_lt hN32]

/-- The window of `N + 2` words at `ebp = W + w` `+= [edi + multOff] ·` the
number of `N` words at the offset argument `xi`, when the sum fits. -/
theorem mulRow_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (hw : Ws s W L) (ha : Args s W L A)
    (hA0 : (A 0).toNat = W.toNat) {xi bx S w N : Nat} (hxi : xi < 9) (hb : (A xi).toNat = bx)
    (hn : (A 2).toNat * 8 = 4 * N) (hN : 0 < N) (hN32 : 4 * N < 2 ^ 32)
    (hedi : PtrAt s W .edi S) (hebp : PtrAt s W .ebp w)
    (hbL : bx + 4 * N ≤ L) (hwL : w + 4 * N + 8 ≤ L) (hmL : S + multOff + 4 ≤ L)
    (hsep : bx + 4 * N ≤ w ∨ w + 4 * N + 8 ≤ bx) (hsm : S + multOff + 4 ≤ w ∨ w + 4 * N + 8 ≤ S + multOff)
    (hlt : val32 s.mem W w (N + 2) + w32 s.mem W (S + multOff) * val32 s.mem W bx N < 2 ^ (32 * (N + 2))) :
    WP isa (Rt.mulRow (Rt.arg xi)) s fun u =>
      Outside W w (4 * N + 8) s.mem u.mem ∧
      val32 u.mem W w (N + 2) = val32 s.mem W w (N + 2) + w32 s.mem W (S + multOff) * val32 s.mem W bx N ∧
      PtrAt u W .ebp w ∧ Keeps clob6 s u := by
  have hnw := hw.nowrap
  unfold Rt.mulRow
  -- The pointer to the number, and the count.
  have setup : WP isa (.block ([.mov .ebx (.imm 0)] ++ ptr .ecx (Rt.arg xi) .edx ++ lenTimes .esi 0)) s
      fun (t : State) => Keeps [.ebx, .ecx, .edx, .esi] s t ∧ t.mem = s.mem ∧ t.gpr .ebx = 0 ∧ PtrAt t W .ecx bx ∧
        (t.gpr .esi).toNat = 4 * N := by
    simp only [List.cons_append, List.nil_append]
    refine wp_movS rfl fun s₀ u₀ _ => ?_
    refine WP.block_append (WP.mono (ptr_ok (ha.of_upd u₀ (by decide)) hxi (r := .ecx) (t := .edx)
      (by decide) (by decide)) fun s₁ ⟨e₁, _, m₁, K₁⟩ => ?_)
    have ha₁ : Args s₁ W L A := (ha.of_upd u₀ (by decide)).of_keeps K₁ (by decide) (by rw [m₁]; exact Outs.refl _ _ _)
    refine WP.mono (lenTimes_ok ha₁ (r := .esi) 0) fun s₂ ⟨l₂, m₂, K₂⟩ => ?_
    refine ⟨(((u₀.keeps.mono (rs' := [.ebx, .ecx, .edx, .esi]) (by decide)).widen K₁).widen K₂),
      by rw [m₂, m₁, u₀.mem], ?_, ?_, by rw [l₂, len_ok hn hN32]⟩
    · rw [K₂.1 _ (by decide), K₁.1 _ (by decide), u₀.gpr]
    · rw [PtrAt, K₂.1 _ (by decide), e₁, BitVec.toNat_add, hA0, hb]
  refine WP.seq (WP.mono setup fun t₀ ⟨K₀, m₀, ebx₀, ecx₀, esi₀⟩ => ?_)
  -- The loop: `j` steps done.
  let I : Nat → State → Prop := fun j t =>
    Keeps clob6 s t ∧ PtrAt t W .ecx (bx + 4 * j) ∧ PtrAt t W .ebp (w + 4 * j) ∧
    (t.gpr .esi).toNat = 4 * (N - j) ∧ Outside W w (4 * j) s.mem t.mem ∧
    val32 t.mem W w j + 2 ^ (32 * j) * (t.gpr .ebx).toNat =
      val32 s.mem W w j + w32 s.mem W (S + multOff) * val32 s.mem W bx j
  have I₀ : I 0 t₀ := by
    refine ⟨K₀.mono (by decide), by simpa using ecx₀, ?_, by simpa using esi₀, by rw [m₀]; exact Outside.refl _ _ _ _, ?_⟩
    · rw [PtrAt, K₀.1 _ (by decide)]; simpa using hebp
    · rw [ebx₀]; simp [val32]
  refine WP.seq (WP.mono (WP.loop (M := isa) (Q := I N) (fun m t => ∃ j, m = N - j ∧ j < N ∧ I j t) ?_ N t₀
    ⟨0, by omega, hN, I₀⟩) ?_)
  · rintro m t ⟨j, rfl, hj, K, ecx, ebp, esi, O, V⟩
    have ht := hw.of_keeps K
    have edi : PtrAt t W .edi S := by rw [PtrAt, K.1 _ (by decide)]; exact hedi
    refine WP.mono (mulStep_ok ht edi ecx ebp esi hj (by omega) (by omega) (by omega))
      fun u ⟨mu, bu, cu, pu, su, zu, Ku⟩ => ?_
    have mk : w32 t.mem W (S + multOff) = w32 s.mem W (S + multOff) := O.w32 (by omega) (by omega)
    have bk : w32 t.mem W (bx + 4 * j) = w32 s.mem W (bx + 4 * j) := O.w32 (by omega) (by omega)
    have tk : w32 t.mem W (w + 4 * j) = w32 s.mem W (w + 4 * j) := O.w32 (by omega) (by omega)
    rw [mk, bk, tk] at mu bu
    have Wr := writeW32_outside t.mem W (d := w + 4 * j)
      (BitVec.ofNat 32 (w32 s.mem W (S + multOff) * w32 s.mem W (bx + 4 * j) + (t.gpr .ebx).toNat +
        w32 s.mem W (w + 4 * j))) (by omega)
    rw [← mu] at Wr
    have I' : I (j + 1) u := by
      refine ⟨K.trans (Ku.mono (by decide)), cu, pu, su,
        (O.mono (Nat.le_refl _) (by omega)).trans (Wr.mono (by omega) (by omega)), ?_⟩
      have hlow : val32 u.mem W w j = val32 t.mem W w j := Wr.val32 (by omega) (by omega)
      have htop : w32 u.mem W (w + 4 * j) = (w32 s.mem W (S + multOff) * w32 s.mem W (bx + 4 * j) +
          (t.gpr .ebx).toNat + w32 s.mem W (w + 4 * j)) % 2 ^ 32 := by
        rw [mu, w32_write_self, BitVec.toNat_ofNat]
      rw [val32_succ, val32_succ, val32_succ, hlow, htop, bu, pow32_succ]
      generalize hxd : w32 s.mem W (S + multOff) * w32 s.mem W (bx + 4 * j) + (t.gpr .ebx).toNat +
        w32 s.mem W (w + 4 * j) = x at *
      have hx := Nat.div_add_mod x (2 ^ 32)
      generalize 2 ^ (32 * j) = P at *
      grind
    by_cases hjN : j + 1 = N
    · exact .inl ⟨by simp only [eval, zu, hjN, decide_true, Option.map_some, Bool.not_true], hjN ▸ I'⟩
    · exact .inr ⟨by simp only [eval, zu, decide_eq_false hjN, Option.map_some, Bool.not_false],
        N - (j + 1), by omega, j + 1, rfl, by omega, I'⟩
  · intro t ⟨K, _, ebp, _, O, V⟩
    have ht := hw.of_keeps K
    -- The carry into the window's top two words.
    have hhi : val32 t.mem W (w + 4 * N) 2 = val32 s.mem W (w + 4 * N) 2 := O.val32 (by omega) (by omega)
    have hsplit : val32 s.mem W w (N + 2) =
        val32 s.mem W w N + 2 ^ (32 * N) * val32 s.mem W (w + 4 * N) 2 := val32_append _ _ _ _ _
    rw [pow32_add, show 32 * 2 = 64 by rfl] at hlt
    have hP : 0 < 2 ^ (32 * N) := Nat.two_pow_pos _
    have hlt₁ : val32 t.mem W (w + 4 * N) 2 + (t.gpr .ebx).toNat < 2 ^ 64 := by
      rw [hhi]
      rw [hsplit] at hlt
      refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (32 * N)) ?_
      rw [Nat.mul_add]
      have := val32_lt t.mem W w N
      omega
    unfold Rt.carryUp
    rw [List.append_assoc]
    refine WP.block_append (WP.mono (carry_ok ht ebp (by omega) hlt₁) fun t₁ ⟨O₁, V₁, K₁⟩ => ?_)
    have Kt₁ : Keeps clob6 s t₁ := K.trans (K₁.mono (by decide))
    have Ost₁ : Outside W w (4 * N + 8) s.mem t₁.mem :=
      (O.mono (Nat.le_refl _) (by omega)).trans (O₁.mono (by omega) (by omega))
    have ha₁ : Args t₁ W L A := ha.of_keeps Kt₁ (by decide)
      (Outs.of_outside (Ost₁.mono (by omega) (by omega)) (List.mem_singleton_self _))
    refine WP.block_append (WP.mono (lenTimes_ok ha₁ (r := .eax) 0) fun t₂ ⟨l₂, m₂, K₂⟩ => ?_)
    refine wp_subS rfl fun t₃ u₃ _ => WP.block_nil ?_
    have ebp₂ : PtrAt t₂ W .ebp (w + 4 * N) := by rw [PtrAt, K₂.1 _ (by decide), K₁.1 _ (by decide)]; exact ebp
    refine ⟨by rw [u₃.mem, m₂]; exact Ost₁, ?_, ?_, (Kt₁.trans (K₂.mono (by decide))).trans (u₃.keeps.mono (by decide))⟩
    · rw [u₃.mem, m₂, val32_append, V₁, O₁.val32 (d := w) (k := N) (by omega) (by omega), hhi, hsplit, Nat.mul_add]
      have hlow : val32 t.mem W w N + 2 ^ (32 * N) * (t.gpr .ebx).toNat =
          val32 s.mem W w N + w32 s.mem W (S + multOff) * val32 s.mem W bx N := V
      omega
    · rw [PtrAt, u₃.gpr, ptr_sub ebp₂ _ (by rw [l₂, len_ok hn hN32]; omega), l₂, len_ok hn hN32]
      congr 2; omega

end VG.Proof.Mont.X86.Rt
