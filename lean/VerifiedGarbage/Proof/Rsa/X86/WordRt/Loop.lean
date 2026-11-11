module

public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Step
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Framework.Omega

/-! # `WordModRt` on i686: the remainder

`seed_ok`: `r` set to the dividend's top `W' - 1` words, and the steps'
count `X - W' + 1` into the header, for the dividend's `X` words; `wordMod_ok`:
`r = x mod m'` for `m'` the divisor with its top bit set (`orTop`), by the
steps, each bringing down the dividend's next word (`step_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.WordRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Keep arr num S slot)
open VG.Proof.Rsa.X86.KeyRt (RtWs kw arrPtr_ok lenSrc bytesB_ok)
open VG.Impl.Rsa.X86.WordModRt (oD oV oD1 oQ oU0 oU2 oSteps oDig h0)

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- The dividend's words: `w`, or `2 w` across two arrays (`wide`). -/
abbrev xw (len : Nat) (wide : Bool) : Nat := if wide then 2 * kw len else kw len

/-- `xBytes wide r`: `r = 4 X`. -/
theorem xBytes_ok {s : State} {is : List Instr} {Q : State → Prop} (h : RtWs L s B Z len N) {wide : Bool} {r : Reg}
    (k : ∀ t, Keeps [r] s t → t.mem = s.mem → (t.gpr r).toNat = 4 * xw len wide → WP isa (.block is) t Q) :
    WP isa (.block (VG.Impl.Rsa.X86.WordModRt.xBytes L wide r ++ is)) s Q := by
  have hw := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  unfold VG.Impl.Rsa.X86.WordModRt.xBytes
  rw [List.append_assoc]
  refine bytesB_ok (lenSrc h) h.lenLe fun t K m e => ?_
  cases wide with
  | false => simpa [xw] using k t K m (by simpa [xw] using e)
  | true =>
    simp only [ite_true, List.cons_append, List.nil_append]
    refine wp_addS rfl fun u U _ => k u (K.trans U.keeps) (U.mem.trans m) ?_
    rw [U.gpr, BitVec.toNat_add, e]; simp only [xw, ite_true]; omega

theorem val32_high (m : Mem) (B : Addr) (d k j : Nat) :
    val32 m B d (k + j) / 2 ^ (32 * k) = val32 m B (d + 4 * k) j := by
  rw [val32_append, Nat.add_comm, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt (val32_lt _ _ _ _),
    Nat.add_zero]

theorem oSteps_val' : oSteps = 72 := rfl

/-- `seed ml x r wide`: `r`'s words `0, …, W' - 2` the dividend's top `W' - 1` words, its words
`W' - 1, …, w` zero, and `X - W' + 1` at `oSteps`, for the dividend's `X ≥ W'` words. -/
theorem seed_ok {s : State} (h : RtWs L s B Z len N) {ml a x r : Nat} {wide : Bool} (hm : MLen s B Z ml a)
    (hx : x + wide.toNat < N) (hr : r < N) (hxr : r ≠ x) (hxr1 : wide = true → r ≠ x + 1)
    (h3 : 3 ≤ wq a) (hw : wq a ≤ kw len) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.seed L ml x r wide) s fun v => RtWs L v B Z len N ∧
      Keep B (kw len) [r] [oSteps] s.mem v.mem ∧
      val32 v.mem B (arr (kw len) r) (kw len + 1) =
        val32 s.mem B (arr (kw len) x) (xw len wide) / 2 ^ (32 * (xw len wide - (wq a - 1))) ∧
      slot v.mem B oSteps = xw len wide - wq a + 1 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s v := by
  have nw := h.ws.workspace.nowrap
  have fr := h.ws.arr_fit hr
  have fx := h.ws.arr_fit (j := x + wide.toNat) hx
  have hdr := h.ws.hdr_le
  have hkw := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  simp only [S] at fr fx
  simp only [VG.Impl.Rsa.X86.Keys.hdr] at hdr
  have ws := h.rt
  have hX : wq a ≤ xw len wide := by cases wide <;> simp only [xw, Bool.false_eq_true, ↓reduceIte] <;> omega
  have hX4 : arr (kw len) x + 4 * xw len wide + 4 ≤ arr (kw len) (x + wide.toNat) + 4 * (kw len + 2) := by
    cases wide <;> simp only [xw, Bool.toNat_false, Bool.toNat_true, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
      VG.Proof.Rsa.X86.Keys.arr_succ, S] <;> omega
  have sepr : arr (kw len) r + 4 * (kw len + 2) ≤ arr (kw len) x ∨
      arr (kw len) x + 4 * xw len wide + 4 ≤ arr (kw len) r := by
    rcases Nat.lt_or_gt_of_ne hxr with hlt | hgt
    · have := VG.Proof.Rsa.X86.Keys.arr_end (w := kw len) hlt; simp only [S] at this; omega
    · cases wide with
      | false =>
        have := VG.Proof.Rsa.X86.Keys.arr_end (w := kw len) hgt
        simp only [S, xw, Bool.false_eq_true, ↓reduceIte] at this ⊢; right; omega
      | true =>
        have hne := hxr1 rfl
        have h2' : x + 1 < r := by omega
        have := VG.Proof.Rsa.X86.Keys.arr_end (w := kw len) h2'
        simp only [S, xw, ite_true, VG.Proof.Rsa.X86.Keys.arr_succ] at this ⊢; right; omega
  unfold VG.Impl.Rsa.X86.WordModRt.seed
  simp only [VG.Impl.Rsa.X86.WordModRt.seqs]
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.KeyRt.zeroWide_ok h hr) fun u₁ ⟨h₁, k₁, z₁, K₁⟩ => ?_)
  have xk : ∀ o, arr (kw len) x ≤ o → o + 4 ≤ arr (kw len) x + 4 * xw len wide + 4 →
      w32 u₁.mem B o = w32 s.mem B o := fun o h1 h2 => by
    have := VG.Proof.Rsa.X86.KeyRt.keep_outside h.ws k₁ (by simpa using hr) (by simp)
    have O : Outside B (arr (kw len) r) (4 * (kw len + 2)) s.mem u₁.mem := fun y hy =>
      k₁ y fun q hq => by
        simp only [VG.Proof.Rsa.X86.Keys.ranges, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
          List.mem_cons, List.not_mem_nil, or_false, S] at hq
        subst hq; exact hy
    exact O.w32 (by omega) (by omega)
  -- The pointers.
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.seq (arrPtr_ok (lenSrc h₁) h₁.lenLe h₁.edi (r := .esi) (t := .edx) (j := x) (by decide) (by decide)
    (by omega) fun u₂ K₂ m₂ p₂ _ => ?_)
  refine xBytes_ok (h₁.keep K₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _)) (wide := wide)
    (r := .ecx) fun u₃ K₃ m₃ e₃ => wp_addS rfl fun u₄ U₄ _ => ?_
  have hm₁ : MLen u₁ B Z ml a := hm.keep K₁ (by decide) (VG.Proof.Rsa.X86.KeyRt.keep_outside h.ws k₁
    (by simpa using hr) (by simp))
  have K₂₄ : Keeps [.ecx, .edx, .esi] u₁ u₄ := ((K₂.mono (by decide)).trans (K₃.mono (by decide))).trans
    (U₄.keeps.mono (by decide))
  have m₄ : u₄.mem = u₁.mem := by rw [U₄.mem, m₃, m₂]
  refine width4_ok (hm₁.keep K₂₄ (by decide) (by rw [m₄]; exact Outside.refl _ _ _ _)) fun u₅ K₅ m₅ e₅ => ?_
  refine wp_subS rfl fun u₆ U₆ _ => wp_subS rfl fun u₇ U₇ _ => ?_
  have K₂₇ : Keeps [.ecx, .edx, .esi] u₁ u₇ := (K₂₄.trans (K₅.mono (by decide))).trans
    ((U₆.keeps.mono (by decide)).trans (U₇.keeps.mono (by decide)))
  have m₇ : u₇.mem = u₁.mem := by rw [U₇.mem, U₆.mem, m₅, m₄]
  have edi₇ : (u₇.gpr .edi).toNat = B.toNat := by rw [K₂₇.1 _ (by decide)]; exact h₁.edi
  have esi₇ : PtrAt u₇ B .esi (arr (kw len) x + 4 * (xw len wide - (wq a - 1))) := by
    have hw4 : (BitVec.ofNat 32 (4 * wq a)).toNat = 4 * wq a := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := hm.le; omega)
    have p₄ : (u₄.gpr .esi).toNat = B.toNat + (arr (kw len) x + 4 * xw len wide) := by
      rw [U₄.gpr, BitVec.toNat_add, e₃, show (u₃.gpr .esi) = u₂.gpr .esi from K₃.1 _ (by decide), p₂]
      have := B.isLt
      omega
    rw [PtrAt, U₇.gpr, BitVec.toNat_sub, U₆.gpr, U₆.other .esi (by decide), K₅.1 .esi (by decide), p₄, e₅,
      BitVec.toNat_sub, hw4, show (4 : BitVec 32).toNat = 4 from rfl]
    have := B.isLt
    omega
  have hl₇ := (lenSrc h₁).keep K₂₇ (by decide) m₇
  refine arrPtr_ok hl₇ h₁.lenLe edi₇ (r := .ebp) (t := .edx) (j := r) (by decide) (by decide) (by omega)
    fun u₈ K₈ m₈ p₈ _ => ?_
  have K₂₈ : Keeps [.ecx, .edx, .esi, .ebp] u₁ u₈ := (K₂₇.mono (by decide)).trans (K₈.mono (by decide))
  have m₈' : u₈.mem = u₁.mem := by rw [m₈, m₇]
  refine width4_ok (hm₁.keep K₂₈ (by decide) (by rw [m₈']; exact Outside.refl _ _ _ _)) fun u₉ K₉ m₉ e₉ =>
    wp_subZ rfl fun u₁₀ U₁₀ z₁₀ => WP.block_nil ?_
  have K₁₀ : Keeps [.ecx, .edx, .esi, .ebp, .edi] u₁ u₁₀ := ((K₂₈.mono (by decide)).trans (K₉.mono (by decide))).trans
    (U₁₀.keeps.mono (by decide))
  have m₁₀ : u₁₀.mem = u₁.mem := by rw [U₁₀.mem, m₉, m₈']
  have hw4 : (BitVec.ofNat 32 (4 * wq a)).toNat = 4 * wq a := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := hm.le; omega)
  have di₁₀ : (u₁₀.gpr .edi).toNat = 4 * (wq a - 1) := by
    rw [U₁₀.gpr, BitVec.toNat_sub, e₉, hw4, show (4 : BitVec 32).toNat = 4 from rfl]; omega
  have zf : u₁₀.zf = some false := by
    rw [z₁₀, ← U₁₀.gpr]
    congr 1
    rw [beq_eq_false_iff_ne]
    intro hc
    have := congrArg BitVec.toNat hc
    rw [di₁₀] at this; simp at this; omega
  refine WP.seq (WP.ite false zf (fun f => absurd f (by decide)) fun _ => ?_)
  -- The copy.
  have g : SubGeo B Z (arr (kw len) r) (arr (kw len) r) (arr (kw len) x + 4 * (xw len wide - (wq a - 1)))
      (wq a - 1) :=
    ⟨nw, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have I₀ : CopyI u₁₀ B (arr (kw len) r) (arr (kw len) x + 4 * (xw len wide - (wq a - 1))) (wq a - 1) 0 u₁₀ :=
    ⟨by rw [Nat.mul_zero, Nat.add_zero, PtrAt, U₁₀.other _ (by decide), K₉.1 _ (by decide), K₈.1 _ (by decide)];
        exact esi₇,
      by rw [Nat.mul_zero, Nat.add_zero, PtrAt, U₁₀.other _ (by decide), K₉.1 _ (by decide)]; exact p₈,
      by apply BitVec.eq_of_toNat_eq; rw [di₁₀, Nat.sub_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)],
      Keeps.refl _ _, Outside.refl _ _ _ _, by simp [val32]⟩
  have wsu := ws.of_keeps K₁ |>.of_keeps K₁₀
  refine WP.mono (WP.loop (M := isa)
    (Q := fun u => CopyI u₁₀ B (arr (kw len) r) (arr (kw len) x + 4 * (xw len wide - (wq a - 1))) (wq a - 1)
      (wq a - 1) u)
    (fun n u => ∃ j, n = wq a - 1 - j ∧ j < wq a - 1 ∧
      CopyI u₁₀ B (arr (kw len) r) (arr (kw len) x + 4 * (xw len wide - (wq a - 1))) (wq a - 1) j u) ?_ _ u₁₀
      ⟨0, rfl, by omega, I₀⟩) fun u I => ?_
  · rintro n u ⟨j, rfl, hj, I⟩
    refine WP.mono (copyStep_ok wsu g hj I) fun u' ⟨z, I'⟩ => ?_
    by_cases e : j + 1 = wq a - 1
    · exact .inl ⟨by simp only [eval, z, e, decide_true, Option.map_some, Bool.not_true], e ▸ I'⟩
    · exact .inr ⟨by simp only [eval, z, e, decide_false, Option.map_some, Bool.not_false], wq a - 1 - (j + 1),
        by omega, j + 1, rfl, by omega, I'⟩
  -- The steps' count.
  have K₁u : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp, .edi] u₁ u := (K₁₀.mono (by decide)).trans I.keep
  have O₁u : Outside B (arr (kw len) r) (4 * (wq a - 1)) u₁.mem u.mem := by rw [← m₁₀]; exact I.out
  have Z₁u : Outside B 0 Z u₁.mem u.mem := O₁u.mono (Nat.zero_le _) (by omega)
  have ca := h₁.wsArg.keep K₁u (by decide) Z₁u
  simp only [restoreEdi, List.cons_append, List.nil_append]
  refine wp_movS ca.readSrc fun v₁ V₁ _ => ?_
  have K₁v₁ : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] u₁ v₁ :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .esi, .ebp])
      ((K₁u.trans (V₁.keeps.mono (by decide))).mono (by decide)) (V₁.gpr.trans h₁.edi_eq.symm)
  have hv₁ : RtWs L v₁ B Z len N := h₁.keep K₁v₁ (by decide) (by decide) (by rw [V₁.mem]; exact Z₁u)
  refine xBytes_ok hv₁ (wide := wide) (r := .eax) fun v₂ K₂' m₂' e₂' => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun v₃ V₃ => ?_
  have hm₃ : MLen v₃ B Z ml a := hm₁.keep ((K₁v₁.trans (K₂'.mono (by decide))).trans (V₃.keeps.mono (by decide)))
    (by decide) (by rw [V₃.mem, m₂', V₁.mem]; exact Z₁u)
  refine width4_ok hm₃ fun v₄ K₄' m₄' e₄' => VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun v₅ V₅ => ?_
  refine wp_subS rfl fun v₆ V₆ _ => wp_addS rfl fun v₇ V₇ _ => ?_
  have K₁v₇ : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] u₁ v₇ :=
    (K₁v₁.trans (K₂'.mono (by decide))).trans (((V₃.keeps.mono (by decide)).trans (K₄'.mono (by decide))).trans
      (((V₅.keeps.mono (by decide)).trans (V₆.keeps.mono (by decide))).trans (V₇.keeps.mono (by decide))))
  have m₇' : v₇.mem = u.mem := by rw [V₇.mem, V₆.mem, V₅.mem, m₄', V₃.mem, m₂', V₁.mem]
  have hv₇ : RtWs L v₇ B Z len N := h₁.keep K₁v₇ (by decide) (by decide) (by rw [m₇']; exact Z₁u)
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.storeSlot_ok hv₇ (d := oSteps) (by decide) .eax)
    fun v ⟨hv, kv, ev, Kv⟩ => ?_
  have hXk : xw len wide ≤ 2 * kw len := by cases wide <;> simp only [xw, Bool.false_eq_true, ↓reduceIte] <;> omega
  have eax₇ : (v₇.gpr .eax).toNat = xw len wide - wq a + 1 := by
    have h3' : (v₃.gpr .eax).toNat = xw len wide := by
      rw [V₃.gpr, BitVec.toNat_ushiftRight, e₂', Nat.shiftRight_eq_div_pow]; omega
    have h5' : (v₅.gpr .ecx).toNat = wq a := by
      rw [V₅.gpr, BitVec.toNat_ushiftRight, e₄', hw4, Nat.shiftRight_eq_div_pow]; omega
    rw [V₇.gpr, BitVec.toNat_add, V₆.gpr, BitVec.toNat_sub, h5', V₅.other .eax (by decide),
      K₄'.1 .eax (by decide), h3', show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s v :=
    (K₁.mono (by decide)).trans (K₁v₇.trans (Kv.mono (by decide)))
  refine ⟨hv, ?_, ?_, by rw [ev, eax₇], Kall⟩
  · refine (k₁.mono (by simp) (by simp)).trans (Keep.trans ?_ (kv.mono (by simp) (by simp)))
    rw [m₇']
    exact Keep.of_arr (d := 0) (by simpa using O₁u) (by simp only [S]; omega) (by simp)
  · -- The words of `r`.
    have fitr := h.ws.fit64 hr
    have hk : val32 v.mem B (arr (kw len) r) (kw len + 1) = val32 u.mem B (arr (kw len) r) (kw len + 1) := by
      rw [← m₇']
      exact val32_congr fun i hi => kv.word (j := r) (i := i) (by simp only [S]; omega) (by simp) (by decide) fitr
    rw [hk, show kw len + 1 = (wq a - 1) + (kw len + 2 - wq a) by omega, val32_append, I.val, m₁₀]
    have hi : val32 u.mem B (arr (kw len) r + 4 * (wq a - 1)) (kw len + 2 - wq a) = 0 := by
      rw [O₁u.val32 (.inr (by omega)) (by omega), ← val32_high,
        show wq a - 1 + (kw len + 2 - wq a) = kw len + 1 by omega, z₁, Nat.zero_div]
    have hlo : val32 u₁.mem B (arr (kw len) x + 4 * (xw len wide - (wq a - 1))) (wq a - 1) =
        val32 s.mem B (arr (kw len) x + 4 * (xw len wide - (wq a - 1))) (wq a - 1) :=
      val32_congr fun i hi => xk _ (by omega) (by omega)
    rw [hi, Nat.mul_zero, Nat.add_zero, hlo, ← val32_high,
      show xw len wide - (wq a - 1) + (wq a - 1) = xw len wide by omega]

end VG.Proof.Rsa.X86.WordRt
