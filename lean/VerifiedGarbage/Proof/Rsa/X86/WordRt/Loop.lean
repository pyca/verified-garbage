module

public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Step
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc

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

/-- The dividend's words: `w`, its array's (`top = none`), or the divisor's `W'` and `k` more
(`top = some k`). -/
abbrev xw (len a : Nat) (top : Option Nat) : Nat :=
  match top with
  | none => kw len
  | some k => wq a + k

/-- The dividend is within its array, and at least the divisor's words. -/
theorem xw_le {len a : Nat} {top : Option Nat} (hw : wq a ≤ kw len) (htop : ∀ k, top = some k → wq a + k ≤ kw len) :
    wq a ≤ xw len a top ∧ xw len a top ≤ kw len := by
  cases top with
  | none => exact ⟨hw, Nat.le_refl _⟩
  | some k => exact ⟨Nat.le_add_right _ _, htop k rfl⟩

/-- `xBytes ml top r`: `r = 4 X`. -/
theorem xBytes_ok {s : State} {is : List Instr} {Q : State → Prop} (h : RtWs L s B Z len N) {ml a : Nat}
    (hm : MLen s B Z ml a) {top : Option Nat} (htop : ∀ k, top = some k → wq a + k ≤ kw len) {r : Reg}
    (k : ∀ t, Keeps [r] s t → t.mem = s.mem → (t.gpr r).toNat = 4 * xw len a top → WP isa (.block is) t Q) :
    WP isa (.block (VG.Impl.Rsa.X86.WordModRt.xBytes L ml top r ++ is)) s Q := by
  have hw := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  unfold VG.Impl.Rsa.X86.WordModRt.xBytes
  cases top with
  | none => exact bytesB_ok (lenSrc h) h.lenLe fun t K m e => k t K m (by simpa [xw] using e)
  | some j =>
    have hj := htop j rfl
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine width4_ok hm fun t K m e => wp_addS rfl fun u U _ => k u (K.trans U.keeps) (U.mem.trans m) ?_
    have hw4 : (BitVec.ofNat 32 (4 * wq a)).toNat = 4 * wq a := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := hm.le; omega)
    have hj4 : (BitVec.ofNat 32 (4 * j)).toNat = 4 * j := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    rw [U.gpr, BitVec.toNat_add, e, hw4, hj4]; simp only [xw]; omega

theorem val32_high (m : Mem) (B : Addr) (d k j : Nat) :
    val32 m B d (k + j) / 2 ^ (32 * k) = val32 m B (d + 4 * k) j := by
  rw [val32_append, Nat.add_comm, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt (val32_lt _ _ _ _),
    Nat.add_zero]

theorem oSteps_val' : oSteps = 72 := rfl

/-- `seed ml x r top`: `r`'s words `0, …, W' - 2` the dividend's top `W' - 1` words, its words
`W' - 1, …, w` zero, and `X - W' + 1` at `oSteps`, for the dividend's `X ≥ W'` words. -/
theorem seed_ok {s : State} (h : RtWs L s B Z len N) {ml a x r : Nat} {top : Option Nat} (hm : MLen s B Z ml a)
    (hx : x < N) (hr : r < N) (hxr : r ≠ x) (htop : ∀ k, top = some k → wq a + k ≤ kw len)
    (h3 : 3 ≤ wq a) (hw : wq a ≤ kw len) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.seed L ml x r top) s fun v => RtWs L v B Z len N ∧
      Keep B (kw len) [r] [oSteps] s.mem v.mem ∧
      val32 v.mem B (arr (kw len) r) (kw len + 1) =
        val32 s.mem B (arr (kw len) x) (xw len a top) / 2 ^ (32 * (xw len a top - (wq a - 1))) ∧
      slot v.mem B oSteps = xw len a top - wq a + 1 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s v := by
  have nw := h.ws.workspace.nowrap
  have fr := h.ws.arr_fit hr
  have fx := h.ws.arr_fit (j := x) hx
  have hdr := h.ws.hdr_le
  have hkw := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  simp only [S] at fr fx
  simp only [VG.Impl.Rsa.X86.Keys.hdr] at hdr
  have ws := h.rt
  obtain ⟨hX, hXk'⟩ := xw_le (top := top) hw htop
  have hX4 : arr (kw len) x + 4 * xw len a top + 4 ≤ arr (kw len) x + 4 * (kw len + 2) := by omega
  have sepr : arr (kw len) r + 4 * (kw len + 2) ≤ arr (kw len) x ∨
      arr (kw len) x + 4 * xw len a top + 4 ≤ arr (kw len) r := by
    rcases Nat.lt_or_gt_of_ne hxr with hlt | hgt
    · have := VG.Proof.Rsa.X86.Keys.arr_end (w := kw len) hlt; simp only [S] at this; omega
    · have := VG.Proof.Rsa.X86.Keys.arr_end (w := kw len) hgt
      simp only [S] at this ⊢; right; omega
  unfold VG.Impl.Rsa.X86.WordModRt.seed
  simp only [VG.Impl.Rsa.X86.WordModRt.seqs]
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.KeyRt.zeroWide_ok h hr) fun u₁ ⟨h₁, k₁, z₁, K₁⟩ => ?_)
  have xk : ∀ o, arr (kw len) x ≤ o → o + 4 ≤ arr (kw len) x + 4 * xw len a top + 4 →
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
  have hm₁ : MLen u₁ B Z ml a := hm.keep K₁ (by decide) (VG.Proof.Rsa.X86.KeyRt.keep_outside h.ws k₁
    (by simpa using hr) (by simp))
  refine xBytes_ok (h₁.keep K₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _))
    (hm₁.keep K₂ (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _)) htop
    (r := .ecx) fun u₃ K₃ m₃ e₃ => wp_addS rfl fun u₄ U₄ _ => ?_
  have K₂₄ : Keeps [.ecx, .edx, .esi] u₁ u₄ := ((K₂.mono (by decide)).trans (K₃.mono (by decide))).trans
    (U₄.keeps.mono (by decide))
  have m₄ : u₄.mem = u₁.mem := by rw [U₄.mem, m₃, m₂]
  refine width4_ok (hm₁.keep K₂₄ (by decide) (by rw [m₄]; exact Outside.refl _ _ _ _)) fun u₅ K₅ m₅ e₅ => ?_
  refine wp_subS rfl fun u₆ U₆ _ => wp_subS rfl fun u₇ U₇ _ => ?_
  have K₂₇ : Keeps [.ecx, .edx, .esi] u₁ u₇ := (K₂₄.trans (K₅.mono (by decide))).trans
    ((U₆.keeps.mono (by decide)).trans (U₇.keeps.mono (by decide)))
  have m₇ : u₇.mem = u₁.mem := by rw [U₇.mem, U₆.mem, m₅, m₄]
  have edi₇ : (u₇.gpr .edi).toNat = B.toNat := by rw [K₂₇.1 _ (by decide)]; exact h₁.edi
  have esi₇ : PtrAt u₇ B .esi (arr (kw len) x + 4 * (xw len a top - (wq a - 1))) := by
    have hw4 : (BitVec.ofNat 32 (4 * wq a)).toNat = 4 * wq a := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := hm.le; omega)
    have p₄ : (u₄.gpr .esi).toNat = B.toNat + (arr (kw len) x + 4 * xw len a top) := by
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
  have g : SubGeo B Z (arr (kw len) r) (arr (kw len) r) (arr (kw len) x + 4 * (xw len a top - (wq a - 1)))
      (wq a - 1) :=
    ⟨nw, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have I₀ : CopyI u₁₀ B (arr (kw len) r) (arr (kw len) x + 4 * (xw len a top - (wq a - 1))) (wq a - 1) 0 u₁₀ :=
    ⟨by rw [Nat.mul_zero, Nat.add_zero, PtrAt, U₁₀.other _ (by decide), K₉.1 _ (by decide), K₈.1 _ (by decide)];
        exact esi₇,
      by rw [Nat.mul_zero, Nat.add_zero, PtrAt, U₁₀.other _ (by decide), K₉.1 _ (by decide)]; exact p₈,
      by apply BitVec.eq_of_toNat_eq; rw [di₁₀, Nat.sub_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)],
      Keeps.refl _ _, Outside.refl _ _ _ _, by simp [val32]⟩
  have wsu := ws.of_keeps K₁ |>.of_keeps K₁₀
  refine WP.mono (WP.loop (M := isa)
    (Q := fun u => CopyI u₁₀ B (arr (kw len) r) (arr (kw len) x + 4 * (xw len a top - (wq a - 1))) (wq a - 1)
      (wq a - 1) u)
    (fun n u => ∃ j, n = wq a - 1 - j ∧ j < wq a - 1 ∧
      CopyI u₁₀ B (arr (kw len) r) (arr (kw len) x + 4 * (xw len a top - (wq a - 1))) (wq a - 1) j u) ?_ _ u₁₀
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
  have hmv₁ : MLen v₁ B Z ml a := hm₁.keep K₁v₁ (by decide) (by rw [V₁.mem]; exact Z₁u)
  refine xBytes_ok hv₁ hmv₁ htop (r := .eax) fun v₂ K₂' m₂' e₂' => ?_
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
  have hXk : xw len a top ≤ 2 * kw len := by omega
  have eax₇ : (v₇.gpr .eax).toNat = xw len a top - wq a + 1 := by
    have h3' : (v₃.gpr .eax).toNat = xw len a top := by
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
    have hlo : val32 u₁.mem B (arr (kw len) x + 4 * (xw len a top - (wq a - 1))) (wq a - 1) =
        val32 s.mem B (arr (kw len) x + 4 * (xw len a top - (wq a - 1))) (wq a - 1) :=
      val32_congr fun i hi => xk _ (by omega) (by omega)
    rw [hi, Nat.mul_zero, Nat.add_zero, hlo, ← val32_high,
      show xw len a top - (wq a - 1) + (wq a - 1) = xw len a top by omega]

/-- Word `k` of a number: its `32 k`-bit shift, modulo `2^32`. -/
theorem w32_of_val32 (m : Mem) (B : Addr) {d n k : Nat} (hk : k < n) :
    w32 m B (d + 4 * k) = val32 m B d n / 2 ^ (32 * k) % 2 ^ 32 := by
  rw [show n = k + (1 + (n - k - 1)) by omega, val32_high, val32_append]
  simp only [val32, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (m.readW _ 32).isLt]

/-- A step of the remainder: `(a mod M) 2^32 + (y mod 2^32)` reduced is `y mod M`, for
`a = ⌊y / 2^32⌋`. -/
theorem step_mod {y M : Nat} : ((y / 2 ^ 32) % M * 2 ^ 32 + y % 2 ^ 32) % M = y % M := by
  conv => rhs; rw [← Nat.div_add_mod y (2 ^ 32)]
  rw [Nat.add_mod, Nat.mul_comm (2 ^ 32), Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

/-- What `wordMod`'s loop keeps, after `i` of its `S` steps, from `s₀` (after `seed`): `r` is the
dividend's top words, shifted by `32 (S - i)` bits, modulo `M`, its words from `W'` to `w` zero,
and the count `S - i` in the header. -/
structure LoopI (L : Lay) (s₀ : State) (B : Addr) (Z len N ml a r t : Nat) (M X₀ Sc i : Nat) (u : State) : Prop where
  ws : RtWs L u B Z len N
  ml : MLen u B Z ml a
  keep : Keep B (kw len) [r, t] [oMask, oSteps, oQ, oU0, oU2, oDig] s₀.mem u.mem
  rest : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s₀ u
  val : val32 u.mem B (arr (kw len) r) (wq a) = X₀ / 2 ^ (32 * (Sc - i)) % M
  high : ∀ j, wq a ≤ j → j < kw len + 1 → mw u.mem B (kw len) r j = 0
  steps : slot u.mem B oSteps = Sc - i

/-- The dividend's words through a frame that leaves its array. -/
theorem keep_x {w n : Nat} {js ds : List Nat} {m m' : Mem} (k : Keep B w js ds m m') {x : Nat}
    (hx : x ∉ js) (hd : ∀ d ∈ ds, d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr)
    (fit : arr w x + S w ≤ 2 ^ 64) (hn : n ≤ w + 2) :
    val32 m' B (arr w x) n = val32 m B (arr w x) n :=
  val32_congr fun i hi => k.word (j := x) (i := i) (by simp only [S]; omega) (fun j hj e => hx (e ▸ hj)) hd fit

/-- A header word stored, the flags kept. -/
theorem storeSlotZ_ok {s : State} (h : RtWs L s B Z len N) {d : Nat} (hd : d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr)
    (r : Reg) :
    WP isa (.block [.store (sc d) r]) s fun t => RtWs L t B Z len N ∧ Keep B (kw len) [] [d] s.mem t.mem ∧
      slot t.mem B d = (s.gpr r).toNat ∧ Keeps [] s t ∧ t.zf = s.zf := by
  have head := h.ws.hdr_le
  refine wp_storeS (h.ws.workspace.ea (by omega)) (h.ws.workspace.write (by omega)) fun t T => WP.block_nil ?_
  have O := writeW32_outside s.mem B (d := d) (s.gpr r) (by unfold VG.Impl.Rsa.X86.Keys.hdr at hd; omega)
  rw [← T.mem] at O
  refine ⟨h.keep (T.keeps []) (by decide) (by decide) (O.mono (Nat.zero_le _) (by omega)),
    Keep.of_slot O (by simp), by unfold slot; rw [T.mem, w32_write_self], T.keeps [], T.zf⟩

/-- A step of `wordMod`'s loop: the dividend's word `Sc - i - 1` into the header, `step`, and the
count down. -/
theorem digitStep_ok {s₀ u : State} {ml a x r m t : Nat} {top : Option Nat} {M X₀ Sc i : Nat}
    (hx : x < N) (hr : r < N) (hmN : m < N) (ht : t < N) (hrt : r ≠ t) (hmt : m ≠ t)
    (hrm : r ≠ m) (hxr : r ≠ x) (hxt : t ≠ x)
    (h4 : 4 ≤ wq a) (hw : wq a ≤ kw len) (htop : ∀ k, top = some k → wq a + k ≤ kw len)
    (hX : val32 s₀.mem B (arr (kw len) x) (xw len a top) = X₀) (hM : val32 s₀.mem B (arr (kw len) m) (wq a) = M)
    (H : StepHdr s₀.mem B M (wq a)) (hS : Sc = xw len a top - wq a + 1) (hi : i < Sc)
    (I : LoopI L s₀ B Z len N ml a r t M X₀ Sc i u) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.digitStep L ml x r m t) u fun v =>
      LoopI L s₀ B Z len N ml a r t M X₀ Sc (i + 1) v ∧ v.zf = some (decide (i + 1 = Sc)) := by
  have h := I.ws
  have nw := h.ws.workspace.nowrap
  have fx := h.ws.arr_fit (j := x) hx
  have hdr := h.ws.hdr_le
  have hkw := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  simp only [S] at fx
  simp only [VG.Impl.Rsa.X86.Keys.hdr] at hdr
  obtain ⟨hXW, hXk⟩ := xw_le (top := top) hw htop
  have hXw : xw len a top ≤ 2 * kw len := by omega
  have hX4 : arr (kw len) x + 4 * xw len a top ≤ arr (kw len) x + 4 * (kw len + 2) := by omega
  -- What `u` keeps of `s₀`.
  have Xu : val32 u.mem B (arr (kw len) x) (xw len a top) = X₀ := by
    rw [← hX]
    exact keep_x I.keep (by simp; omega) (by decide) (by simp only [S]; omega) (by omega)
  have Mu : val32 u.mem B (arr (kw len) m) (wq a) = M := by
    rw [← hM]
    exact val32_congr fun j hj => I.keep.word (j := m) (i := j) (by simp only [S]; omega)
      (by simp; omega) (by decide) (h.ws.fit64 hmN)
  have Hu : StepHdr u.mem B M (wq a) := H.keep (I.keep.slot (by decide) (by decide))
    (I.keep.slot (by decide) (by decide)) (I.keep.slot (by decide) (by decide))
  have hk : Sc - i - 1 < xw len a top := by omega
  -- The digit.
  unfold VG.Impl.Rsa.X86.WordModRt.digitStep
  simp only [VG.Impl.Rsa.X86.WordModRt.seqs]
  refine WP.seq (arrPtr_ok (lenSrc h) h.lenLe h.edi (r := .ebx) (t := .edx) (j := x) (by decide) (by decide)
    (by omega) fun u₁ K₁ m₁ p₁ _ => ?_)
  have h₁ := h.keep K₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
  have rs := readSrc_sc h₁.ws.workspace (d := oSteps) (by rw [oSteps_val']; omega)
  refine wp_movS rs fun u₂ U₂ _ => wp_subS rfl fun u₃ U₃ _ => wp_addS rfl fun u₄ U₄ _ => wp_addS rfl fun u₅ U₅ _ =>
    wp_addS rfl fun u₆ U₆ _ => ?_
  have e₂ : (u₂.gpr .eax).toNat = Sc - i := by rw [U₂.gpr, m₁]; exact I.steps
  have e₅ : (u₅.gpr .eax).toNat = 4 * (Sc - i - 1) := by
    rw [U₅.gpr, BitVec.toNat_add, U₄.gpr, BitVec.toNat_add, U₃.gpr, BitVec.toNat_sub, e₂,
      show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  have p₆ : PtrAt u₆ B .ebx (arr (kw len) x + 4 * (Sc - i - 1)) := by
    rw [PtrAt, U₆.gpr, BitVec.toNat_add, U₅.other .ebx (by decide), U₄.other .ebx (by decide),
      U₃.other .ebx (by decide), U₂.other .ebx (by decide), p₁, e₅]
    have := B.isLt; omega
  have K₁₆ : Keeps [.eax, .ebx, .edx] u u₆ := (K₁.mono (by decide)).trans
    (((U₂.keeps.mono (by decide)).trans (U₃.keeps.mono (by decide))).trans
      (((U₄.keeps.mono (by decide)).trans (U₅.keeps.mono (by decide))).trans (U₆.keeps.mono (by decide))))
  have m₆ : u₆.mem = u.mem := by rw [U₆.mem, U₅.mem, U₄.mem, U₃.mem, U₂.mem, m₁]
  refine wp_movS (readSrc_ptr (h.rt.of_keeps K₁₆) p₆ (d := 0) (by omega)) fun u₇ U₇ _ => ?_
  have K₁₇ : Keeps [.eax, .ebx, .edx] u u₇ := K₁₆.trans (U₇.keeps.mono (by decide))
  have h₇ := h.keep K₁₇ (by decide) (by decide) (by rw [U₇.mem, m₆]; exact Outside.refl _ _ _ _)
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.storeSlot_ok h₇ (d := oDig) (by decide) .eax) fun u₈ ⟨h₈, k₈, e₈, K₈⟩ => ?_
  have Z₈ := VG.Proof.Rsa.X86.KeyRt.keep_outside h₇.ws k₈ (by simp) (by decide)
  have K₀₈ : Keeps [.eax, .ebx, .edx] u u₈ := K₁₇.trans (K₈.mono (by simp))
  have Zu₈ : Outside B 0 Z u.mem u₈.mem := by rw [U₇.mem, m₆] at Z₈; exact Z₈
  have hm₈ : MLen u₈ B Z ml a := I.ml.keep K₀₈ (by decide) Zu₈
  have k₀₈ : Keep B (kw len) [] [oDig] u.mem u₈.mem := by rw [U₇.mem, m₆] at k₈; exact k₈
  have dig : slot u₈.mem B oDig = X₀ / 2 ^ (32 * (Sc - i - 1)) % 2 ^ 32 := by
    rw [e₈, U₇.gpr, m₆, Nat.add_zero, ← Xu]
    exact w32_of_val32 u.mem B hk
  have R₈ : val32 u₈.mem B (arr (kw len) r) (wq a) = X₀ / 2 ^ (32 * (Sc - i)) % M := by
    rw [← I.val]
    exact val32_congr fun j hj => k₀₈.word (j := r) (i := j) (by simp only [S]; omega) (by simp) (by decide)
      (h.ws.fit64 hr)
  have M₈ : val32 u₈.mem B (arr (kw len) m) (wq a) = M := by
    rw [← Mu]
    exact val32_congr fun j hj => k₀₈.word (j := m) (i := j) (by simp only [S]; omega) (by simp) (by decide)
      (h.ws.fit64 hmN)
  have H₈ : StepHdr u₈.mem B M (wq a) := Hu.keep (k₀₈.slot (by decide) (by decide))
    (k₀₈.slot (by decide) (by decide)) (k₀₈.slot (by decide) (by decide))
  have hM0 : 0 < M := by have := H.dn; rcases Nat.eq_zero_or_pos M with e | e <;> simp_all
  -- The step.
  refine WP.seq (WP.mono (step_ok h₈ hm₈ hr hmN ht hrt hmt h4 hw M₈ R₈ (Nat.mod_lt _ hM0) H₈)
    fun v₁ ⟨hv₁, kv₁, ev₁, sv₁, hiv₁, Kv₁⟩ => ?_)
  rw [dig] at ev₁
  have st : slot v₁.mem B oSteps = Sc - i := by rw [sv₁, k₀₈.slot (by decide) (by decide)]; exact I.steps
  -- The count down.
  refine wp_movS (readSrc_sc hv₁.ws.workspace (d := oSteps) (by rw [oSteps_val']; omega)) fun v₂ V₂ _ =>
    wp_subZ rfl fun v₃ V₃ z₃ => ?_
  have K₁₃ : Keeps [.eax] v₁ v₃ := (V₂.keeps.mono (by decide)).trans (V₃.keeps.mono (by decide))
  have hv₃ := hv₁.keep K₁₃ (by decide) (by decide) (by rw [V₃.mem, V₂.mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (storeSlotZ_ok hv₃ (d := oSteps) (by decide) .eax) fun v ⟨hv, kv, ev, Kv, zv⟩ => ?_
  have e₂' : (v₂.gpr .eax).toNat = Sc - i := by rw [V₂.gpr]; exact st
  have e₃' : (v₃.gpr .eax).toNat = Sc - i - 1 := by
    rw [V₃.gpr, BitVec.toNat_sub, e₂', show (1 : BitVec 32).toNat = 1 from rfl]; omega
  have Kuv : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] u v :=
    (K₀₈.mono (by decide)).trans (Kv₁.trans ((K₁₃.mono (by decide)).trans (Kv.mono (by simp))))
  have kv' : Keep B (kw len) [] [oSteps] v₁.mem v.mem := by rw [V₃.mem, V₂.mem] at kv; exact kv
  have kuv : Keep B (kw len) [r, t] [oMask, oSteps, oQ, oU0, oU2, oDig] u.mem v.mem :=
    ((k₀₈.mono (by simp) (by simp)).trans (kv₁.mono (by simp) (by simp))).trans (kv'.mono (by simp) (by simp))
  have Zuv := VG.Proof.Rsa.X86.KeyRt.keep_outside h.ws kuv (by simp; omega) (by decide)
  refine ⟨⟨hv, I.ml.keep Kuv (by decide) Zuv, I.keep.trans kuv, I.rest.trans Kuv, ?_, ?_, ?_⟩, ?_⟩
  · have ev : val32 v.mem B (arr (kw len) r) (wq a) = val32 v₁.mem B (arr (kw len) r) (wq a) := by
      exact val32_congr fun j hj => kv'.word (j := r) (i := j) (by simp only [S]; omega) (by simp) (by decide)
        (h.ws.fit64 hr)
    rw [ev, ev₁, show Sc - (i + 1) = Sc - i - 1 by omega]
    have e : X₀ / 2 ^ (32 * (Sc - i)) = X₀ / 2 ^ (32 * (Sc - i - 1)) / 2 ^ 32 := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, show 32 * (Sc - i - 1) + 32 = 32 * (Sc - i) by omega]
    rw [e]; exact step_mod
  · intro j hj1 hj2
    rw [mw, kv'.word (j := r) (i := j) (by simp only [S]; omega) (by simp) (by decide) (h.ws.fit64 hr)]
    rw [← mw, hiv₁ j hj1 (by omega), mw, k₀₈.word (j := r) (i := j) (by simp only [S]; omega) (by simp)
      (by decide) (h.ws.fit64 hr)]
    exact I.high j hj1 hj2
  · rw [ev, e₃']; omega
  · rw [zv, z₃]
    congr 1
    have hSb : Sc - i < 2 ^ 32 := by omega
    have hv2 : v₂.gpr .eax = BitVec.ofNat 32 (Sc - i) :=
      BitVec.eq_of_toNat_eq (by rw [e₂', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hSb])
    rw [hv2]
    by_cases e : i + 1 = Sc
    · rw [decide_eq_true e, beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hSb]; simp; omega
    · rw [decide_eq_false e, beq_eq_false_iff_ne]
      intro hc
      have := congrArg BitVec.toNat hc
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hSb] at this; simp at this; omega


/-- A number of `n + 1` words below `2^(32 n)`: its top word is zero, and so the words above. -/
theorem val32_word_zero {m : Mem} {d n k j : Nat} (hk : k < n) (hj : j ≤ k) (h : val32 m B d n < 2 ^ (32 * j)) :
    w32 m B (d + 4 * k) = 0 := by
  rw [w32_of_val32 m B hk, Nat.div_eq_of_lt (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))]

theorem val32_zero_of {m : Mem} {d : Nat} : ∀ {n : Nat}, (∀ j < n, w32 m B (d + 4 * j) = 0) → val32 m B d n = 0
  | 0, _ => rfl
  | n + 1, h => by rw [val32_succ, val32_zero_of fun j hj => h j (by omega), h n (by omega)]; rfl

/-- `wordMod`'s start: `orTop`, `recip` and `seed`, to the loop's invariant. -/
theorem wordModPre_ok {s : State} (h : RtWs L s B Z len N) {ml a x r m t : Nat} {top : Option Nat}
    (hm : MLen s B Z ml a) (hx : x < N) (hr : r < N) (hmN : m < N)
    (hrm : r ≠ m) (hxr : r ≠ x) (hxm : m ≠ x)
    (h4 : 4 ≤ wq a) (hw : wq a ≤ kw len) (htop : ∀ k, top = some k → wq a + k ≤ kw len) :
    WP isa (.seq (.seq (.block (VG.Impl.Rsa.X86.WordModRt.orTop L ml m)) (VG.Impl.Rsa.X86.WordModRt.recip L))
      (VG.Impl.Rsa.X86.WordModRt.seed L ml x r top)) s fun u => ∃ Mn X₀,
      X₀ = val32 s.mem B (arr (kw len) x) (xw len a top) ∧ val32 u.mem B (arr (kw len) x) (xw len a top) = X₀ ∧
      val32 u.mem B (arr (kw len) m) (wq a) = Mn ∧ StepHdr u.mem B Mn (wq a) ∧
      LoopI L u B Z len N ml a r t Mn X₀ (xw len a top - wq a + 1) 0 u ∧
      Keep B (kw len) [m, r] [oD, oD1, oV, oSteps] s.mem u.mem ∧
      (∀ i, i < kw len + 2 → i ≠ wq a - 1 → mw u.mem B (kw len) m i = mw s.mem B (kw len) m i) ∧
      mw u.mem B (kw len) m (wq a - 1) = mw s.mem B (kw len) m (wq a - 1) % 2 ^ 31 + 2 ^ 31 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s u := by
  have nw := h.ws.workspace.nowrap
  have hkw := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  obtain ⟨hXW, hXk⟩ := xw_le (top := top) hw htop
  have hXw : xw len a top ≤ 2 * kw len := by omega
  have fx := h.ws.arr_fit (j := x) hx
  simp only [S] at fx
  -- The divisor's top bit, `d`, `d₁` and `v`.
  refine WP.seq (WP.seq (WP.mono (orTop_ok h hm hmN (by omega) hw) fun u₁ ⟨h₁, k₁, w₁, t₁, d₁, d1₁, K₁⟩ => ?_))
  obtain ⟨Mn, hMn⟩ : ∃ Mn, Mn = val32 u₁.mem B (arr (kw len) m) (wq a) := ⟨_, rfl⟩
  have hMsplit : Mn = val32 u₁.mem B (arr (kw len) m) (wq a - 1) +
      2 ^ (32 * (wq a - 1)) * mw u₁.mem B (kw len) m (wq a - 1) := by
    rw [hMn, show wq a = wq a - 1 + 1 by omega, val32_succ, Nat.add_sub_cancel]
  have hmw : mw u₁.mem B (kw len) m (wq a - 1) < 2 ^ 32 := (u₁.mem.readW _ 32).isLt
  have hdiv : Mn / 2 ^ (32 * (wq a - 1)) = mw u₁.mem B (kw len) m (wq a - 1) := by
    rw [hMsplit, Nat.add_comm, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt (val32_lt _ _ _ _),
      Nat.add_zero]
  have hdn : 2 ^ 31 ≤ Mn / 2 ^ (32 * (wq a - 1)) := by rw [hdiv, t₁]; omega
  refine (WP.mono (recip_ok h₁ (d := Mn / 2 ^ (32 * (wq a - 1))) (by rw [hdiv]; exact d₁) hdn
    (by rw [hdiv]; exact hmw)) fun u₂ ⟨h₂, k₂, v₂, K₂⟩ => ?_)
  have Hd : StepHdr u₂.mem B Mn (wq a) := by
    refine ⟨?_, hdn, ?_, v₂, by rw [hMn]; exact val32_lt _ _ _ _⟩
    · rw [k₂.slot (by decide) (by decide), d₁, hdiv]
    · rw [k₂.slot (by decide) (by decide), d1₁, ← w₁ (wq a - 2) (by omega) (by omega), hMn]
      exact w32_of_val32 u₁.mem B (by omega)
  have K₀₂ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₂ := (K₁.mono (by decide)).trans K₂
  have k₀₂ : Keep B (kw len) [m] [oD, oD1, oV] s.mem u₂.mem :=
    (k₁.mono (by simp) (by simp)).trans (k₂.mono (by simp) (by simp))
  have Z₀₂ := VG.Proof.Rsa.X86.KeyRt.keep_outside h.ws k₀₂ (by simpa using hmN) (by decide)
  have hm₂ : MLen u₂ B Z ml a := hm.keep K₀₂ (by decide) Z₀₂
  -- `r` seeded with the dividend's top words.
  refine WP.mono (seed_ok h₂ hm₂ hx hr hxr htop (by omega) hw) fun u₃ ⟨h₃, k₃, v₃, st₃, K₃⟩ => ?_
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, X₀ = val32 s.mem B (arr (kw len) x) (xw len a top) := ⟨_, rfl⟩
  have fitx : arr (kw len) x + 4 * (kw len + 2) ≤ 2 ^ 64 := by omega
  have X₂ : val32 u₂.mem B (arr (kw len) x) (xw len a top) = X₀ := by
    rw [hX₀]; exact keep_x k₀₂ (by simpa using hxm.symm) (by decide)
      (by simp only [S]; omega) (by omega)
  have X₃ : val32 u₃.mem B (arr (kw len) x) (xw len a top) = X₀ := by
    rw [← X₂]; exact keep_x k₃ (by simpa using hxr.symm) (by decide)
      (by simp only [S]; omega) (by omega)
  have M₃ : val32 u₃.mem B (arr (kw len) m) (wq a) = Mn := by
    rw [hMn]
    exact val32_congr fun j hj => ((k₂.mono (js' := [r]) (ds' := [oV, oSteps]) (by simp) (by simp)).trans
      (k₃.mono (by simp) (by simp))).word (j := m) (i := j) (by simp only [S]; omega) (by simpa using hrm)
      (by decide) (h.ws.fit64 hmN)
  have H₃ : StepHdr u₃.mem B Mn (wq a) := Hd.keep (k₃.slot (by decide) (by decide))
    (k₃.slot (by decide) (by decide)) (k₃.slot (by decide) (by decide))
  have hXlt : X₀ < 2 ^ (32 * xw len a top) := by rw [hX₀]; exact val32_lt _ _ _ _
  have hseed : val32 u₃.mem B (arr (kw len) r) (kw len + 1) < 2 ^ (32 * (wq a - 1)) := by
    rw [v₃, X₂, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
      show 32 * (wq a - 1) + 32 * (xw len a top - (wq a - 1)) = 32 * xw len a top by omega]
    exact hXlt
  have hMlow : 2 ^ (32 * (wq a - 1)) ≤ Mn := by
    rw [hMsplit, t₁]
    have := Nat.mul_le_mul_left (2 ^ (32 * (wq a - 1))) (show 1 ≤ mw s.mem B (kw len) m (wq a - 1) % 2 ^ 31 + 2 ^ 31 by omega)
    omega
  have hz : ∀ j, wq a - 1 ≤ j → j < kw len + 1 → w32 u₃.mem B (arr (kw len) r + 4 * j) = 0 :=
    fun j h1 h2 => val32_word_zero (n := kw len + 1) h2 h1 hseed
  have hr0 : val32 u₃.mem B (arr (kw len) r) (wq a) = val32 u₃.mem B (arr (kw len) r) (kw len + 1) := by
    rw [show kw len + 1 = wq a + (kw len + 1 - wq a) by omega, val32_append,
      val32_zero_of (n := kw len + 1 - wq a) fun j hj => by
        rw [show arr (kw len) r + 4 * wq a + 4 * j = arr (kw len) r + 4 * (wq a + j) by omega]
        exact hz _ (by omega) (by omega),
      Nat.mul_zero, Nat.add_zero]
  obtain ⟨Sc, hSc⟩ : ∃ Sc, Sc = xw len a top - wq a + 1 := ⟨_, rfl⟩
  have I₀ : LoopI L u₃ B Z len N ml a r t Mn X₀ Sc 0 u₃ := by
    refine ⟨h₃, hm₂.keep K₃ (by decide) (VG.Proof.Rsa.X86.KeyRt.keep_outside h₂.ws k₃ (by simpa using hr)
      (by decide)), Keep.refl _ _ _ _ _, Keeps.refl _ _, ?_, ?_, ?_⟩
    · rw [hr0, Nat.sub_zero, show Sc = xw len a top - (wq a - 1) by omega, ← X₂, ← v₃,
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hseed hMlow)]
    · intro j hj1 hj2; exact hz j (by omega) hj2
    · rw [st₃, hSc, Nat.sub_zero]
  refine ⟨Mn, X₀, hX₀, X₃, M₃, H₃, by rw [← hSc]; exact I₀,
    (k₀₂.mono (by simp) (by simp)).trans (k₃.mono (by simp) (by simp)), fun i hi hne => ?_, ?_,
    (K₀₂.mono (by decide)).trans (K₃.mono (by decide))⟩
  · rw [mw, ((k₂.mono (js' := [r]) (ds' := [oV, oSteps]) (by simp) (by simp)).trans
      (k₃.mono (by simp) (by simp))).word (j := m) (i := i) (by simp only [S]; omega) (by simpa using hrm)
      (by decide) (h.ws.fit64 hmN)]
    exact w₁ i hi hne
  · rw [mw, ((k₂.mono (js' := [r]) (ds' := [oV, oSteps]) (by simp) (by simp)).trans
      (k₃.mono (by simp) (by simp))).word (j := m) (i := wq a - 1) (by simp only [S]; omega) (by simpa using hrm)
      (by decide) (h.ws.fit64 hmN)]
    exact t₁

/-- `wordMod ml x r m t top`: `r = x mod m'` for the dividend `x` (`X` words) and `m'` the
divisor's `W'` words with the top bit of its word `W' - 1` set, written back to `m`. -/
theorem wordMod_ok {s : State} (h : RtWs L s B Z len N) {ml a x r m t : Nat} {top : Option Nat}
    (hm : MLen s B Z ml a) (hx : x < N) (hr : r < N) (hmN : m < N) (ht : t < N)
    (hrt : r ≠ t) (hmt : m ≠ t) (hrm : r ≠ m) (hxr : r ≠ x) (hxt : t ≠ x) (hxm : m ≠ x)
    (h4 : 4 ≤ wq a) (hw : wq a ≤ kw len) (htop : ∀ k, top = some k → wq a + k ≤ kw len) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.wordMod L ml x r m t top) s fun v => RtWs L v B Z len N ∧
      Keep B (kw len) [m, r, t] [oD, oD1, oV, oMask, oSteps, oQ, oU0, oU2, oDig] s.mem v.mem ∧
      (∀ i, i < kw len + 2 → i ≠ wq a - 1 → mw v.mem B (kw len) m i = mw s.mem B (kw len) m i) ∧
      mw v.mem B (kw len) m (wq a - 1) = mw s.mem B (kw len) m (wq a - 1) % 2 ^ 31 + 2 ^ 31 ∧
      num v.mem B (kw len) r =
        val32 s.mem B (arr (kw len) x) (xw len a top) % val32 v.mem B (arr (kw len) m) (wq a) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s v := by
  have nw := h.ws.workspace.nowrap
  have hkw := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  obtain ⟨hXW, hXk⟩ := xw_le (top := top) hw htop
  have hXw : xw len a top ≤ 2 * kw len := by omega
  have fx := h.ws.arr_fit (j := x) hx
  simp only [S] at fx
  unfold VG.Impl.Rsa.X86.WordModRt.wordMod
  simp only [VG.Impl.Rsa.X86.WordModRt.seqs]
  refine WP.assoc (WP.assoc (WP.seq (WP.mono (wordModPre_ok (t := t) h hm hx hr hmN hrm hxr hxm h4 hw htop) fun u₃ ⟨Mn, X₀, hX₀, X₃, M₃, H₃, I₀, k₀₃, w₃, t₃, K₀₃⟩ => ?_)))
  obtain ⟨Sc, hSc⟩ : ∃ Sc, Sc = xw len a top - wq a + 1 := ⟨_, rfl⟩
  rw [← hSc] at I₀
  -- The steps.
  have fitr := h.ws.fit64 hr
  have fitm := h.ws.fit64 hmN
  refine WP.loop (M := isa) (fun n u => ∃ i, n = Sc - i ∧ i < Sc ∧ LoopI L u₃ B Z len N ml a r t Mn X₀ Sc i u)
    ?_ Sc u₃ ⟨0, by omega, by omega, I₀⟩
  rintro n u ⟨i, rfl, hi, I⟩
  refine WP.mono (digitStep_ok hx hr hmN ht hrt hmt hrm hxr hxt h4 hw htop X₃ M₃ H₃ hSc hi I)
    fun v ⟨I', z⟩ => ?_
  have km : ∀ j, j < kw len + 2 → mw v.mem B (kw len) m j = mw u₃.mem B (kw len) m j := fun j hj =>
    I'.keep.word (j := m) (i := j) (by simp only [S]; omega) (by simp; omega) (by decide) fitm
  by_cases e : i + 1 = Sc
  · refine .inl ⟨by simp only [eval, z, e, decide_true, Option.map_some, Bool.not_true], I'.ws, ?_, ?_, ?_, ?_,
      K₀₃.trans I'.rest⟩
    · exact (k₀₃.mono (by simp) (by simp)).trans (I'.keep.mono (by simp) (by simp))
    · intro j hj hne
      rw [km j hj]; exact w₃ j hj hne
    · rw [km _ (by omega)]; exact t₃
    · have Mv : val32 v.mem B (arr (kw len) m) (wq a) = Mn := by
        rw [← M₃]
        exact val32_congr fun j hj => km j (by omega)
      rw [Mv, VG.Proof.Rsa.X86.Keys.num, show kw len = wq a + (kw len - wq a) by omega, val32_append,
        val32_zero_of (n := kw len - wq a) fun j hj => by
          rw [show arr (wq a + (kw len - wq a)) r + 4 * wq a + 4 * j = arr (wq a + (kw len - wq a)) r + 4 * (wq a + j)
            by omega]
          have := I'.high (wq a + j) (by omega) (by omega)
          rw [mw, show wq a + (kw len - wq a) = kw len by omega] at *
          exact this,
        Nat.mul_zero, Nat.add_zero, show wq a + (kw len - wq a) = kw len by omega, I'.val, e, Nat.sub_self,
        Nat.mul_zero, Nat.pow_zero, Nat.div_one, hX₀]
  · exact .inr ⟨by simp only [eval, z, e, decide_false, Option.map_some, Bool.not_false], Sc - (i + 1), by omega,
      i + 1, rfl, by omega, I'⟩

/-- `X` has `k` words, the top bit of the top one set. -/
def Top (k X : Nat) : Prop := 2 ^ (32 * k - 1) ≤ X ∧ X < 2 ^ (32 * k)

/-- The low `k` words of a number below `2^(32 k)`: the number. -/
theorem val32_low {m : Mem} {B : Addr} {d w k : Nat} (hk : k ≤ w) (hl : val32 m B d w < 2 ^ (32 * k)) :
    val32 m B d k = val32 m B d w := by
  have e := val32_append m B d k (w - k)
  rw [show k + (w - k) = w by omega] at e
  generalize val32 m B (d + 4 * k) (w - k) = R at e
  rcases Nat.eq_zero_or_pos R with h0 | hp
  · rw [h0, Nat.mul_zero, Nat.add_zero] at e; exact e.symm
  · have : 2 ^ (32 * k) * 1 ≤ 2 ^ (32 * k) * R := Nat.mul_le_mul_left _ hp
    omega

/-- The top word of a number of `k` words: whether it is at least `2^(32 k - 1)`. -/
theorem top_iff {m : Mem} {B : Addr} {d k : Nat} (hk : 0 < k) :
    2 ^ 31 ≤ w32 m B (d + 4 * (k - 1)) ↔ 2 ^ (32 * k - 1) ≤ val32 m B d k := by
  have e := val32_succ m B d (k - 1)
  rw [show k - 1 + 1 = k by omega] at e
  have lo := val32_lt m B d (k - 1)
  have hp : 2 ^ (32 * k - 1) = 2 ^ (32 * (k - 1)) * 2 ^ 31 := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hp, e]
  generalize w32 m B (d + 4 * (k - 1)) = T
  generalize val32 m B d (k - 1) = L at lo ⊢
  generalize (2 : Nat) ^ (32 * (k - 1)) = P at lo ⊢
  constructor
  · intro hT
    calc P * 2 ^ 31 ≤ P * T := Nat.mul_le_mul_left _ hT
      _ ≤ L + P * T := Nat.le_add_left _ _
  · intro hT
    refine Nat.le_of_not_lt fun hlt => ?_
    have : P * T + P ≤ P * 2 ^ 31 := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
    omega

/-- `wordMod`: where the divisor's top bit is already set, the divisor left as it was and the
remainder. -/
theorem wordMod_cond_ok {s : State} (h : RtWs L s B Z len N) {ml a x r m t : Nat} {top : Option Nat}
    (hm : MLen s B Z ml a) (hx : x < N) (hr : r < N) (hmN : m < N) (ht : t < N)
    (hrt : r ≠ t) (hmt : m ≠ t) (hrm : r ≠ m) (hxr : r ≠ x) (hxt : t ≠ x) (hxm : m ≠ x)
    (h4 : 4 ≤ wq a) (hw : wq a ≤ kw len) (htop : ∀ k, top = some k → wq a + k ≤ kw len) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.wordMod L ml x r m t top) s fun v => RtWs L v B Z len N ∧
      Keep B (kw len) [m, r, t] [oD, oD1, oV, oMask, oSteps, oQ, oU0, oU2, oDig] s.mem v.mem ∧
      (Top (wq a) (num s.mem B (kw len) m) → num v.mem B (kw len) m = num s.mem B (kw len) m ∧
        num v.mem B (kw len) r = val32 s.mem B (arr (kw len) x) (xw len a top) % num s.mem B (kw len) m) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s v := by
  refine WP.mono (wordMod_ok h hm hx hr hmN ht hrt hmt hrm hxr hxt hxm h4 hw htop)
    fun v ⟨hv, k, wk, wtop, wr, K⟩ => ⟨hv, k, fun top => ?_, K⟩
  obtain ⟨lo, hi⟩ := top
  have hpos : 0 < wq a := by omega
  have low : val32 s.mem B (arr (kw len) m) (wq a) = num s.mem B (kw len) m := val32_low hw hi
  have topw : 2 ^ 31 ≤ mw s.mem B (kw len) m (wq a - 1) := (top_iff hpos).mpr (by rw [low]; exact lo)
  have tlt : mw s.mem B (kw len) m (wq a - 1) < 2 ^ 32 := (s.mem.readW _ 32).isLt
  have same : ∀ i, i < kw len + 2 → mw v.mem B (kw len) m i = mw s.mem B (kw len) m i := fun i hi' => by
    by_cases e : i = wq a - 1
    · subst e
      have key : ∀ T : Nat, 2 ^ 31 ≤ T → T < 2 ^ 32 → T % 2 ^ 31 + 2 ^ 31 = T := fun T a b => by omega
      rw [wtop]; exact key _ topw tlt
    · exact wk i hi' e
  have numEq : ∀ n, n ≤ kw len → val32 v.mem B (arr (kw len) m) n = val32 s.mem B (arr (kw len) m) n :=
    fun n hn => val32_congr (k := n) fun i (hi' : i < n) => same i (by omega)
  exact ⟨numEq _ (Nat.le_refl _), by rw [wr, numEq _ hw, low]⟩

end VG.Proof.Rsa.X86.WordRt
