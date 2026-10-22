module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Product
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Prepare
import VerifiedGarbage.Proof.Framework.Omega

/-! # The acceptance of the key and the input

`validate_ok`: the mask at `accOff` all ones exactly when `p q = n`, the
input is below `n` and `qInv` below `p`, for the numbers in the wide slots 9
(`n`, `2 B` bytes), 10 (`p`), 11 (`q`), 14 (`qInv`) and 15 (the input).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

/-- The ranges the acceptance changes. -/
abbrev valR (len : Nat) : List (Nat × Nat) :=
  [(accOff, 4), (multOff, 4), (prodOff, 2 * bc len .wide + 4), (mulAOff, bc len .wide)]

/-- The low `a` words of a number below `2^(32 a)` are the number. -/
theorem val32_low {m : Mem} {base : Addr} {d a b v : Nat} (h : val32 m base d (a + b) = v)
    (hv : v < 2 ^ (32 * a)) : val32 m base d a = v := by
  rw [val32_append] at h
  have hl := val32_lt m base d a
  have : val32 m base (d + 4 * a) b = 0 := by
    by_contra hne
    have : 2 ^ (32 * a) ≤ 2 ^ (32 * a) * val32 m base (d + 4 * a) b := Nat.le_mul_of_pos_right _ (by omega)
    omega
  rw [this, Nat.mul_zero, Nat.add_zero] at h
  exact h

/-- A number of `a` words zero-extended to `a + b`. -/
theorem val32_ext {m : Mem} {base : Addr} {d a b : Nat} (h : val32 m base (d + 4 * a) b = 0) :
    val32 m base d (a + b) = val32 m base d a := by
  rw [val32_append, h, Nat.mul_zero, Nat.add_zero]

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- `ecx` and-ed into the mask at `accOff`. -/
theorem accept_ok (h : In Ex base bytes len args s) {a c : Bool} (ha : w32 s.mem base accOff = (cmask a).toNat)
    (hc : s.gpr .ecx = cmask c) :
    WP isa (.block accept) s fun u => Outside base accOff 4 s.mem u.mem ∧
      w32 u.mem base accOff = (cmask (a && c)).toNat ∧ Keeps [.eax] s u := by
  have nb := h.need
  have ao : accOff = 8 := rfl
  have nbs : numBase = 3336 := rfl
  unfold CrtRt.need at nb
  unfold accept
  refine wp_movS (readSrc_sc h.scratch (d := accOff) (by omega)) fun u₁ a₁ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun u₂ a₂ => ?_
  have K₂ : Keeps [.eax] s u₂ := a₁.keeps.trans a₂.keeps
  have h₂ := h.regs K₂ (by rw [a₂.mem, a₁.mem])
  refine wp_storeS (h₂.scratch.ea (d := accOff) (by omega)) (h₂.scratch.write (d := accOff) (n := 4)
    (by omega)) fun u₃ m₃ => WP.block_nil ⟨?_, ?_, K₂.trans (m₃.keeps _)⟩
  · rw [m₃.mem, a₂.mem, a₁.mem]; exact writeW32_outside _ _ _ (by omega)
  · have e : s.mem.readW (off base accOff) 32 = cmask a := BitVec.eq_of_toNat_eq ha
    rw [m₃.mem, w32_write_self, a₂.gpr]
    simp only [ite_true]
    rw [a₁.gpr, a₁.other .ecx (by decide), hc, e, cmask_and]

theorem valR_fit (h : In Ex base bytes len args s) : ∀ p ∈ valR len, p.1 + p.2 ≤ bytes := by
  have pf := h.prod_fit
  intro p hp; simp only [valR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> simp only [accOff, multOff, prodOff, mulAOff, numBase] at * <;> omega

/-- The acceptance keeps everything from the slots up. -/
theorem valR_keep (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (valR len)) m m') (R : CallRoom sp base bytes) {d k : Nat} (hd : numBase ≤ d)
    (hk : d + 4 * k ≤ bytes) : val32 m' base d k = val32 m base d k := by
  have pf := h.prod_fit
  refine frameR_val32 F R h.scratch.nowrap hk ?_ (valR_fit h)
  intro p hp; simp only [valR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> simp only [accOff, multOff, prodOff, mulAOff, numBase] at * <;> omega

theorem validate_ok (h : In Ex base bytes len args s) {n p q x qi : Nat}
    (hn : val32 s.mem base (lo len (.slot .wide 9)) (2 * cwc len .wide) = n) (hnb : n < 2 ^ (32 * cwc len .wide))
    (hp : val32 s.mem base (lo len (.slot .wide 10)) (cwc len .wide) = p)
    (hq : val32 s.mem base (lo len (.slot .wide 11)) (cwc len .wide) = q)
    (hqi : val32 s.mem base (lo len (.slot .wide 14)) (cwc len .wide) = qi)
    (hx : val32 s.mem base (lo len (.slot .wide 15)) (cwc len .wide) = x) :
    WP isa validate s fun u =>
      Frame (frameR base (s.gpr .esp) (valR len)) s.mem u.mem ∧
      w32 u.mem base accOff = (cmask (decide (p * q = n ∧ x < n ∧ qi < p))).toNat ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have pf := h.prod_fit
  have bw := bc_eq_cwc len .wide
  have g := bc_ge h.lower' .wide
  have nw := h.scratch.nowrap
  have f17 := h.slot_fit .wide (j := 17) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e10 : lo len (.slot .wide 10) = numBase + 10 * st len .wide := rfl
  have e11 : lo len (.slot .wide 11) = numBase + 11 * st len .wide := rfl
  have e14 : lo len (.slot .wide 14) = numBase + 14 * st len .wide := rfl
  have e15 : lo len (.slot .wide 15) = numBase + 15 * st len .wide := rfl
  have e17 : lo len (.slot .wide 17) = numBase + 17 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  have ao : accOff = 8 := rfl
  have cb1 : cb len (one .wide) = bc len .wide := by simp [cb, one]
  have cw1 : cw len (one .wide) = cwc len .wide := by simp [cw, cwc, cb, one]
  have cb2 : cb len (two .wide) = 2 * bc len .wide := by simp [cb, two]
  have cw2 : cw len (two .wide) = 2 * cwc len .wide := by
    have := bc_dvd len .wide; simp [cw, cb, two, cwc]; omega
  have ma : mulAOff = 2312 := rfl
  have po : prodOff = 256 := rfl
  have fitV := valR_fit h
  let cn := cwc len .wide
  -- `n`'s low half is `n`.
  have nlo : val32 s.mem base (lo len (.slot .wide 9)) cn = n :=
    val32_low (b := cn) (by rw [show cn + cn = 2 * cwc len .wide by omega]; exact hn) hnb
  unfold validate
  -- `p` into the multiplicand, and `p q`.
  refine WP.seq (WP.mono (copy_ok h (x := .slot .wide 10) (d := mulA) (one_ok .wide) (by rw [cb1]; omega)
    (by rw [cb1]; simp only [mulA, lo]; omega) (by rw [cb1]; simp only [mulA, lo]; exact .inl (by omega)))
    fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  simp only [mulA, lo, cb1, cw1] at O₁ V₁
  rw [show numBase + 10 * st len .wide = lo len (.slot .wide 10) from rfl, hp] at V₁
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega))
  have k₁ : ∀ {d k}, numBase ≤ d → d + 4 * k ≤ bytes → val32 u₁.mem base d k = val32 s.mem base d k :=
    fun hd hk => O₁.val32 (.inr (by omega_using [pf.2.1, hd])) (by omega_using [hk, h.bytes_lt])
  refine WP.seq (WP.mono (wideProduct_ok h₁ (b := .slot .wide 11) (by omega) (by simp only [lo]; omega))
    fun u₂ ⟨F₂, V₂, K₂⟩ => ?_)
  rw [V₁, k₁ (d := lo len (.slot .wide 11)) (k := cwc len .wide) (by omega) (by omega), hq] at V₂
  have h₂ := h₁.keepF K₂ (by decide) (by decide) F₂ (prodR_fit h₁)
  have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  rw [sp₁] at F₂
  have k₂ : ∀ {d k}, numBase ≤ d → d + 4 * k ≤ bytes → val32 u₂.mem base d k = val32 s.mem base d k :=
    fun hd hk => (prodR_keep h₁ F₂ (sp₁ ▸ h₁.room) (by omega) hk).trans (k₁ hd hk)
  -- `p q = n`.
  have pq : val32 u₂.mem base prodOff (2 * cn) = p * q := by
    have sp := val32_succ u₂.mem base prodOff (2 * cn)
    rw [V₂] at sp
    have hl := val32_lt u₂.mem base prodOff (2 * cn)
    have hpq : p * q < 2 ^ (32 * (2 * cn)) := by
      have := val32_lt s.mem base (lo len (.slot .wide 10)) cn
      have := val32_lt s.mem base (lo len (.slot .wide 11)) cn
      rw [hp] at *; rw [hq] at *
      rw [show 32 * (2 * cn) = 32 * cn + 32 * cn by omega, Nat.pow_add]
      exact Nat.mul_lt_mul'' (by assumption) (by assumption)
    have : w32 u₂.mem base (prodOff + 4 * (2 * cn)) = 0 := by
      by_contra hne
      have : 2 ^ (32 * (2 * cn)) ≤ 2 ^ (32 * (2 * cn)) * w32 u₂.mem base (prodOff + 4 * (2 * cn)) :=
        Nat.le_mul_of_pos_right _ (by omega)
      omega
    rw [this, Nat.mul_zero, Nat.add_zero] at sp
    exact sp.symm
  refine WP.seq (WP.mono (equal_ok h₂ (a := prod) (b := .slot .wide 9) (two_ok .wide)
    (by rw [cb2]; simp only [prod, lo]; omega_using [pf.1, pf.2.1, pf.2.2]) (by rw [cb2]; omega)) fun u₃ ⟨M₃, C₃, K₃⟩ => ?_)
  simp only [prod, lo, cw2] at C₃
  rw [show numBase + 9 * st len .wide = lo len (.slot .wide 9) from rfl, k₂ (d := lo len (.slot .wide 9)) (k := 2 * cwc len .wide) (by omega) (by omega), hn,
    show 2 * cwc len .wide = 2 * cn from rfl, pq] at C₃
  have h₃ := h₂.regs K₃ M₃
  -- The mask stored.
  refine WP.seq (wp_storeS (h₃.scratch.ea (d := accOff) (by omega))
    (h₃.scratch.write (d := accOff) (n := 4) (by omega)) fun u₄ m₄ => WP.block_nil ?_)
  have O₄ : Outside base accOff 4 u₃.mem u₄.mem := by rw [m₄.mem]; exact writeW32_outside _ _ _ (by omega)
  have A₄ : w32 u₄.mem base accOff = (cmask (decide (p * q = n))).toNat := by
    rw [m₄.mem, w32_write_self, C₃]
  have h₄ := h₃.keep (m₄.keeps []) (by decide) (by decide) (O₄.mono (Nat.zero_le _) (by omega))
  have k₄ : ∀ {d k}, numBase ≤ d → d + 4 * k ≤ bytes → val32 u₄.mem base d k = val32 s.mem base d k :=
    fun hd hk => by rw [O₄.val32 (.inr (by omega)) (by omega), M₃]; exact k₂ hd hk
  -- The input below `n`.
  refine WP.seq (WP.mono (lessThan_ok h₄ (a := .slot .wide 15) (b := .slot .wide 9) (one_ok .wide)
    (by rw [cb1]; omega) (by rw [cb1]; omega)) fun u₅ ⟨M₅, C₅, K₅⟩ => ?_)
  rw [cw1, k₄ (d := lo len (.slot .wide 15)) (k := cwc len .wide) (by omega) (by omega),
    k₄ (d := lo len (.slot .wide 9)) (k := cwc len .wide) (by omega) (by omega), hx, nlo] at C₅
  have h₅ := h₄.regs K₅ M₅
  refine WP.seq (WP.mono (accept_ok h₅ (a := decide (p * q = n)) (by rw [M₅]; exact A₄) C₅) fun u₆ ⟨O₆, A₆, K₆⟩ => ?_)
  have h₆ := h₅.keep K₆ (by decide) (by decide) (O₆.mono (Nat.zero_le _) (by omega))
  have k₆ : ∀ {d k}, numBase ≤ d → d + 4 * k ≤ bytes → val32 u₆.mem base d k = val32 s.mem base d k :=
    fun hd hk => by rw [O₆.val32 (.inr (by omega)) (by omega), M₅]; exact k₄ hd hk
  -- `qInv` below `p`.
  refine WP.seq (WP.mono (lessThan_ok h₆ (a := .slot .wide 14) (b := .slot .wide 10) (one_ok .wide)
    (by rw [cb1]; omega) (by rw [cb1]; omega)) fun u₇ ⟨M₇, C₇, K₇⟩ => ?_)
  rw [cw1, k₆ (d := lo len (.slot .wide 14)) (k := cwc len .wide) (by omega) (by omega),
    k₆ (d := lo len (.slot .wide 10)) (k := cwc len .wide) (by omega) (by omega), hqi, hp] at C₇
  have h₇ := h₆.regs K₇ M₇
  refine WP.mono (accept_ok h₇ (a := decide (p * q = n) && decide (x < n)) (by rw [M₇]; exact A₆) C₇) fun u ⟨O₈, A₈, K₈⟩ => ⟨?_, ?_, ?_⟩
  · have sp₂ : u₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
    have F₁ : Frame (frameR base (s.gpr .esp) (valR len)) s.mem u₁.mem :=
      frameR_of_outside O₁ (by omega) (by simp)
    have F₂' : Frame (frameR base (s.gpr .esp) (valR len)) u₁.mem u₂.mem :=
      frameR_mono F₂ fun p hp => by
        simp only [prodR, List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> simp
    have F₄ : Frame (frameR base (s.gpr .esp) (valR len)) u₂.mem u₄.mem := by
      rw [← M₃]; exact frameR_of_outside O₄ (by omega) (by simp)
    have F₆ : Frame (frameR base (s.gpr .esp) (valR len)) u₄.mem u₆.mem := by
      rw [← M₅]; exact frameR_of_outside O₆ (by omega) (by simp)
    have F₈ : Frame (frameR base (s.gpr .esp) (valR len)) u₆.mem u.mem := by
      rw [← M₇]; exact frameR_of_outside O₈ (by omega) (by simp)
    exact (((F₁.trans F₂').trans F₄).trans F₆).trans F₈
  · rw [A₈]; congr 2; simp only [Bool.and_assoc, Bool.decide_and]
  · exact ((((((K₁.mono (by decide)).trans K₂).trans K₃).trans ((m₄.keeps []).mono (by decide))).trans
      ((K₅.trans (K₆.mono (by decide))).mono (by decide))).trans
      ((K₇.trans (K₈.mono (by decide))).mono (by decide)))

end

end VG.Proof.Bignum.X86.CrtRt
