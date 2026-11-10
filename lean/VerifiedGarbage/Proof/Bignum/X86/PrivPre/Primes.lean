module

public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Prime
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Validate
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Import
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedRt.Key
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # An RSA private key's precomputed values on x86: the factors' values

`pqCheck_ok`: the mask at `accOff` all ones exactly when `p q = n` (as the
first half of `CrtRt.validate`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrivPre

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Impl.Bignum.X86.PrivPre (pqCheck setLen primesBody check factor)
open VG.Proof.Bignum.X86.Crt (componentValue componentArguments)

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

theorem pqCheck_ok (h : In Ex base bytes len args s) {n p q : Nat}
    (hn : val32 s.mem base (lo len (.slot .wide 9)) (2 * cwc len .wide) = n)
    (hp : val32 s.mem base (lo len (.slot .wide 10)) (cwc len .wide) = p)
    (hq : val32 s.mem base (lo len (.slot .wide 11)) (cwc len .wide) = q) :
    WP isa pqCheck s fun u =>
      Frame (frameR base (s.gpr .esp) (valR len)) s.mem u.mem ∧
      w32 u.mem base accOff = (cmask (decide (p * q = n))).toNat ∧
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
    have := bc_dvd len .wide; simp [cw, cb, two, cwc]; omega_arith
  have ma : mulAOff = 2312 := rfl
  have po : prodOff = 256 := rfl
  have fitV := valR_fit h
  let cn := cwc len .wide
  unfold pqCheck
  -- `p` into the multiplicand, and `p q`.
  refine WP.seq (WP.mono (copy_ok h (x := .slot .wide 10) (d := mulA) (one_ok .wide) (by rw [cb1]; omega_arith)
    (by rw [cb1]; simp only [mulA, lo]; omega_arith) (by rw [cb1]; simp only [mulA, lo]; exact .inl (by omega_arith)))
    fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  simp only [mulA, lo, cb1, cw1] at O₁ V₁
  rw [show numBase + 10 * st len .wide = lo len (.slot .wide 10) from rfl, hp] at V₁
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega_arith))
  have k₁ : ∀ {d k}, numBase ≤ d → d + 4 * k ≤ bytes → val32 u₁.mem base d k = val32 s.mem base d k :=
    fun hd hk => O₁.val32 (.inr (by omega_using [pf.2.1, hd])) (by omega_using [hk, h.bytes_lt])
  refine WP.seq (WP.mono (wideProduct_ok h₁ (b := .slot .wide 11) (by omega_arith) (by simp only [lo]; omega_arith))
    fun u₂ ⟨F₂, V₂, K₂⟩ => ?_)
  rw [V₁, k₁ (d := lo len (.slot .wide 11)) (k := cwc len .wide) (by omega_arith) (by omega_arith), hq] at V₂
  have h₂ := h₁.keepF K₂ (by decide) (by decide) F₂ (prodR_fit h₁)
  have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  rw [sp₁] at F₂
  have k₂ : ∀ {d k}, numBase ≤ d → d + 4 * k ≤ bytes → val32 u₂.mem base d k = val32 s.mem base d k :=
    fun hd hk => (prodR_keep h₁ F₂ (sp₁ ▸ h₁.room) (by omega_arith) hk).trans (k₁ hd hk)
  -- `p q = n`.
  have pq : val32 u₂.mem base prodOff (2 * cn) = p * q := by
    have sp := val32_succ u₂.mem base prodOff (2 * cn)
    rw [V₂] at sp
    have hl := val32_lt u₂.mem base prodOff (2 * cn)
    have hpq : p * q < 2 ^ (32 * (2 * cn)) := by
      have := val32_lt s.mem base (lo len (.slot .wide 10)) cn
      have := val32_lt s.mem base (lo len (.slot .wide 11)) cn
      rw [hp] at *; rw [hq] at *
      rw [show 32 * (2 * cn) = 32 * cn + 32 * cn by omega_arith, Nat.pow_add]
      exact Nat.mul_lt_mul'' (by assumption) (by assumption)
    have : w32 u₂.mem base (prodOff + 4 * (2 * cn)) = 0 := by
      by_contra hne
      have : 2 ^ (32 * (2 * cn)) ≤ 2 ^ (32 * (2 * cn)) * w32 u₂.mem base (prodOff + 4 * (2 * cn)) :=
        Nat.le_mul_of_pos_right _ (by omega_arith)
      omega_arith
    rw [this, Nat.mul_zero, Nat.add_zero] at sp
    exact sp.symm
  refine WP.seq (WP.mono (equal_ok h₂ (a := prod) (b := .slot .wide 9) (two_ok .wide)
    (by rw [cb2]; simp only [prod, lo]; omega_using [pf.1, pf.2.1, pf.2.2]) (by rw [cb2]; omega_arith)) fun u₃ ⟨M₃, C₃, K₃⟩ => ?_)
  simp only [prod, lo, cw2] at C₃
  rw [show numBase + 9 * st len .wide = lo len (.slot .wide 9) from rfl, k₂ (d := lo len (.slot .wide 9)) (k := 2 * cwc len .wide) (by omega_arith) (by omega_arith), hn,
    show 2 * cwc len .wide = 2 * cn from rfl, pq] at C₃
  have h₃ := h₂.regs K₃ M₃
  -- The mask stored.
  refine wp_storeS (h₃.scratch.ea (d := accOff) (by omega_arith))
    (h₃.scratch.write (d := accOff) (n := 4) (by omega_arith)) fun u₄ m₄ => WP.block_nil ?_
  have O₄ : Outside base accOff 4 u₃.mem u₄.mem := by rw [m₄.mem]; exact writeW32_outside _ _ _ (by omega_arith)
  have A₄ : w32 u₄.mem base accOff = (cmask (decide (p * q = n))).toNat := by
    rw [m₄.mem, w32_write_self, C₃]
  refine ⟨?_, A₄, (((K₁.mono (by decide)).trans K₂).trans K₃).trans ((m₄.keeps []).mono (by decide))⟩
  have sp₂ : u₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
  have F₁ : Frame (frameR base (s.gpr .esp) (valR len)) s.mem u₁.mem :=
    frameR_of_outside O₁ (by omega_arith) (by simp)
  have F₂' : Frame (frameR base (s.gpr .esp) (valR len)) u₁.mem u₂.mem :=
    frameR_mono F₂ fun p hp => by
      simp only [prodR, List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> simp
  have F₄ : Frame (frameR base (s.gpr .esp) (valR len)) u₂.mem u₄.mem := by
    rw [← M₃]; exact frameR_of_outside O₄ (by omega_arith) (by simp)
  exact (F₁.trans F₂').trans F₄

/-- A factor's value is below `2^(8 L)` for its length `L`. -/
theorem component_lt (m : Mem) (args : Nat → BitVec 32) (i : Nat) :
    componentValue m args i < 2 ^ (8 * (args (i + 1)).toNat) := by
  have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt m (byteAddr (args i)) (args (i + 1)).toNat)
  rwa [VG.Proof.Bignum.bytesAt_length, VG.Proof.Bignum.pow256_eq] at this

/-- A factor's length (argument `i`) into the header word at `lenOff`. -/
theorem setLen_ok (h : In Ex base bytes len args s) {i : Nat} (hi : i < 18) {is : List Instr} {Q : State → Prop}
    (k : ∀ u, In Ex base bytes len args u → VG.Proof.Mont.Outside base lenOff 4 s.mem u.mem →
      w32 u.mem base lenOff = (args i).toNat → Keeps [.eax] s u → WP isa (.block is) u Q) :
    WP isa (.block (setLen i ++ is)) s Q := by
  have nw := h.scratch.nowrap
  have bl : 3336 ≤ bytes := by
    have := h.slot_fit .wide (j := 0) (by decide)
    have e0 : lo len (.slot .wide 0) = numBase := sl_zero len .wide
    simp only [numBase] at e0; omega_arith
  simp only [setLen, List.cons_append]
  refine wp_movS (h.arg hi) fun v₁ b₁ _ => ?_
  have hv₁ := h.regs b₁.keeps b₁.mem
  refine wp_storeS (hv₁.scratch.ea (d := lenOff) (by simp only [lenOff]; omega_arith))
    (hv₁.scratch.write (d := lenOff) (by simp only [lenOff]; omega_arith)) fun u s₅ => ?_
  have m : u.mem = s.mem.writeW (off base lenOff) (args i) := by rw [s₅.mem, b₁.mem, b₁.gpr]
  have O : VG.Proof.Mont.Outside base lenOff 4 s.mem u.mem := by
    rw [m]; exact writeW32_outside _ _ _ (by simp only [lenOff]; omega_arith)
  refine k u (hv₁.keep (s₅.keeps []) (by decide) (by decide)
    (by rw [b₁.mem]; exact O.mono (Nat.zero_le _) (by simp only [lenOff]; omega_arith))) O
    (by rw [m, w32_write_self]) (b₁.keeps.trans ((s₅.keeps []).mono (by decide)))

/-- The body of the factors' values, after the entry: `n`, `p` and `q`
loaded, the mask of `p q = n`, then each factor's `R² mod p` into the wide
slots 16 (`p`) and 17 (`q`), and the mask's low bit in `eax`. -/
theorem primesBody_ok (h : RIn base bytes len args s) :
    WP isa primesBody s fun u =>
      Frame [below (s.gpr .esp) 96, ⟨base, bytes⟩] s.mem u.mem ∧
      val32 u.mem base (lo len (.slot .wide 16)) (2 * Spec.Rsa.primeWords (args 7).toNat) =
        2 ^ r2Exp (args 7).toNat % safeM (componentValue s.mem args 6) ∧
      val32 u.mem base (lo len (.slot .wide 17)) (2 * Spec.Rsa.primeWords (args 9).toNat) =
        2 ^ r2Exp (args 9).toNat % safeM (componentValue s.mem args 8) ∧
      u.gpr .eax = BitVec.ofNat 32 (decide (componentValue s.mem args 6 * componentValue s.mem args 8 =
        componentValue s.mem args 2)).toNat ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have nw := h.scratch.nowrap
  have bl := h.bytes_lt
  have pf := h.prod_fit
  have hup := h.upper'
  have f18 := h.slot_fit .wide (j := 18) (by decide)
  have bw := bc_eq_cwc len .wide
  have bwh := bc_le_wide len .half
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have el : ∀ j, lo len (.slot .wide j) = numBase + j * st len .wide := fun _ => rfl
  have nb : numBase = 3336 := rfl
  have p7 : 0 < (args 7).toNat := h.extra.positive 6 (by simp [componentArguments])
  have b7 : (args 7).toNat ≤ len := h.extra.bounded 6 (by simp [componentArguments])
  have p9 : 0 < (args 9).toNat := h.extra.positive 8 (by simp [componentArguments])
  have b9 : (args 9).toNat ≤ len := h.extra.bounded 8 (by simp [componentArguments])
  have gw := bc_ge h.lower' .wide
  have pw7 : 2 * Spec.Rsa.primeWords (args 7).toNat ≤ cwc len .wide := by
    have := len_le_bc len; have := bc_dvd len .wide
    simp only [Spec.Rsa.primeWords, Spec.Rsa.modulusWords, cwc]; omega_arith
  have pw9 : 2 * Spec.Rsa.primeWords (args 9).toNat ≤ cwc len .wide := by
    have := len_le_bc len; have := bc_dvd len .wide
    simp only [Spec.Rsa.primeWords, Spec.Rsa.modulusWords, cwc]; omega_arith
  have e9 := el 9
  have e10 := el 10
  have e11 := el 11
  have e16 := el 16
  have e17 := el 17
  have e18 := el 18
  -- A frame of `factorR len o` keeps a number from the wide slot 9 on that misses the slot `o`.
  have keepR : ∀ {o : Nat} {sp : BitVec 32} {v : State} {m m' : Mem}, 16 ≤ o → o ≤ 17 →
      RIn base bytes len args v → CallRoom sp base bytes → Frame (frameR base sp (factorR len o)) m m' →
      ∀ {d k : Nat}, lo len (.slot .wide 9) ≤ d → d + 4 * k ≤ bytes →
        (d + 4 * k ≤ lo len (.slot .wide o) ∨ lo len (.slot .wide o) + bc len .wide ≤ d) →
        val32 m' base d k = val32 m base d k := by
    intro o sp v m m' ho16 ho hv R F d k hd hk hdo
    refine frameR_val32 F R nw hk (fun q hq => ?_) (fun q hq => (factorR_props hv ho16 ho q hq).1)
    rcases (factorR_props hv ho16 ho q hq).2.2 with hb | ⟨e, hl⟩
    · exact .inr (Nat.le_trans hb hd)
    · rw [e]; rcases hdo with hdo | hdo
      · exact .inl hdo
      · exact .inr (by omega)
  have keepA : ∀ {o : Nat} {sp : BitVec 32} {v : State} {m m' : Mem}, 16 ≤ o → o ≤ 17 →
      RIn base bytes len args v → CallRoom sp base bytes → Frame (frameR base sp (factorR len o)) m m' →
      w32 m' base accOff = w32 m base accOff := by
    intro o sp v m m' ho16 ho hv R F
    rw [← w32_val32_one, ← w32_val32_one]
    exact frameR_val32 F R nw (by simp only [accOff]; omega_arith)
      (fun q hq => by have := (factorR_props hv ho16 ho q hq).2.1; simpa using this)
      (fun q hq => (factorR_props hv ho16 ho q hq).1)
  unfold primesBody check
  -- `n`, `p` and `q` (and the rest of the components).
  refine WP.seq (WP.seq (WP.mono (importComponents_ok h) fun u₁ ⟨O₁, n₁, _, p₁, q₁, _, _, _, K₁⟩ => ?_))
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega_arith))
  have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  -- `p q = n`.
  refine WP.mono (pqCheck_ok h₁ n₁ p₁ q₁) fun u₂ ⟨F₂, A₂, K₂⟩ => ?_
  have h₂ := h₁.keepF K₂ (by decide) (by decide) F₂ (valR_fit h₁)
  have sp₂ : u₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
  have k₂ : ∀ {d k}, numBase ≤ d → d + 4 * k ≤ bytes → val32 u₂.mem base d k = val32 u₁.mem base d k :=
    fun hd hk => valR_keep h₁ F₂ h₁.room hd hk
  -- The factor `p`.
  refine WP.seq (setLen_ok h₂ (i := 7) (by decide) fun u₃ h₃ O₃ l₃ K₃ => WP.block_nil ?_)
  have sp₃ : u₃.gpr .esp = s.gpr .esp := (K₃.1 _ (by decide)).trans sp₂
  have k₃ : ∀ {d k}, numBase ≤ d → d + 4 * k ≤ bytes → val32 u₃.mem base d k = val32 u₁.mem base d k :=
    fun hd hk => by
      rw [VG.Proof.Mont.Outside.val32 O₃ (.inr (by simp only [lenOff]; omega_arith)) (by omega_arith)]
      exact k₂ hd hk
  refine WP.seq (WP.mono (factor_ok h₃ (f := 10) (o := 16) (p := componentValue s.mem args 6) (by decide)
    (by decide) (by decide) (by decide) (by rw [k₃ (by omega_arith) (by omega_arith), p₁])
    (by rw [l₃]; omega) (by rw [l₃]; exact b7) (by rw [l₃]; exact component_lt s.mem args 6))
    fun u₄ ⟨F₄, V₄, L₄, K₄⟩ => ?_)
  rw [l₃] at V₄
  have h₄ := h₃.keepF K₄ (by decide) (by decide) F₄ (fun q hq => (factorR_props h₃ (by decide) (by decide) q hq).1)
  have sp₄ : u₄.gpr .esp = s.gpr .esp := (K₄.1 _ (by decide)).trans sp₃
  rw [sp₃] at F₄
  -- The factor `q`.
  refine WP.seq (setLen_ok h₄ (i := 9) (by decide) fun u₅ h₅ O₅ l₅ K₅ => WP.block_nil ?_)
  have sp₅ : u₅.gpr .esp = s.gpr .esp := (K₅.1 _ (by decide)).trans sp₄
  have q₅ : val32 u₅.mem base (lo len (.slot .wide 11)) (cwc len .wide) = componentValue s.mem args 8 := by
    rw [VG.Proof.Mont.Outside.val32 O₅ (.inr (by simp only [lenOff]; omega_arith)) (by omega_arith),
      keepR (o := 16) (by decide) (by decide) h₃ h.room F₄ (by omega_arith) (by omega_arith) (.inl (by omega_arith)),
      k₃ (by omega_arith) (by omega_arith), q₁]
  refine WP.seq (WP.mono (factor_ok h₅ (f := 11) (o := 17) (p := componentValue s.mem args 8) (by decide)
    (by decide) (by decide) (by decide) q₅
    (by rw [l₅]; omega) (by rw [l₅]; exact b9) (by rw [l₅]; exact component_lt s.mem args 8))
    fun u₆ ⟨F₆, V₆, _, K₆⟩ => ?_)
  rw [l₅] at V₆
  rw [sp₅] at F₆
  have h₆ := h₅.keepF K₆ (by decide) (by decide) (by rw [sp₅]; exact F₆)
    (fun q hq => (factorR_props h₅ (by decide) (by decide) q hq).1)
  -- The result.
  have acc : w32 u₆.mem base accOff = (cmask (decide (componentValue s.mem args 6 * componentValue s.mem args 8 =
      componentValue s.mem args 2))).toNat := by
    rw [keepA (o := 17) (by decide) (by decide) h₅ h.room F₆,
      VG.Proof.Mont.Outside.w32 O₅ (.inl (by simp only [accOff, lenOff]; omega)) (by simp only [accOff]; omega),
      keepA (o := 16) (by decide) (by decide) h₃ h.room F₄,
      VG.Proof.Mont.Outside.w32 O₃ (.inl (by simp only [accOff, lenOff]; omega)) (by simp only [accOff]; omega),
      A₂]
  refine wp_movS (readSrc_sc h₆.scratch (d := accOff) (by simp only [accOff]; omega_arith)) fun u₇ a₇ _ => ?_
  refine VG.X86.Wp.wp_andi fun u a => WP.block_nil ?_
  have mu : u.mem = u₆.mem := by rw [a.mem, a₇.mem]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- The frames, as regions of the stack and the working space.
    let R : List Region := [below (s.gpr .esp) 96, ⟨base, bytes⟩]
    have ofR : ∀ {ws : List (Nat × Nat)} {m m' : Mem}, (∀ q ∈ ws, q.1 + q.2 ≤ bytes) →
        Frame (frameR base (s.gpr .esp) ws) m m' → Frame R m m' := fun fit F => F.sub fun r hr => by
      simp only [frameR, List.mem_cons, List.mem_map] at hr
      rcases hr with rfl | ⟨q, hq, rfl⟩
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨⟨base, bytes⟩, by simp [R], Offset.sub_base base (fit q hq)⟩
    have ofB : ∀ {o n : Nat} {m m' : Mem}, o + n ≤ bytes → VG.Proof.Mont.Outside base o n m m' →
        Frame R m m' := by
      intro o n m m' hon O
      refine (outside_frame O (by omega)).sub fun r hr => ?_
      rw [List.mem_singleton.mp hr]
      exact ⟨⟨base, bytes⟩, by simp [R], Offset.sub_base base hon⟩
    rw [sp₁] at F₂
    rw [mu]
    exact (((((ofB (by omega_arith) O₁).trans (ofR (valR_fit h₁) F₂)).trans
      (ofB (by simp only [lenOff]; omega_arith) O₃)).trans
      (ofR (fun q hq => (factorR_props h₃ (by decide) (by decide) q hq).1) F₄)).trans
      (ofB (by simp only [lenOff]; omega_arith) O₅)).trans
      (ofR (fun q hq => (factorR_props h₅ (by decide) (by decide) q hq).1) F₆)
  · rw [mu, keepR (o := 17) (by decide) (by decide) h₅ h.room F₆ (by omega_arith) (by omega_arith)
      (.inl (by omega_arith)),
      VG.Proof.Mont.Outside.val32 O₅ (.inr (by simp only [lenOff]; omega_arith)) (by omega_arith)]
    exact V₄
  · rw [mu]; exact V₆
  · rw [a.gpr, a₇.gpr]
    have e : u₆.mem.readW (off base accOff) 32 = cmask (decide (componentValue s.mem args 6 *
        componentValue s.mem args 8 = componentValue s.mem args 2)) := BitVec.eq_of_toNat_eq acc
    rw [e]
    cases decide (componentValue s.mem args 6 * componentValue s.mem args 8 = componentValue s.mem args 2) <;> rfl
  · exact (((((((K₁.mono (by decide)).trans K₂).trans (K₃.mono (by decide))).trans K₄).trans
      (K₅.mono (by decide))).trans K₆).trans (a₇.keeps.mono (by decide))).trans (a.keeps.mono (by decide))

end

end VG.Proof.Bignum.X86.PrivPre
