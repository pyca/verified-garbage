module

import VerifiedGarbage.Proof.Rsa.X86.GcdBatchRt.Shr
public import VerifiedGarbage.Proof.Rsa.X86.GcdBatchRt.Writes
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Slots
public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.InitWords
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.SelectX
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Red
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import VerifiedGarbage.Impl.Rsa.X86.GcdBatchRt
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Ops
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Weierstrass.X86.InvClob

/-! # The GCD's start

`copyC_ok`: `InvBatchRt.copy_ok` for any count; `extend_ok`: a number of `n - 1` words
(a narrow array), zero-extended to `n + 1`; `init_ok`: `f = m`, `g = oddInput m x`, `δ = 1`
and the batch count.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.GcdBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Impl.Rsa.X86.GcdBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.InvBatchRt
open VG.Proof.Weierstrass (Unch)
open VG.Proof.Weierstrass.X86.Inv (wordClob)
open VG.Proof.Rsa.Divstep (oddInput)

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- `selIn o a cnt`: `[o] = [a]` where the mask `ecx` is all ones, else kept, `n + e`
words. -/
theorem selInC_ok {s : State} (h : Bx L s B Z len N) {o a : Ref} {cnt : List Instr} {c : Nat} {k : Bool}
    (hk : s.gpr .ecx = cmask k) (hc : CountSpec cnt .edi B Z (kw len) c) (hc0 : 0 < c)
    (hoz : rv (kw len) o + 4 * c ≤ Z) (haz : rv (kw len) a + 4 * c ≤ Z)
    (sep : rv (kw len) o + 4 * c ≤ rv (kw len) a ∨ rv (kw len) a + 4 * c ≤ rv (kw len) o) :
    WP isa (selIn L o a cnt) s fun t =>
      Bx L t B Z len N ∧ Outside B (rv (kw len) o) (4 * c) s.mem t.mem ∧
      val32 t.mem B (rv (kw len) o) c =
        (if k then val32 s.mem B (rv (kw len) a) c else val32 s.mem B (rv (kw len) o) c) ∧
      Keeps [.eax, .ebx, .edx, .ebp] s t := by
  have hn := h.nowrap
  have hw := kw_bound h.ws.lenLe
  have hpos := h.ws.kw_pos
  have ke := kw_eq len
  have hZ := h.halfZ
  unfold selIn
  rw [show cnt = cnt ++ [] from (List.append_nil _).symm]
  simp only [List.append_assoc]
  refine WP.seq (ptr_ok h.ws h.slots hZ (by decide) (by decide) (by decide) (by decide) (by intro e; cases e)
    (by omega) fun u₁ K₁ m₁ p₁ => ?_)
  have h₁ : Bx L u₁ B Z len N := h.keep K₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
    (rv_ge _ o) hoz
  refine ptr_ok h₁.ws h₁.slots hZ (by decide) (by decide) (by decide) (by decide) (by intro e; cases e)
    (by omega) fun u₂ K₂ m₂ p₂ => ?_
  have h₂ : Bx L u₂ B Z len N := h₁.keep K₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _)
    (rv_ge _ o) hoz
  refine hc u₂ _ _ h₂.ws.ws.workspace h₂.slots fun u K₃ m₃ c₃ => WP.block_nil ?_
  have K : Keeps [.ebx, .edx, .ebp, .edi] s u :=
    (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide)))
  have m : u.mem = s.mem := by rw [m₃, m₂, m₁]
  have ecx : u.gpr .ecx = cmask k := by rw [K.1 _ (by decide)]; exact hk
  refine WP.seq (WP.mono (selectLoopX_ok (h.ws.rt.of_keeps K) (x := rv (kw len) a) (d := rv (kw len) o)
    (N := c) k (by omega) (by omega) sep
    (by rw [PtrAt, K₃.1 _ (by decide), K₂.1 _ (by decide)]; exact p₁)
    (by rw [PtrAt, K₃.1 _ (by decide)]; exact p₂) (by rw [c₃]) ecx) fun t ⟨O, V, _, Kt⟩ => ?_)
  rw [m] at O V
  have KK : Keeps [.eax, .ebx, .edx, .ebp, .edi] s t := (K.mono (by decide)).trans Kt
  have O0 : Outside B 0 Z s.mem t.mem := O.mono (Nat.zero_le _) (by omega)
  refine wp_movS (h.ws.wsArg.keep KK (by decide) O0).readSrc fun t₁ U _ => WP.block_nil ?_
  have K' : Keeps [.eax, .ebx, .edx, .ebp] s t₁ :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .edx, .ebp])
      (KK.trans (U.keeps.mono (by decide))) (U.gpr.trans (RtWs.edi_eq h.ws).symm)
  exact ⟨h.keep K' (by decide) (by decide) (by rw [U.mem]; exact O) (rv_ge _ o) hoz,
    by rw [U.mem]; exact O, by rw [U.mem]; exact V, K'⟩

/-- `copy o a cnt`: `[o] = [a]`, `n + e` words. -/
theorem copyC_ok {s : State} (h : Bx L s B Z len N) {o a : Ref} {cnt : List Instr} {c : Nat}
    (hc : CountSpec cnt .edi B Z (kw len) c) (hc0 : 0 < c)
    (hoz : rv (kw len) o + 4 * c ≤ Z) (haz : rv (kw len) a + 4 * c ≤ Z)
    (sep : rv (kw len) o + 4 * c ≤ rv (kw len) a ∨ rv (kw len) a + 4 * c ≤ rv (kw len) o) :
    WP isa (VG.Impl.Rsa.X86.InvBatchRt.copy L o a cnt) s fun t =>
      Bx L t B Z len N ∧ Outside B (rv (kw len) o) (4 * c) s.mem t.mem ∧
      val32 t.mem B (rv (kw len) o) c = val32 s.mem B (rv (kw len) a) c ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold VG.Impl.Rsa.X86.InvBatchRt.copy
  refine WP.seq (wp_movS rfl fun u U _ => WP.block_nil ?_)
  have hu : Bx L u B Z len N := h.keep U.keeps (by decide) (by decide) (by rw [U.mem]; exact Outside.refl _ _ _ _)
    (rv_ge _ o) hoz
  refine WP.mono (selInC_ok hu (k := true) (by rw [U.gpr]; rfl) hc hc0 hoz haz sep) fun t ⟨H, O, V, K⟩ =>
    ⟨H, by rw [U.mem] at O; exact O, by rw [V, U.mem]; rfl, (U.keeps.mono (by decide)).trans (K.mono (by decide))⟩

/-- `nBytesLess r` counts `n - 1` words. -/
theorem countLess {r : Reg} {s : State} (hb : Bx L s B Z len N) (h2 : 2 ≤ nw len) :
    CountSpec (nBytesLess r) r B Z (kw len) (nw len - 1) :=
  fun _ _ _ hs hsl k => nBytesLess_ok hs hsl hb.halfZ (by have := kw_bound hb.ws.lenLe; omega)
    (by have := kw_eq len; omega) fun v K m c => k v K m (by rw [c]; have := kw_eq len; omega)

/-- `nBytes r 1` counts `n + 1` words. -/
theorem countN1 {r : Reg} {s : State} (hb : Bx L s B Z len N) :
    CountSpec (nBytes r 1) r B Z (kw len) (nw len + 1) := by
  have := nBytes_spec (r := r) (e := 1) (B := B) hb.halfZ (w := kw len) (by have := kw_bound hb.ws.lenLe; omega)
    (by decide) (by have := kw_eq len; omega)
  rwa [show kw len / 2 + 1 = nw len + 1 by have := kw_eq len; omega] at this

/-- `nBytes r 0` counts `n` words. -/
theorem countN0 {r : Reg} {s : State} (hb : Bx L s B Z len N) :
    CountSpec (nBytes r 0) r B Z (kw len) (nw len) := by
  have := nBytes_spec (r := r) (e := 0) (B := B) hb.halfZ (w := kw len) (by have := kw_bound hb.ws.lenLe; omega)
    (by decide) (by have := kw_eq len; omega)
  rwa [show kw len / 2 + 0 = nw len by have := kw_eq len; omega] at this

/-- A number of `k` words followed by two words of zeros, from the zeros of `k + 2` words and
the number's words. -/
theorem val32_extend {m m' : Mem} {d k v : Nat} (Z0 : val32 m B d (k + 2) = 0) (C : val32 m' B d k = v)
    (O : Outside B d (4 * k) m m') (hd : d + 4 * (k + 2) ≤ 2 ^ 64) : val32 m' B d (k + 2) = v := by
  have hi : val32 m' B (d + 4 * k) 2 = val32 m B (d + 4 * k) 2 := O.val32 (.inr (Nat.le_refl _)) (by omega)
  rw [val32_append] at Z0 ⊢
  have p := Nat.two_pow_pos (32 * k)
  have z : val32 m B (d + 4 * k) 2 = 0 := by
    rcases Nat.eq_zero_or_pos (val32 m B (d + 4 * k) 2) with e | e
    · exact e
    · have := Nat.mul_le_mul_left (2 ^ (32 * k)) e; omega
  rw [hi, z, C]; omega

/-- A number of `k + 1` words below `2 ^ (32 k)`: its low `k` words, and its top word zero. -/
theorem low_eq {mm : Mem} {d k v : Nat} (h : val32 mm B d (k + 1) = v) (hv : v < 2 ^ (32 * k)) :
    val32 mm B d k = v ∧ w32 mm B (d + 4 * k) = 0 := by
  rw [val32_succ] at h
  have p := Nat.two_pow_pos (32 * k)
  rcases Nat.eq_zero_or_pos (w32 mm B (d + 4 * k)) with e | e
  · rw [e, Nat.mul_zero, Nat.add_zero] at h; exact ⟨h, e⟩
  · have := Nat.mul_le_mul_left (2 ^ (32 * k)) e; omega

/-- `[o]` the `n - 1` words of `[src]` zero-extended to `n + 1`. -/
theorem extend_ok {s : State} (h : Bx L s B Z len N) (h3 : 3 ≤ nw len) {o src : Ref}
    (hoz : rv (kw len) o + 4 * (nw len + 1) ≤ Z) (hsz : rv (kw len) src + 4 * (nw len - 1) ≤ Z)
    (sep : rv (kw len) o + 4 * (nw len + 1) ≤ rv (kw len) src ∨ rv (kw len) src + 4 * (nw len - 1) ≤ rv (kw len) o)
    {rest : Prog isa} {Q : State → Prop}
    (k : ∀ u, Bx L u B Z len N → Outside B (rv (kw len) o) (4 * (nw len + 1)) s.mem u.mem →
      val32 u.mem B (rv (kw len) o) (nw len + 1) = val32 s.mem B (rv (kw len) src) (nw len - 1) →
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u → WP isa rest u Q) :
    WP isa (.seq (VG.Impl.Rsa.X86.InvBatchRt.zeros L o (nBytes .ecx 1))
      (.seq (VG.Impl.Rsa.X86.InvBatchRt.copy L o src (nBytesLess .edi)) rest)) s Q := by
  have hn := h.nowrap
  refine WP.seq (WP.mono (zeros_ok h (o := o) (countN1 h) (by omega) hoz) fun s₁ ⟨H₁, O₁, V₁, K₁⟩ => ?_)
  have S₁ : val32 s₁.mem B (rv (kw len) src) (nw len - 1) = val32 s.mem B (rv (kw len) src) (nw len - 1) :=
    O₁.val32 (by omega) (by omega)
  refine WP.seq (WP.mono (copyC_ok H₁ (o := o) (a := src) (countLess H₁ (by omega)) (by omega) (by omega)
    (by omega) (by omega)) fun u ⟨Hu, Ou, Vu, Ku⟩ => ?_)
  refine k u Hu ((O₁.mono (Nat.le_refl _) (Nat.le_refl _)).trans (Ou.mono (Nat.le_refl _) (by omega))) ?_
    ((K₁.mono (by decide)).trans Ku)
  rw [show nw len + 1 = nw len - 1 + 2 by omega] at V₁ ⊢
  exact val32_extend V₁ (Vu.trans S₁) Ou (by omega)

/-- The GCD's state between batches: `δ` in the window, `f` and `g` in arrays 4 and 5. -/
structure GState (len : Nat) (B : Addr) (I : Int × Int × Int) (s : State) : Prop where
  d : s.mem.readW (off B win) 32 = BitVec.ofInt 32 I.1
  f : (val32 s.mem B (rv (kw len) (a 4)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
    I.2.1 % 2 ^ (32 * (nw len + 1))
  g : (val32 s.mem B (rv (kw len) (a 5)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
    I.2.2 % 2 ^ (32 * (nw len + 1))

/-- The operands: `[4] = m`, `[5] = oddInput m x`, `n + 1` words each. -/
theorem operands_ok {s : State} (h : Bx L s B Z len N) (h3 : 3 ≤ nw len) {m x : Nat}
    (hm : val32 s.mem B (rv (kw len) (a 4)) (nw len - 1) = m)
    (hx : val32 s.mem B (rv (kw len) (a 0)) (nw len - 1) = x)
    {rest : Prog isa} {Q : State → Prop}
    (k : ∀ u, Bx L u B Z len N → val32 u.mem B (rv (kw len) (a 4)) (nw len + 1) = m →
      val32 u.mem B (rv (kw len) (a 5)) (nw len + 1) = oddInput m x → Keeps wordClob s u →
      Unch B [(rv (kw len) (a 4), 2 * (8 * nw len + 8)), (rv (kw len) (a 12), 8 * nw len + 8)] s.mem u.mem →
      WP isa rest u Q) :
    WP isa (.seq (VG.Impl.Rsa.X86.InvBatchRt.zeros L (a 12) (nBytes .ecx 1)) <|
      .seq (VG.Impl.Rsa.X86.InvBatchRt.copy L (a 12) (a 4) (nBytesLess .edi)) <|
      .seq (VG.Impl.Rsa.X86.InvBatchRt.copy L (a 4) (a 12) (nBytes .edi 1)) <|
      .seq (VG.Impl.Rsa.X86.InvBatchRt.zeros L (a 5) (nBytes .ecx 1)) <|
      .seq (VG.Impl.Rsa.X86.InvBatchRt.copy L (a 5) (a 0) (nBytesLess .edi)) <|
      .seq (VG.Impl.Rsa.X86.InvBatchRt.zeros L (a 12) (nBytes .ecx 1)) <|
      .seq (.block (VG.Impl.Rsa.X86.GcdBatch.evenMask (VG.Impl.Rsa.X86.InvBatchRt.offset 0 0))) <|
      .seq (selIn L (a 12) (a 4) (nBytes .edi 0)) <|
      .seq (VG.Impl.Rsa.X86.InvBatchRt.chain L .adc (a 5) (a 5) (a 12) (nBytes .edx 1)) rest) s Q := by
  have hn := h.nowrap
  have hf16 := h.fits16
  have r0 := rv_a len 0; have r4 := rv_a len 4; have r5 := rv_a len 5; have r12 := rv_a len 12
  have r11 := rv_a len 11
  -- `[12] = m`, then `[4] = m`.
  refine extend_ok h h3 (o := a 12) (src := a 4) (by omega_arith) (by omega_arith) (by omega_arith)
    fun s₁ H₁ O₁ V₁ K₁ => ?_
  rw [hm] at V₁
  refine WP.seq (WP.mono (copy_ok H₁ (o := a 4) (a := a 12) (e := 1) (by decide) (by omega_arith) (by omega_arith)
    (by omega_arith)) fun s₂ ⟨H₂, O₂, V₂, K₂⟩ => ?_)
  rw [V₁] at V₂
  have X₂ : val32 s₂.mem B (rv (kw len) (a 0)) (nw len - 1) = x := by
    rw [O₂.val32 (by omega_arith) (by omega_arith), O₁.val32 (by omega_arith) (by omega_arith), hx]
  -- `[5] = x`.
  refine extend_ok H₂ h3 (o := a 5) (src := a 0) (by omega_arith) (by omega_arith) (by omega_arith)
    fun s₃ H₃ O₃ V₃ K₃ => ?_
  rw [X₂] at V₃
  -- `[12] = 0`, then `m` where `x` is even.
  refine WP.seq (WP.mono (zeros_ok H₃ (o := a 12) (countN1 H₃) (by omega_arith) (by omega_arith))
    fun s₄ ⟨H₄, O₄, V₄, K₄⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.GcdBatch.evenMask_ok H₄.ws.ws.workspace
    (src := VG.Impl.Rsa.X86.InvBatchRt.offset 0 0) (by simp only [VG.Impl.Rsa.X86.InvBatchRt.offset]; omega_arith))
    fun s₅ ⟨C₅, K₅, m₅⟩ => ?_)
  have H₅ : Bx L s₅ B Z len N := H₄.keep K₅ (by decide) (by decide) (o := 160) (c := 0)
    (by rw [m₅]; exact Outside.refl _ _ _ _) (Nat.le_refl _) (by omega_arith)
  have o00 : VG.Impl.Rsa.X86.InvBatchRt.offset 0 0 = rv (kw len) (a 0) := by
    simp only [VG.Impl.Rsa.X86.InvBatchRt.offset]; omega_arith
  rw [o00, O₄.w32 (by omega_arith) (by omega_arith), O₃.w32 (by omega_arith) (by omega_arith),
    O₂.w32 (by omega_arith) (by omega_arith), O₁.w32 (by omega_arith) (by omega_arith)] at C₅
  have even : x % 2 = w32 s.mem B (rv (kw len) (a 0)) % 2 := by
    obtain ⟨j, hj⟩ : ∃ j, nw len - 1 = j + 1 := ⟨nw len - 2, by omega_arith⟩
    rw [← hx, hj, val32]
    omega_arith
  have mlt : m < 2 ^ (32 * (nw len - 1)) := hm ▸ val32_lt _ _ _ _
  have xlt : x < 2 ^ (32 * (nw len - 1)) := hx ▸ val32_lt _ _ _ _
  have grow : 2 ^ (32 * (nw len - 1)) * 2 ^ 32 = 2 ^ (32 * nw len) := by
    rw [← Nat.pow_add]; congr 1; omega_arith
  have g2 : 2 ^ 32 * 2 ^ (32 * nw len) = 2 ^ (32 * (nw len + 1)) := (pow32_succ _).symm
  have M₅ : val32 s₅.mem B (rv (kw len) (a 4)) (nw len) = m := by
    have A₃ : val32 s₃.mem B (rv (kw len) (a 4)) (nw len + 1) = m := by
      rw [O₃.val32 (by omega_arith) (by omega_arith), V₂]
    rw [m₅, O₄.val32 (by omega_arith) (by omega_arith)]
    exact (low_eq A₃ (lt_of_lt_of_le mlt (Nat.pow_le_pow_right (by decide) (by omega_arith)))).1
  refine WP.seq (WP.mono (selIn_ok H₅ (o := a 12) (a := a 4) (e := 0) (k := decide (x % 2 = 0))
    (by rw [C₅, even]; by_cases he : w32 s.mem B (rv (kw len) (a 0)) % 2 = 0 <;> simp [he, cmask])
    (by decide) (by omega_arith) (by omega_arith) (by omega_arith)) fun s₆ ⟨H₆, O₆, V₆, K₆⟩ => ?_)
  simp only [Nat.add_zero] at O₆ V₆
  rw [M₅] at V₆
  have T₆ : val32 s₆.mem B (rv (kw len) (a 12)) (nw len + 1) = if x % 2 = 0 then m else 0 := by
    have p := Nat.two_pow_pos (32 * nw len)
    have top4 : w32 s₄.mem B (rv (kw len) (a 12) + 4 * nw len) = 0 := by
      have := val32_succ s₄.mem B (rv (kw len) (a 12)) (nw len)
      rw [V₄] at this
      rcases Nat.eq_zero_or_pos (w32 s₄.mem B (rv (kw len) (a 12) + 4 * nw len)) with e | e
      · exact e
      · have := Nat.mul_le_mul_left (2 ^ (32 * nw len)) e; omega_arith
    have low4 : val32 s₄.mem B (rv (kw len) (a 12)) (nw len) = 0 := by
      have := val32_succ s₄.mem B (rv (kw len) (a 12)) (nw len)
      rw [V₄] at this; omega_arith
    rw [val32_succ, V₆, O₆.w32 (by omega_arith) (by omega_arith), m₅, top4, Nat.mul_zero, Nat.add_zero, low4]
    by_cases he : x % 2 = 0 <;> simp [he]
  -- `[5] += [12]`.
  refine WP.seq (WP.mono (chainAdd_ok H₆ (o := a 5) (a := a 5) (b := a 12) (e := 1) (by decide) rfl
    (by omega_arith) (by omega_arith) (by omega_arith) (.inl (Nat.le_refl _)) (by omega_arith))
    fun u ⟨Hu, Ou, ⟨c, _, Vu⟩, Ku⟩ => ?_)
  have G₆ : val32 s₆.mem B (rv (kw len) (a 5)) (nw len + 1) = x := by
    rw [O₆.val32 (by omega_arith) (by omega_arith), m₅, O₄.val32 (by omega_arith) (by omega_arith), V₃]
  rw [G₆, T₆] at Vu
  have sum : x + (if x % 2 = 0 then m else 0) < 2 ^ (32 * (nw len + 1)) := by
    rw [← g2, ← grow]; have := Nat.two_pow_pos (32 * (nw len - 1)); split <;> omega_arith
  have Gu : val32 u.mem B (rv (kw len) (a 5)) (nw len + 1) = oddInput m x := by
    unfold oddInput
    cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at Vu <;>
      omega_arith
  refine k u Hu ?_ Gu ?_ ?_
  · rw [Ou.val32 (by omega_arith) (by omega_arith), O₆.val32 (by omega_arith) (by omega_arith), m₅,
      O₄.val32 (by omega_arith) (by omega_arith), O₃.val32 (by omega_arith) (by omega_arith), V₂]
  · exact ((((((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans
      (K₄.mono (by decide))).trans (K₅.mono (by decide))).trans (K₆.mono (by decide))).trans (Ku.mono (by decide))
  · intro y hy
    have hA := hy (rv (kw len) (a 4), 2 * (8 * nw len + 8)) (by simp)
    have hT := hy (rv (kw len) (a 12), 8 * nw len + 8) (by simp)
    rw [Ou y (by omega_arith), O₆ y (by omega_arith), m₅, O₄ y (by omega_arith), O₃ y (by omega_arith),
      O₂ y (by omega_arith), O₁ y (by omega_arith)]

/-- `init`. -/
theorem init_ok {s : State} (h : RtWs L s B Z len N) (room : 16 ≤ N) (h3 : 3 ≤ nw len) {m x : Nat}
    (hm : val32 s.mem B (rv (kw len) (a 4)) (nw len - 1) = m)
    (hx : val32 s.mem B (rv (kw len) (a 0)) (nw len - 1) = x) :
    WP isa (VG.Impl.Rsa.X86.GcdBatchRt.init L) s fun z => Bx L z B Z len N ∧ GState len B (1, m, oddInput m x) z ∧
      w32 z.mem B 100 = 3 * (nw len + 1) ∧ Keeps wordClob s z ∧ Unch B (gcdWrites len) s.mem z.mem := by
  have hn := h.ws.workspace.nowrap
  have hw := kw_bound h.lenLe
  have ke := kw_eq len
  have e16 : win = 16 := rfl
  have e52 : slotBase = 52 := rfl
  have e96 : halfSlot = 96 := rfl
  unfold VG.Impl.Rsa.X86.GcdBatchRt.init
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  -- The slots.
  rw [show slots L = slots L ++ [] from (List.append_nil _).symm]
  refine WP.seq (slots_ok h room fun s₀ H₀ K₀ O₀ => WP.block_nil ?_)
  have hZ := H₀.halfZ
  have hf16 := H₀.fits16
  have r0 := rv_a len 0; have r4 := rv_a len 4; have r5 := rv_a len 5; have r12 := rv_a len 12
  have r11 := rv_a len 11
  have hm₀ : val32 s₀.mem B (rv (kw len) (a 4)) (nw len - 1) = m := by
    rw [O₀.val32 (by omega_arith) (by omega_arith), hm]
  have hx₀ : val32 s₀.mem B (rv (kw len) (a 0)) (nw len - 1) = x := by
    rw [O₀.val32 (by omega_arith) (by omega_arith), hx]
  refine operands_ok H₀ h3 hm₀ hx₀ fun u Hu F₄ G₅ Ku Uu => ?_
  -- `δ = 1`.
  refine WP.seq (wp_movS rfl fun u₁ V₁ _ => ?_)
  have hs₁ := Hu.ws.ws.workspace.of_keeps V₁.keeps (by decide)
  refine wp_storeS (hs₁.ea (by omega_arith)) (hs₁.write (d := win) (n := 4) (by omega_arith)) fun u₂ V₂ => WP.block_nil ?_
  have O₂ : Outside B win 4 u.mem u₂.mem := by rw [V₂.mem, V₁.mem]; exact writeW32_outside _ _ _ (by omega_arith)
  have H₂ : Bx L u₂ B Z len N := Hu.keepLow (V₁.keeps.trans (V₂.keeps _)) (by decide) (by decide) O₂ (by decide)
  have D₂ : u₂.mem.readW (off B win) 32 = 1 := by
    apply BitVec.eq_of_toNat_eq
    change w32 u₂.mem B win = _
    rw [V₂.mem, w32_write_self, V₁.gpr]
  -- The batch count.
  unfold batches
  refine nBytes_ok H₂.ws.ws.workspace H₂.slots hZ (by omega_arith) (e := 1) (by decide) fun u₁₂ K₁₂ m₁₂ c₁₂ => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun u₁₃ V₁₃ => ?_
  refine wp_movS rfl fun u₁₄ V₁₄ _ => wp_addS rfl fun u₁₅ V₁₅ _ => wp_addS rfl fun u₁₆ V₁₆ _ => ?_
  have K₁₆ : Keeps [.eax, .ecx] u₂ u₁₆ :=
    ((((K₁₂.mono (by decide)).trans (V₁₃.keeps.mono (by decide))).trans (V₁₄.keeps.mono (by decide))).trans
      (V₁₅.keeps.mono (by decide))).trans (V₁₆.keeps.mono (by decide))
  have hs₁₆ := H₂.ws.ws.workspace.of_keeps K₁₆ (by decide)
  refine wp_storeS (hs₁₆.ea (by omega_arith)) (hs₁₆.write (d := 100) (n := 4) (by omega_arith)) fun z Vz => WP.block_nil ?_
  have m₁₆ : u₁₆.mem = u₂.mem := by rw [V₁₆.mem, V₁₅.mem, V₁₄.mem, V₁₃.mem, m₁₂]
  have Oz : Outside B 100 4 u₂.mem z.mem := by rw [Vz.mem, m₁₆]; exact writeW32_outside _ _ _ (by omega_arith)
  have Hz : Bx L z B Z len N := H₂.keepHigh (K₁₆.trans (Vz.keeps _)) (by decide) (by decide) Oz (by decide)
    (by omega_arith)
  have count : w32 z.mem B 100 = 3 * (nw len + 1) := by
    rw [Vz.mem, w32_write_self, V₁₆.gpr, V₁₅.gpr, V₁₅.other .ecx (by decide), V₁₄.gpr, V₁₄.other _ (by decide),
      V₁₃.gpr]
    have e₁₂ : (u₁₂.gpr .eax).toNat = 4 * (nw len + 1) := by rw [c₁₂]; omega_arith
    have e₁₃ : (u₁₂.gpr .eax >>> 2).toNat = nw len + 1 := by
      rw [BitVec.toNat_ushiftRight, e₁₂, Nat.shiftRight_eq_div_pow]; omega_arith
    simp only [BitVec.toNat_add, e₁₃]
    omega_arith
  refine ⟨Hz, ⟨?_, ?_, ?_⟩, count, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    change w32 z.mem B win = (BitVec.ofInt 32 1).toNat
    rw [Oz.w32 (by omega_arith) (by omega_arith)]
    exact congrArg BitVec.toNat D₂
  · rw [Oz.val32 (by omega_arith) (by omega_arith), O₂.val32 (by omega_arith) (by omega_arith), F₄]
  · rw [Oz.val32 (by omega_arith) (by omega_arith), O₂.val32 (by omega_arith) (by omega_arith), G₅]
  · exact (((K₀.mono (by decide)).trans Ku).trans ((V₁.keeps.trans (V₂.keeps _)).mono (by decide))).trans
      ((K₁₆.trans (Vz.keeps _)).mono (by decide))
  · intro y hy
    have h1 := hy (win, 88) (by simp [gcdWrites])
    have h2 := hy (rv (kw len) (a 0), 6 * (8 * nw len + 8)) (by simp [gcdWrites])
    have h3 := hy (rv (kw len) (a 11), 2 * (8 * nw len + 8)) (by simp [gcdWrites])
    simp only at h1 h2 h3
    rw [Oz y (by omega), O₂ y (by omega), Uu y (by
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp only <;> omega), O₀ y (by omega)]

end VG.Proof.Rsa.X86.GcdBatchRt
