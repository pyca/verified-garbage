module

public import VerifiedGarbage.Impl.Rsa.X86_64.RecoverFolded
import VerifiedGarbage.Proof.Rsa.X86_64.RpHalf
public import VerifiedGarbage.Proof.Rsa.RecoverFolded
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.RpBase
import VerifiedGarbage.Proof.Rsa.X86_64.RpRest
import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame
public import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Impl.Rsa.X86_64.Recover

/-! # Preparation of the aligned exponent for folded prime recovery -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.RecoveryFolded

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Impl.Rsa.X86_64.Keys.Recover VG.Impl.Rsa.X86_64.Keys.Recover.Folded
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- Copy both exponent arrays, including the padding words between them. -/
theorem copyExponent_ok {s : State} {B : Addr} {Z w o a : Nat} (h : Ws s B Z w)
    (ho : o + 2 ≤ 16) (ha : a + 2 ≤ 16) (hsep : a + 2 ≤ o ∨ o + 2 ≤ a) :
    WP isa (copyExponent o a) s fun t =>
      wv t.mem B (slot w o) (2 * (w + 2)) = wv s.mem B (slot w a) (2 * (w + 2)) ∧
      Outside B (slot w o) (16 * (w + 2)) s.mem t.mem ∧
      Keep [.r12, .r9, .rsi, .rbx, .rax, .r14] s t := by
  have hn := h.scr.nowrap
  have hz := h.hZ
  have hw1 := h.w1
  have hw2 := h.w2
  have so : slot w o + 16 * (w + 2) ≤ Z := by
    have hm := Nat.mul_le_mul_right (8 * (w + 2)) ho
    simp only [Nat.add_mul] at hm
    unfold slot at hz ⊢
    omega
  have sa : slot w a + 16 * (w + 2) ≤ Z := by
    have hm := Nat.mul_le_mul_right (8 * (w + 2)) ha
    simp only [Nat.add_mul] at hm
    unfold slot at hz ⊢
    omega
  have sp : slot w a + 16 * (w + 2) ≤ slot w o ∨ slot w o + 16 * (w + 2) ≤ slot w a := by
    unfold slot
    rcases hsep with hsep | hsep
    · have hm := Nat.mul_le_mul_right (8 * (w + 2)) hsep
      simp only [Nat.add_mul] at hm
      left; omega
    · have hm := Nat.mul_le_mul_right (8 * (w + 2)) hsep
      simp only [Nat.add_mul] at hm
      right; omega
  unfold copyExponent
  rw [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.mono (base2_ok a o (r₁ := .rsi) (r₂ := .rbx) (by decide) (by decide) (by decide)
      ((k₁.gpr (by decide)).trans h.rdi) h9 (by decide)) fun s₂ ⟨hsi, hbx, m₂, k₂⟩ => ?_))
  have h12₂ : s₂.gpr .r12 = BitVec.ofNat 64 w := (k₂.gpr (by decide)).trans h12
  refine WP.seq (WP.mono (WP.keep [.r12] (Q := fun t =>
    t.gpr .r12 = BitVec.ofNat 64 (2 * (w + 2)) ∧ t.mem = s₂.mem) (by
      xrun [h12₂, BitVec.ofNat_add, show 2 * (w + 2) = w + 2 + (w + 2) by omega]
      rfl) rfl)
      fun s₃ ⟨⟨h12₃, m₃⟩, k₃⟩ => ?_)
  have hs₃ := h.scr.congr ((k₁.trans k₂).trans k₃).2.2
  refine WP.mono (copyWords_ok ((k₃.gpr (by decide)).trans hsi)
    ((k₃.gpr (by decide)).trans hbx) h12₃ (by omega) (by omega) (by omega)
    (fun i hi => hs₃.ld (by omega)) (fun i hi => hs₃.st (by omega))
    (fun i hi b hb => by rw [ofs_off B (by omega)]; omega)) fun t ⟨hv, _, out, k₄⟩ => ?_
  rw [m₃, m₂, m₁] at hv out
  exact ⟨hv, by simpa only [show 8 * (2 * (w + 2)) = 16 * (w + 2) by omega] using out,
    (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩

/-- The shift and masked selection, independently of the mask's source. -/
theorem halfTail_ok {s : State} {B : Addr} {Z w el m : Nat} {keep : Bool}
    (h : Ws s B Z w) (he2 : el ≤ 8 * w)
    (h8 : s.gpr .r8 = off B (slot w aM)) (hsi : s.gpr .rsi = off B (slot w aH))
    (h12 : s.gpr .r12 = BitVec.ofNat 64 (w + (el + 7) / 8)) (hbp : s.gpr .rbp = mask keep)
    (hm : wv s.mem B (slot w aM) (2 * (w + 2)) = m)
    (hmlt : m < 2 ^ (64 * (w + (el + 7) / 8))) :
    WP isa halfTail s fun t =>
      wv t.mem B (slot w aM) (2 * (w + 2)) = (if keep then m else m / 2) ∧
      Frm B [(slot w aM, 16 * (w + 2)), (slot w aH, 16 * (w + 2))] s.mem t.mem ∧
      Keep [.rax, .rdx, .r14] s t := by
  have hn := h.scr.nowrap
  have hz := h.hZ
  have hw1 := h.w1
  have hw2 := h.w2
  let n := w + (el + 7) / 8
  have hn1 : 1 ≤ n := by dsimp [n]; omega
  have hn2 : n + 1 ≤ 2 * (w + 2) := by dsimp [n]; omega
  have emh : slot w aH = slot w aM + 32 * (w + 2) := by simp only [slot, aM, aH]; omega
  have eh16 : slot w aH + 16 * (w + 2) = slot w 16 := by simp only [slot, aH]; omega
  have hlow : wv s.mem B (slot w aM) n = m := by
    rw [wv_low_of_lt (v := n) (w := 2 * (w + 2)) (by omega) (by rw [hm]; exact hmlt), hm]
  have htop : word s.mem B (slot w aM + 8 * n) = 0 :=
    word_above_zero (L := 2 * (w + 2)) (n := n) (by omega) (by rw [hm]; exact hmlt)
  unfold halfTail
  refine WP.seq (WP.mono (shr_ok h.scr hsi h8 h12 hn1 (by omega) (by omega) (by omega)
    (Or.inr (by omega))) fun u ⟨hu, ou, ku⟩ => ?_)
  rw [hlow, htop] at hu
  have hv : wv u.mem B (slot w aH) n = m / 2 := by
    rw [show BitVec.toNat (0 : BitVec 64) = 0 from rfl, Nat.zero_mod, Nat.mul_zero, Nat.add_zero] at hu
    dsimp only [n] at *
    omega
  have hm0 : wv u.mem B (slot w aM) n = m := by
    rw [ou.wv (Or.inl (by omega)) (by omega), hlow]
  refine WP.mono (sel_ok (h.scr.congr ku.2.2) ((ku.gpr (by decide)).trans h8)
    ((ku.gpr (by decide)).trans hsi) ((ku.gpr (by decide)).trans hbp)
    ((ku.gpr (by decide)).trans h12) hn1 (by omega) (by omega) (by omega)
    (Or.inl (by omega))) fun t ⟨ht, ot, kt⟩ => ?_
  have hfull (mm : Mem) : wv mm B (slot w aM) (2 * (w + 2)) =
      wv mm B (slot w aM) n + 2 ^ (64 * n) * wv mm B (slot w aM + 8 * n) (2 * (w + 2) - n) := by
    rw [← wv_add, show n + (2 * (w + 2) - n) = 2 * (w + 2) by omega]
  have hhigh0 : wv s.mem B (slot w aM + 8 * n) (2 * (w + 2) - n) = 0 := by
    have he := hfull s.mem
    rw [hm, hlow] at he
    have heq : 2 ^ (64 * n) * wv s.mem B (slot w aM + 8 * n) (2 * (w + 2) - n) = 0 := by omega
    exact (Nat.mul_eq_zero.mp heq).resolve_left (Nat.ne_of_gt (Nat.two_pow_pos _))
  have hhigh : wv t.mem B (slot w aM + 8 * n) (2 * (w + 2) - n) = 0 := by
    rw [ot.wv (Or.inr (Nat.le_refl _)) (by omega), ou.wv (Or.inl (by omega)) (by omega), hhigh0]
  refine ⟨?_, ?_, (ku.trans kt).mono (by decide)⟩
  · rw [hfull, hhigh, Nat.mul_zero, Nat.add_zero, ht, hm0, hv]
  · intro x hx
    have hM := hx (slot w aM, 16 * (w + 2)) (by simp)
    have hH := hx (slot w aH, 16 * (w + 2)) (by simp)
    dsimp only at hM hH
    rw [ot x (by omega), ou x (by omega)]

theorem halfOnce_ok {s : State} {B : Addr} {Z w el m : Nat} (h : Ws s B Z w)
    (hel : word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el)
    (he2 : el ≤ 8 * w) (hm : wv s.mem B (slot w aM) (2 * (w + 2)) = m)
    (hmlt : m < 2 ^ (64 * (w + (el + 7) / 8))) :
    WP isa halfOnce s fun t =>
      wv t.mem B (slot w aM) (2 * (w + 2)) = (if m % 2 = 1 then m else m / 2) ∧
      Frm B [(slot w aM, 16 * (w + 2)), (slot w aH, 16 * (w + 2))] s.mem t.mem ∧
      Keep [.r12, .r9, .r8, .rsi, .rax, .rbp, .rdx, .r14] s t := by
  have hw1 := h.w1
  have hw2 := h.w2
  have hp : (word s.mem B (slot w aM)).toNat % 2 = m % 2 := by
    rw [← hm, wv_low (show 1 ≤ 2 * (w + 2) by omega)]
    omega
  unfold halfOnce
  refine WP.seq (WP.mono (halfHead_ok h hel (by omega)) fun u ⟨h8, hsi, h12, hbp, _, mu, ku⟩ => ?_)
  have hu : Ws u B Z w := h.congrR (rs := []) (by rw [mu]; exact Frm.refl _ _ _)
    (by simp) ku (by decide)
  refine WP.mono (halfTail_ok (keep := decide (m % 2 = 1)) hu he2 h8 hsi h12 (by rw [hp] at hbp; exact hbp)
    (by rw [mu]; exact hm) hmlt) fun t ⟨hv, hf, kt⟩ => ?_
  rw [mu] at hf
  exact ⟨by simpa only [decide_eq_true_eq] using hv, hf, (ku.trans kt).mono (by decide)⟩

theorem halfAlign_ok {s : State} {B : Addr} {Z w el m t : Nat} (h : Ws s B Z w)
    (hel : word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el)
    (he2 : el ≤ 8 * w) (hm : wv s.mem B (slot w aM) (2 * (w + 2)) = m)
    (hmlt : m < 2 ^ (64 * (w + (el + 7) / 8)))
    (hT : word s.mem B (8 * sT) = BitVec.ofNat 64 t) (ht : t < 2 ^ 64) :
    WP isa halfAlign s fun u =>
      wv u.mem B (slot w aM) (2 * (w + 2)) = (if t % 2 = 1 then m else m / 2) ∧
      Frm B [(slot w aM, 16 * (w + 2)), (slot w aH, 16 * (w + 2))] s.mem u.mem ∧
      Keep [.r12, .r9, .r8, .rsi, .rax, .rbp, .rdx, .r14] s u := by
  have hw2 := h.w2
  have hz := h.hZ
  have h256 := h.h256
  unfold halfAlign
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (halfHead_ok h hel (by omega))
    fun u ⟨h8, hsi, h12, _, hdi, mu, ku⟩ => ?_))
  have hs := h.scr.congr ku.2.2
  have hT' : word u.mem B (8 * sT) = BitVec.ofNat 64 t := by rw [mu]; exact hT
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun v =>
      v.gpr .rbp = mask (decide (t % 2 = 1)) ∧ v.mem = u.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hs.ld (d := 8 * sT) (by dsimp [sT, sFn]; omega), hT',
      mask_low, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht]) rfl) fun v ⟨⟨hbp, mv⟩, kv⟩ => ?_
  have ksv := ku.trans kv
  have hv : Ws v B Z w := h.congrR (rs := []) (by rw [mv, mu]; exact Frm.refl _ _ _)
    (by simp) ksv (by decide)
  refine WP.mono (halfTail_ok hv he2 ((kv.gpr (by decide)).trans h8)
    ((kv.gpr (by decide)).trans hsi) ((kv.gpr (by decide)).trans h12) hbp
    (by rw [mv, mu]; exact hm) hmlt) fun z ⟨hz, hf, kz⟩ => ?_
  rw [mv, mu] at hf
  exact ⟨by simpa only [decide_eq_true_eq] using hz, hf, (ksv.trans kz).mono (by decide)⟩

theorem sigma_bits {t : Nat} (ht1 : 1 ≤ t) (ht : t < 2 ^ 64) :
    ((BitVec.ofNat 64 t &&& 1#64) ^^^ 1#64) + 1#64 =
      BitVec.ofNat 64 (VG.Proof.Rsa.RecoveryFolded.sigma t) := by
  have hl : BitVec.ofNat 64 t &&& 1#64 = BitVec.ofNat 64 (t % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, show BitVec.toNat (1#64) = 1 from rfl,
      Nat.and_one_is_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht]
    omega
  rcases Nat.mod_two_eq_zero_or_one t with h0 | h1
  · have hs : VG.Proof.Rsa.RecoveryFolded.sigma t = 2 := by
      unfold VG.Proof.Rsa.RecoveryFolded.sigma; omega
    rw [hl, h0, hs]; rfl
  · have hs : VG.Proof.Rsa.RecoveryFolded.sigma t = 1 := by
      unfold VG.Proof.Rsa.RecoveryFolded.sigma; omega
    rw [hl, h1, hs]; rfl

theorem storeSigma_ok {s : State} {B : Addr} {Z w t : Nat} (h : Ws s B Z w)
    (hT : word s.mem B (8 * sT) = BitVec.ofNat 64 t) (ht1 : 1 ≤ t) (ht : t < 2 ^ 64) :
    WP isa (.block storeSigma) s fun u =>
      u.mem = s.mem.writeW (off B (8 * sT)) (BitVec.ofNat 64 (VG.Proof.Rsa.RecoveryFolded.sigma t)) ∧
      Keep [.rax] s u := by
  have h256 := h.h256
  unfold storeSigma
  refine WP.mono (WP.keep [.rax] (Q := fun u =>
      u.mem = s.mem.writeW (off B (8 * sT)) (BitVec.ofNat 64 (VG.Proof.Rsa.RecoveryFolded.sigma t))) (by
    xrun [State.ea, hdr, h.rdi, hdrOff, hT, sigma_bits ht1 ht,
      h.scr.ld (d := 8 * sT) (by dsimp [sT, sFn]; omega),
      h.scr.st (d := 8 * sT) (by dsimp [sT, sFn]; omega)]
    exact congrArg (fun v => s.mem.writeW (off B (8 * sT)) v) (sigma_bits ht1 ht)) rfl) fun _ h => h

theorem pair_frame {B : Addr} {w j : Nat} {m m' : Mem}
    (h : Outside B (slot w j) (16 * (w + 2)) m m') :
    Frm B (rg w [j, j + 1] []) m m' := by
  intro x hx
  have a := hx _ (rg_mem_arr (w := w) (j := j) [] (by simp))
  have b := hx _ (rg_mem_arr (w := w) (j := j + 1) [] (by simp))
  have e := slot_add w j 1
  dsimp only at a b
  exact h x (by omega)

theorem half_frame {B : Addr} {w : Nat} {m m' : Mem}
    (h : Frm B [(slot w aM, 16 * (w + 2)), (slot w aH, 16 * (w + 2))] m m') :
    Frm B (rg w [aM, aM + 1, aH, aH + 1] [sT]) m m' := by
  apply frm_halving
  intro x hx
  apply h x
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hx _ (by simp)
  · exact hx _ (by simp)

/-- Preparation preserves the unsplit exponent, computes its alignment,
and changes only six temporary arrays and the private trailing count. -/
theorem prepare_ok {s : State} {B : Addr} {Z w el m : Nat} (h : Ws s B Z w)
    (hel : word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el)
    (he1 : 1 ≤ el) (he2 : el ≤ 8 * w)
    (hm : wv s.mem B (slot w aM) (2 * (w + 2)) = m) (hm0 : 0 < m) (hm2 : m % 2 = 0)
    (hmlt : m < 2 ^ (64 * (w + (el + 7) / 8))) :
    WP isa prepare s fun u =>
      wv u.mem B (slot w aM) (2 * (w + 2)) = m / 2 ^ VG.Proof.Rsa.RecoveryFolded.sigma (VG.Spec.Rsa.splitTwos m).1 ∧
      word u.mem B (8 * sT) = BitVec.ofNat 64 (VG.Proof.Rsa.RecoveryFolded.sigma (VG.Spec.Rsa.splitTwos m).1) ∧
      Frm B (rg w [aM, aM + 1, aG, aO, aH, aH + 1] [sT]) s.mem u.mem ∧
      Keep [.r12, .r9, .r8, .rsi, .rbx, .rax, .rbp, .rdx, .r14, .r11, .r13] s u := by
  have hn := h.scr.nowrap
  have hz := h.hZ
  have hZ16 : slot w 16 ≤ 2 ^ 64 := by omega
  have hw1 := h.w1
  have hw2 := h.w2
  have hspl := VG.Proof.Rsa.splitTwos_spec hm0
  have ht1 : 1 ≤ (VG.Spec.Rsa.splitTwos m).1 := by
    by_contra hlt
    have he : (VG.Spec.Rsa.splitTwos m).1 = 0 := by omega
    rw [he, Nat.pow_zero, Nat.one_mul] at hspl
    omega
  have ht2 := VG.Proof.Rsa.splitTwos_lt hm0 hmlt
  have ht64 : (VG.Spec.Rsa.splitTwos m).1 < 2 ^ 64 := by omega
  simp only [prepare, seqs]
  refine WP.seq (WP.mono (copyExponent_ok h (o := aG) (a := aM) (by decide) (by decide) (by decide))
    fun s₁ ⟨hb₁, out₁, k₁⟩ => ?_)
  rw [hm] at hb₁
  have f₁ := pair_frame out₁
  have h₁ := h.congrG f₁ (by simp) k₁ (by decide)
  have hm₁ : wv s₁.mem B (slot w aM) (2 * (w + 2)) = m := by
    rw [f₁.rg_wv2 hZ16 (by simp) (by decide) (by decide) (by decide) (by omega), hm]
  have he₁ : word s₁.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el := by
    rw [f₁.rg_word (by decide) (by simp)]; exact hel
  refine WP.seq (WP.mono (halving_ok h₁ he₁ he1 he2 hm₁ hm0 hmlt)
    fun s₂ ⟨_, _, ht₂, raw₂, k₂⟩ => ?_)
  have f₂ := frm_halving raw₂
  have h₂ := h₁.congrG f₂ (by decide) k₂ (by decide)
  have hb₂ : wv s₂.mem B (slot w aG) (2 * (w + 2)) = m := by
    rw [f₂.rg_wv2 hZ16 (by decide) (by decide) (by decide) (by decide) (by omega), hb₁]
  refine WP.seq (WP.mono (copyExponent_ok h₂ (o := aM) (a := aG) (by decide) (by decide) (by decide))
    fun s₃ ⟨hm₃, out₃, k₃⟩ => ?_)
  rw [hb₂] at hm₃
  have f₃ := pair_frame out₃
  have h₃ := h₂.congrG f₃ (by simp) k₃ (by decide)
  have he₃ : word s₃.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el := by
    rw [f₃.rg_word (by decide) (by simp), f₂.rg_word (by decide) (by decide)]; exact he₁
  have ht₃ : word s₃.mem B (8 * sT) = BitVec.ofNat 64 (VG.Spec.Rsa.splitTwos m).1 := by
    rw [f₃.rg_word (by decide) (by simp)]; exact ht₂
  refine WP.seq (WP.mono (halfOnce_ok h₃ he₃ he2 hm₃ hmlt) fun s₄ ⟨hm₄, raw₄, k₄⟩ => ?_)
  have hne : m % 2 ≠ 1 := by omega
  rw [ite_eq_right hne] at hm₄
  have f₄ := half_frame raw₄
  have h₄ := h₃.congrG f₄ (by decide) k₄ (by decide)
  have he₄ : word s₄.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el := by
    rw [f₄.rg_word (by decide) (by decide)]; exact he₃
  have ht₄ : word s₄.mem B (8 * sT) = BitVec.ofNat 64 (VG.Spec.Rsa.splitTwos m).1 := by
    rw [raw₄.word_eq (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> simp only [slot, hdrBytes, aM, aH, sT, sFn] <;> omega) (by decide)]
    exact ht₃
  refine WP.seq (WP.mono (halfAlign_ok h₄ he₄ he2 hm₄ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hmlt)
    ht₄ ht64) fun s₅ ⟨hm₅, raw₅, k₅⟩ => ?_)
  have f₅ := half_frame raw₅
  have h₅ := h₄.congrG f₅ (by decide) k₅ (by decide)
  have ht₅ : word s₅.mem B (8 * sT) = BitVec.ofNat 64 (VG.Spec.Rsa.splitTwos m).1 := by
    rw [raw₅.word_eq (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> simp only [slot, hdrBytes, aM, aH, sT, sFn] <;> omega) (by decide)]
    exact ht₄
  refine WP.mono (storeSigma_ok h₅ ht₅ ht1 ht64) fun u ⟨mu, k₆⟩ => ?_
  have f₆ : Frm B (rg w [] [sT]) s₅.mem u.mem := by
    rw [mu]
    exact Frm.rg_of_hdr (writeW_outside _ _ _ (by decide)) [] [sT] (by decide)
  refine ⟨?_, ?_, ?_, (((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).mono (by decide)⟩
  · rw [f₆.rg_wv2 hZ16 (by decide) (by decide) (by decide) (by decide) (by omega), hm₅]
    rcases Nat.mod_two_eq_zero_or_one (VG.Spec.Rsa.splitTwos m).1 with hp | hp
    · have hs : VG.Proof.Rsa.RecoveryFolded.sigma (VG.Spec.Rsa.splitTwos m).1 = 2 := by
        unfold VG.Proof.Rsa.RecoveryFolded.sigma; omega
      rw [hs, show 2 ^ 2 = 2 * 2 from rfl, ← Nat.div_div_eq_div_mul, ite_eq_right (by omega)]
    · have hs : VG.Proof.Rsa.RecoveryFolded.sigma (VG.Spec.Rsa.splitTwos m).1 = 1 := by
        unfold VG.Proof.Rsa.RecoveryFolded.sigma; omega
      rw [hs, ite_eq_left hp]
  · rw [mu, word_writeW_self]
  · exact (((((f₁.rg_trans f₂).rg_trans f₃).rg_trans f₄).rg_trans f₅).rg_trans f₆).rg_mono
      (by decide) (by decide)

end VG.Proof.Rsa.X86_64.RecoveryFolded
