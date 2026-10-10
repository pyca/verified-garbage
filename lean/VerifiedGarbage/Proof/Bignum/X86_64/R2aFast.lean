import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
import VerifiedGarbage.Proof.Bignum.X86_64.R2wFast

/-!
# `R² mod m` by word steps with ADX on x86-64

`R2Adx.steps`: `c` word steps, `x := x 2^(64 c) mod m` (`steps_ok`), with
`R - m` kept in the accumulator; `R2Adx.fast`: `R - m` into `x` and the
accumulator, the reciprocal `v` of `m`'s top word and `w` steps, `R² mod m`
(`fast_ok`); and `R2Adx.choice`, which takes `fast` for `m`'s top bit set and
`w` a multiple of 4, `vg_rsa_public`'s computation otherwise (`choice_ok`,
`R2w.choice_ok`'s statement).
-/

namespace VG.Proof.Bignum.X86_64.R2ax

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.R2Adx
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.WordStep
open VG.Proof.Bignum.X86_64.R2w (sub_mul_mod neg_ok fastFlag old_eq)

/-! ## The steps -/

/-- After `j` of `c` steps from `s`, from `x = X`, modulo `m = M` whose top
word is `T`, with `v = ⌊(2^128 - 1) / T⌋ - 2^64` the temporary's first word. -/
structure StepsInv (s : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (c X M T j : Nat) (t : State) :
    Prop where
  scr : Scr t B Z
  rdi : t.gpr .rdi = B
  hdr : Hdr t.mem B w minv
  cnt : word t.mem B (8 * sCnt) = BitVec.ofNat 64 (c - j)
  xv : wv t.mem B (slot w aR2) w = X * 2 ^ (64 * j) % M
  nv : wv t.mem B (slot w aN) w = M
  top : (word t.mem B (slot w aN + 8 * (w - 1))).toNat = T
  rcp : (word t.mem B (slot w aTmp)).toNat = (2 ^ 128 - 1) / T - 2 ^ 64
  acc : wv t.mem B (slot w aAcc) w + M = 2 ^ (64 * w)
  frm : Frm B (r2Ranges w) s.mem t.mem
  keep : Keep mmRegs s t

theorem stepIter_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {c X M T j : Nat}
    (hZ : slot w 8 ≤ Z) (hw : 4 ≤ w) (hw4 : w % 4 = 0) (hw' : w < 2 ^ 30) (hc : c < 2 ^ 31) (hM : 0 < M)
    (hT : 2 ^ 63 ≤ T) (hj : j < c) {t : State} (hI : StepsInv s B Z w minv c X M T j t) :
    WP isa (.seq step (.block (dblCount sCnt))) t fun t' =>
      t'.zf = some (decide (j + 1 = c)) ∧ StepsInv s B Z w minv c X M T (j + 1) t' := by
  have hn := hI.scr.nowrap
  have hsl8 := slot_le (w := w) (show aN < 8 by decide)
  have hhs : ∀ j, 8 * sCnt + 8 ≤ slot w j := fun j => hdr_lt_slot w j (show sCnt < 32 by decide)
  have hZ0 := slot_le (w := w) (show 0 < 8 by decide)
  have hc0 : 8 * sCnt + 8 ≤ Z := by have := hhs 0; omega_arith
  have hlt : wv t.mem B (slot w aR2) w < wv t.mem B (slot w aN) w := by rw [hI.xv, hI.nv]; exact Nat.mod_lt _ hM
  have hst := step_ok (L := ⟨B, Z, w, minv⟩) ⟨⟨hI.scr, hI.rdi, hI.hdr⟩, hZ⟩ hw hw4 hw' (by rw [hI.top]; exact hT)
    (by rw [hI.rcp, hI.top]) hlt (by rw [hI.nv]; exact hI.acc)
  refine WP.seq (WP.mono hst fun t₁ ⟨hg₁, hv₁, ha₁, k₁⟩ => ?_)
  dsimp only at hg₁ hv₁ ha₁
  have hst₁ : Scr t₁ B Z := hg₁.1.scr
  have hdi₁ : t₁.gpr .rdi = B := hg₁.1.rdi
  have hH₁ : Hdr t₁.mem B w minv := hg₁.1.hdr
  have hcnt₁ : word t₁.mem B (8 * sCnt) = BitVec.ofNat 64 (c - j) := by
    rw [ha₁.word_eq (fun j' hj' => Or.inl (by simp at hj'; rcases hj' with rfl; exact hhs _))
      (by omega_arith), hI.cnt]
  have hld : InRegions (t₁.rd ++ t₁.wr) (off B (8 * sCnt)) 8 := hst₁.ld hc0
  have hsto : InRegions t₁.wr (off B (8 * sCnt)) 8 := hst₁.st hc0
  refine WP.mono (WP.keep [.rcx] (Q := fun t' => t'.mem = t₁.mem.writeW (off B (8 * sCnt))
      (BitVec.ofNat 64 (c - (j + 1))) ∧ t'.zf = some (decide (c - (j + 1) = 0))) (by
    xrun [State.ea, hdr, hdi₁, hdrOff, hld, hsto, hcnt₁,
      ofNat64_pred (show 1 ≤ c - j by omega_arith) (by omega_arith), ofNat64_beq_zero (show c - j - 1 < 2 ^ 64 by omega_arith)]
    exact ⟨by congr 2, by congr 1⟩) rfl) fun t' ⟨⟨hm', hz'⟩, k'⟩ => ⟨?_, ?_⟩
  · rw [hz']; congr 1; exact decide_eq_decide.mpr (by omega_arith)
  have o' : Outside B (8 * sCnt) 8 t₁.mem t'.mem := by rw [hm']; exact writeW_outside _ _ _ (by omega_arith)
  have hN₁ : wv t₁.mem B (slot w aN) w = M := by
    rw [ha₁.wv_eq (fun j' hj' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
      rcases hj' with rfl
      have := Rsa.slot_lt (w := w) (show aN < aR2 by decide); omega_arith) (by omega_arith), hI.nv]
  have hT₁ : (word t₁.mem B (slot w aN + 8 * (w - 1))).toNat = T := by
    rw [ha₁.word_eq (fun j' hj' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
      rcases hj' with rfl
      have := Rsa.slot_lt (w := w) (show aN < aR2 by decide); omega_arith) (by omega_arith), hI.top]
  have hsv := slot_le (w := w) (show aTmp < 8 by decide)
  have hV₁ : (word t₁.mem B (slot w aTmp)).toNat = (2 ^ 128 - 1) / T - 2 ^ 64 := by
    rw [ha₁.word_eq (fun j' hj' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
      rcases hj' with rfl
      have := Rsa.slot_lt (w := w) (show aTmp < aR2 by decide); omega_arith) (by omega_arith), hI.rcp]
  have hst8 := slot_le (w := w) (show aAcc < 8 by decide)
  have hC₁ : wv t₁.mem B (slot w aAcc) w = wv t.mem B (slot w aAcc) w := by
    rw [ha₁.wv_eq (fun j' hj' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
      rcases hj' with rfl
      have := Rsa.slot_lt (w := w) (show aAcc < aR2 by decide); omega_arith) (by omega_arith)]
  have hH' : Hdr t'.mem B w minv := by rw [hm']; exact Hdr.store hH₁ (by decide) (by decide) _
  refine ⟨hst₁.congr k'.2.2, (k'.gpr (by decide)).trans hdi₁, hH', by rw [hm', word_writeW_self], ?_, ?_, ?_, ?_,
    ?_, ?_, ((hI.keep.trans k₁).trans k').mono (by decide)⟩
  · rw [o'.wv (by have := hhs aR2; omega_arith) (by have := slot_le (w := w) (show aR2 < 8 by decide); omega_arith), hv₁,
      hI.xv, hI.nv, Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.pow_add, show 64 * j + 64 = 64 * (j + 1) by omega_arith]
  · rw [o'.wv (by have := hhs aN; omega_arith) (by omega_arith), hN₁]
  · rw [o'.word (by have := hhs aN; omega_arith) (by omega_arith), hT₁]
  · rw [o'.word (by have := hhs aTmp; omega_arith) (by omega_arith), hV₁]
  · rw [o'.wv (by have := hhs aAcc; omega_arith) (by omega_arith), hC₁]; exact hI.acc
  · exact (hI.frm.trans (Frm.of_arrays ha₁ (by simp [r2Ranges]))).trans (Frm.of_outside o' (by simp [r2Ranges]))

theorem steps_eq : steps =
    .seq (.block [.store (hdr sCnt) .rcx]) (.loop (.seq step (.block (dblCount sCnt))) .ne) := rfl

/-- `steps`' start: the count `c` into `sCnt`. -/
theorem stepsStart_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {c : Nat}
    (hcx : s.gpr .rcx = BitVec.ofNat 64 c) (hO : wv s.mem B (slot w aR2) w < wv s.mem B (slot w aN) w)
    (hv : (word s.mem B (slot w aTmp)).toNat =
      (2 ^ 128 - 1) / (word s.mem B (slot w aN + 8 * (w - 1))).toNat - 2 ^ 64)
    (hc : wv s.mem B (slot w aAcc) w + wv s.mem B (slot w aN) w = 2 ^ (64 * w)) :
    WP isa (.block [.store (hdr sCnt) .rcx]) s (StepsInv s B Z w minv c (wv s.mem B (slot w aR2) w)
      (wv s.mem B (slot w aN) w) (word s.mem B (slot w aN + 8 * (w - 1))).toNat 0) := by
  have hn := hs.nowrap
  have hsl8 := slot_le (w := w) (show aN < 8 by decide)
  have hsr8 := slot_le (w := w) (show aR2 < 8 by decide)
  have hsv := slot_le (w := w) (show aTmp < 8 by decide)
  have hhs : ∀ j, 8 * sCnt + 8 ≤ slot w j := fun j => hdr_lt_slot w j (show sCnt < 32 by decide)
  have hZ0 := slot_le (w := w) (show 0 < 8 by decide)
  have hc0 : 8 * sCnt + 8 ≤ Z := by have := hhs 0; omega_arith
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off B (8 * sCnt)) (s.gpr .rcx))
    (by xrun [State.ea, hdr, hdi, hdrOff, hs.st hc0]) rfl) fun s₁ ⟨hm₁, k₁⟩ => ?_
  have o₁ : Outside B (8 * sCnt) 8 s.mem s₁.mem := by rw [hm₁]; exact writeW_outside _ _ _ (by omega_arith)
  exact ⟨hs.congr k₁.2.2, (k₁.gpr (by decide)).trans hdi, by rw [hm₁]; exact Hdr.store hH (by decide) (by decide) _,
      by rw [hm₁, word_writeW_self, hcx, Nat.sub_zero],
      by rw [o₁.wv (by have := hhs aR2; omega_arith) (by omega_arith), Nat.mul_zero, Nat.pow_zero, Nat.mul_one,
        Nat.mod_eq_of_lt hO],
      o₁.wv (by have := hhs aN; omega_arith) (by omega_arith),
      by rw [o₁.word (by have := hhs aN; omega_arith) (by omega_arith)],
      by rw [o₁.word (by have := hhs aTmp; omega_arith) (by omega_arith)]; exact hv,
      by rw [o₁.wv (d := slot w aAcc) (k := w) (by have := hhs aAcc; omega_arith)
          (by have := slot_le (w := w) (show aAcc < 8 by decide); omega_arith)]; exact hc,
      Frm.of_outside o₁ (by simp [r2Ranges]), k₁.mono (by decide)⟩

/-- What `steps` leaves, from `StepsInv`. -/
theorem StepsInv.post {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {c X M T : Nat} {t : State}
    (hZ : slot w 8 ≤ Z) (hI : StepsInv s B Z w minv c X M T c t) :
    wv t.mem B (slot w aR2) w = X * 2 ^ (64 * c) % M ∧ wv t.mem B (slot w aN) w = M ∧
      (word t.mem B (slot w aN) = word s.mem B (slot w aN)) ∧
      Frm B (r2Ranges w) s.mem t.mem ∧ Good t B Z w minv ∧ Keep mmRegs s t := by
  have hn := hI.scr.nowrap
  have hsl8 := slot_le (w := w) (show aN < 8 by decide)
  exact ⟨hI.xv, hI.nv, by
      rw [hI.frm.word_eq (fun r hr => by
        have := r2Ranges_arr w (j := aN) (by decide) (by decide) (by decide) r hr; omega_arith) (by omega_arith)],
    hI.frm, ⟨hI.scr, hI.rdi, hI.hdr⟩, hI.keep⟩

/-- `steps`: `c ≥ 1` word steps (the count in `rcx`), `x := x 2^(64 c) mod m`. -/
theorem steps_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 4 ≤ w) (hw4 : w % 4 = 0)
    (hw' : w < 2 ^ 30) {c : Nat} (hc : 1 ≤ c) (hc' : c < 2 ^ 31) (hcx : s.gpr .rcx = BitVec.ofNat 64 c)
    (hT : 2 ^ 63 ≤ (word s.mem B (slot w aN + 8 * (w - 1))).toNat)
    (hv : (word s.mem B (slot w aTmp)).toNat =
      (2 ^ 128 - 1) / (word s.mem B (slot w aN + 8 * (w - 1))).toNat - 2 ^ 64)
    (hO : wv s.mem B (slot w aR2) w < wv s.mem B (slot w aN) w)
    (hcc : wv s.mem B (slot w aAcc) w + wv s.mem B (slot w aN) w = 2 ^ (64 * w)) :
    WP isa steps s fun t =>
      wv t.mem B (slot w aR2) w = wv s.mem B (slot w aR2) w * 2 ^ (64 * c) % wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w aN) w = wv s.mem B (slot w aN) w ∧
      (word t.mem B (slot w aN) = word s.mem B (slot w aN)) ∧
      Frm B (r2Ranges w) s.mem t.mem ∧ Good t B Z w minv ∧ Keep mmRegs s t := by
  have hM : 0 < wv s.mem B (slot w aN) w := Nat.lt_of_le_of_lt (Nat.zero_le _) hO
  rw [steps_eq]
  refine WP.seq (WP.mono (stepsStart_ok hs hdi hH hZ hcx hO hv hcc) fun s₁ h0 => ?_)
  exact wp_upto (a := 0) (N := c) (by omega_arith) _ (fun j _ hj t hI => stepIter_ok hZ hw hw4 hw' hc' hM hT hj hI)
    (fun t hI => hI.post hZ) h0

/-! ## `R² mod m` by word steps -/

theorem fast_eq : fast = .seq (.block [.mov .rbx (.mem (hdr (sArr aR2))),
      .mov .r10 (.mem (hdr (sArr aN))), .mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aTmp))),
      .mov32 .rbp (.imm 0)])
    (.seq (wordLoop 0 R2Words.negBody) (.seq (.block [.mov .r8 (.reg .rbx), .mov .rbx (.mem (hdr (sArr aAcc)))])
      (.seq R2Words.copyBack
        (.seq (.block [.mov .rbx (.mem (hdr (sArr aR2))), .mov .r8 (.mem (hdr (sArr aTmp)))])
          (.seq R2Words.recip (.seq (.block [.mov .rcx (.mem (hdr sW))]) steps)))))) := rfl

/-- `fast`: `R² mod m`, for the odd `m` of `w` words (a multiple of 4), its
top word at least `2^63`. -/
theorem fast_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 4 ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem B (slot w aN) w = N) (hodd : N % 2 = 1)
    (hT : 2 ^ 63 ≤ (word s.mem B (slot w aN + 8 * (w - 1))).toNat) (h4 : w % 4 = 0) :
    WP isa fast s fun t => Good t B Z w minv ∧
      wv t.mem B (slot w aR2) w < N ∧ wv t.mem B (slot w aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      Frm B (r2Ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hw' : w < 2 ^ 31 := by omega_arith
  have hs := hg.scr
  have hnw := hs.nowrap
  have hN0 : 0 < N := by omega_arith
  have hNR : N < 2 ^ (64 * w) := hn ▸ wv_lt _ _ _ _
  -- `m > R / 2`: its top bit is set, and it is odd.
  have hhalf : 2 ^ (64 * w) < 2 * N := by
    have e : N = wv s.mem B (slot w aN) (w - 1) +
        2 ^ (64 * (w - 1)) * (word s.mem B (slot w aN + 8 * (w - 1))).toNat := by
      rw [← hn, show w = (w - 1) + 1 by omega_arith, wv_succ, show w - 1 + 1 - 1 = w - 1 by omega_arith]
    have hp : 2 ^ (64 * w) = 2 * (2 ^ (64 * (w - 1)) * 2 ^ 63) := by
      rw [← Nat.pow_add, show 64 * w = 1 + (64 * (w - 1) + 63) by omega_arith, Nat.pow_add, Nat.pow_one]
    have hle := Nat.mul_le_mul_left (2 ^ (64 * (w - 1))) hT
    have hev : 2 ^ (64 * (w - 1)) * 2 ^ 63 % 2 = 0 := by
      rw [Nat.mul_mod, show 2 ^ 63 % 2 = 0 by decide, Nat.mul_zero, Nat.zero_mod]
    omega_arith
  have hsx := slot_le (w := w) (show aR2 < 8 by decide)
  have hsm := slot_le (w := w) (show aN < 8 by decide)
  have hsv := slot_le (w := w) (show aTmp < 8 by decide)
  have hsa := slot_le (w := w) (show aAcc < 8 by decide)
  have sXM := Rsa.slot_lt (w := w) (show aN < aR2 by decide)
  have sXV := Rsa.slot_lt (w := w) (show aTmp < aR2 by decide)
  have sMV := Rsa.slot_lt (w := w) (show aN < aTmp by decide)
  have sXA := Rsa.slot_lt (w := w) (show aAcc < aR2 by decide)
  have sMA := Rsa.slot_lt (w := w) (show aN < aAcc by decide)
  have sAV := Rsa.slot_lt (w := w) (show aAcc < aTmp by decide)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  rw [fast_eq]
  refine WP.seq (WP.mono (WP.keep [.rbx, .r10, .r12, .r8, .rbp] (Q := fun t =>
      t.gpr .rbx = off B (slot w aR2) ∧ t.gpr .r10 = off B (slot w aN) ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r8 = off B (slot w aTmp) ∧ t.gpr .rbp = mask false ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr aR2) (by decide), hl (sArr aN) (by decide), hl sW (by decide),
      hl (sArr aTmp) (by decide), hg.hdr.harr aR2 (by decide), hg.hdr.harr aN (by decide), hg.hdr.hw,
      hg.hdr.harr aTmp (by decide)]) rfl)
    fun t₁ ⟨⟨h1bx, h110, h112, _, h1bp, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have hM0 : 0 < wv t₁.mem B (slot w aN) w := by rw [hm₁, hn]; exact hN0
  have e1 : slot w aR2 + 8 * w ≤ Z := by omega_arith
  have e2 : slot w aN + 8 * w ≤ Z := by omega_arith
  have sM : slot w aR2 + 8 * w ≤ slot w aN ∨ slot w aN + 8 * w ≤ slot w aR2 := by omega_arith
  refine WP.seq (WP.mono (neg_ok hs₁ h1bx h110 h112 h1bp (by omega_arith) hw' e1 e2 sM hM0)
    fun t₂ ⟨hx₂, ho₂, k₂⟩ => ?_)
  rw [hm₁, hn] at hx₂
  have hs₂ := hs₁.congr k₂.2.2
  have k₁₂ := k₁.trans k₂
  -- `mc := x`.
  have hdi₂ : t₂.gpr .rdi = B := (k₁₂.gpr (by decide)).trans hg.rdi
  have hH₂ : Hdr t₂.mem B w minv :=
    (Arrays.of_outside (j := aR2) (List.mem_singleton_self _) ho₂ (Nat.le_refl _) (by omega_arith)).hdr
      (hm₁ ▸ hg.hdr)
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off B (8 * i)) 8 := fun i hi =>
    hs₂.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  refine WP.seq (WP.mono (WP.keep [.r8, .rbx] (Q := fun t => t.gpr .r8 = off B (slot w aR2) ∧
      t.gpr .rbx = off B (slot w aAcc) ∧ t.mem = t₂.mem) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ (sArr aAcc) (by decide), hH₂.harr aAcc (by decide),
      (k₂.gpr (by decide)).trans h1bx]) rfl) fun t₃ ⟨⟨h38, h3bx, hm₃⟩, k₃⟩ => ?_)
  refine WP.seq ?_
  unfold R2Words.copyBack
  refine WP.seq (WP.mono (WP.keep [.rsi] (Q := fun t => t.gpr .rsi = off B (slot w aR2) ∧ t.mem = t₃.mem)
    (by xrun [h38]) rfl) fun t₄ ⟨⟨h4si, hm₄⟩, k₄⟩ => ?_)
  have hs₄ := hs₂.congr (k₄.2.2.trans k₃.2.2)
  have k₃₄ := k₃.trans k₄
  have h412 : t₄.gpr .r12 = BitVec.ofNat 64 w := (k₃₄.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h112)
  have hsepw : ∀ j < w, ∀ b < 8, ofs B (off B (slot w aR2 + 8 * j) + BitVec.ofNat 64 b) < slot w aAcc ∨
      slot w aAcc + 8 * w ≤ ofs B (off B (slot w aR2 + 8 * j) + BitVec.ofNat 64 b) := fun j hj b hb => by
    rw [ofs_off B (by omega_arith)]; omega_arith
  refine WP.mono (copyWords_ok (S := B) (D := B) h4si ((k₄.gpr (by decide)).trans h3bx) h412
    (by omega_arith) hw' (by omega_arith) (fun j hj => hs₄.ld (by omega_arith)) (fun j hj => hs₄.st (by omega_arith))
    hsepw) fun t₅ ⟨hc₅, _, ho₅, k₅⟩ => ?_
  rw [hm₄, hm₃, hx₂] at hc₅
  have hs₅ := hs₄.congr k₅.2.2
  have hm₂₄ : t₄.mem = t₂.mem := hm₄.trans hm₃
  rw [hm₂₄] at ho₅
  -- `v`.
  have hH₅ : Hdr t₅.mem B w minv :=
    (Arrays.of_outside (j := aAcc) (List.mem_singleton_self _) ho₅ (Nat.le_refl _) (by omega_arith)).hdr hH₂
  have hdi₅ : t₅.gpr .rdi = B := (k₅.gpr (by decide)).trans ((k₃₄.gpr (by decide)).trans hdi₂)
  have hl₅ : ∀ i < 32, InRegions (t₅.rd ++ t₅.wr) (off B (8 * i)) 8 := fun i hi =>
    hs₅.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  refine WP.seq (WP.mono (WP.keep [.rbx, .r8] (Q := fun t => t.gpr .rbx = off B (slot w aR2) ∧
      t.gpr .r8 = off B (slot w aTmp) ∧ t.mem = t₅.mem) (by
    xrun [State.ea, hdr, hdi₅, hdrOff, hl₅ (sArr aR2) (by decide), hl₅ (sArr aTmp) (by decide),
      hH₅.harr aR2 (by decide), hH₅.harr aTmp (by decide)]) rfl) fun t₆ ⟨⟨_, h68, hm₆⟩, k₆⟩ => ?_)
  have hs₆ := hs₅.congr k₆.2.2
  have k₄₆ := k₅.trans k₆
  have h610 : t₆.gpr .r10 = off B (slot w aN) :=
    (k₄₆.gpr (by decide)).trans ((k₃₄.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h110))
  have h612 : t₆.gpr .r12 = BitVec.ofNat 64 w := (k₄₆.gpr (by decide)).trans h412
  have eV : slot w aTmp + 8 ≤ Z := by omega_arith
  have hN₆ : wv t₆.mem B (slot w aN) w = N := by
    rw [hm₆, ho₅.wv (by omega_arith) (by omega_arith), ho₂.wv (by omega_arith) (by omega_arith), hm₁, hn]
  have hT₆ : 2 ^ 63 ≤ (word t₆.mem B (slot w aN + 8 * (w - 1))).toNat := by
    rw [hm₆, ho₅.word (by omega_arith) (by omega_arith), ho₂.word (by omega_arith) (by omega_arith), hm₁]; exact hT
  refine WP.seq (WP.mono (R2w.recip_ok hs₆ h610 h612 h68 (by omega_arith) e2 eV hT₆) fun t₇ ⟨hm₇, k₇⟩ => ?_)
  have hvlt : (2 ^ 128 - 1) / (word t₆.mem B (slot w aN + 8 * (w - 1))).toNat - 2 ^ 64 < 2 ^ 64 := by
    have : (2 ^ 128 - 1) / (word t₆.mem B (slot w aN + 8 * (w - 1))).toNat < 2 ^ 65 := by
      rw [Nat.div_lt_iff_lt_mul (by omega_arith)]; omega_arith
    omega_arith
  have o₇ : Outside B (slot w aTmp) 8 t₆.mem t₇.mem := by rw [hm₇]; exact writeW_outside _ _ _ (by omega_arith)
  have hs₇ := hs₆.congr k₇.2.2
  have hdi₇ : t₇.gpr .rdi = B := (k₇.gpr (by decide)).trans ((k₆.gpr (by decide)).trans hdi₅)
  have hH₇ : Hdr t₇.mem B w minv :=
    (Arrays.of_outside (j := aTmp) (List.mem_singleton_self _) o₇ (Nat.le_refl _) (by omega_arith)).hdr
      (hm₆ ▸ hH₅)
  have hl₇ : ∀ i < 32, InRegions (t₇.rd ++ t₇.wr) (off B (8 * i)) 8 := fun i hi =>
    hs₇.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 w ∧ t.mem = t₇.mem)
    (by xrun [State.ea, hdr, hdi₇, hdrOff, hl₇ sW (by decide), hH₇.hw]) rfl) fun t₈ ⟨⟨h8cx, hm₈⟩, k₈⟩ => ?_)
  -- The values before the steps.
  have hN₈ : wv t₈.mem B (slot w aN) w = N := by rw [hm₈, o₇.wv (by omega_arith) (by omega_arith), hN₆]
  have hT₈ : 2 ^ 63 ≤ (word t₈.mem B (slot w aN + 8 * (w - 1))).toNat := by
    rw [hm₈, o₇.word (by omega_arith) (by omega_arith)]; exact hT₆
  have hV₈ : (word t₈.mem B (slot w aTmp)).toNat =
      (2 ^ 128 - 1) / (word t₈.mem B (slot w aN + 8 * (w - 1))).toNat - 2 ^ 64 := by
    rw [hm₈, o₇.word (d := slot w aN + 8 * (w - 1)) (by omega_arith) (by omega_arith), hm₇, word_writeW_self,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt]
  have hX₈ : wv t₈.mem B (slot w aR2) w = 2 ^ (64 * w) - N := by
    rw [hm₈, o₇.wv (by omega_arith) (by omega_arith), hm₆, ho₅.wv (by omega_arith) (by omega_arith), hx₂]
  have hC₈ : wv t₈.mem B (slot w aAcc) w = 2 ^ (64 * w) - N := by
    rw [hm₈, o₇.wv (by omega_arith) (by omega_arith), hm₆, hc₅]
  have hO₈ : wv t₈.mem B (slot w aR2) w < wv t₈.mem B (slot w aN) w := by rw [hX₈, hN₈]; omega
  have hsp := steps_ok (hs₇.congr k₈.2.2) ((k₈.gpr (by decide)).trans hdi₇) (hm₈ ▸ hH₇) hZ hw h4 hw30
    (c := w) (by omega_arith) (by omega_arith) h8cx hT₈ hV₈ hO₈ (by rw [hC₈, hN₈]; omega_arith)
  refine WP.mono hsp fun t ⟨hx, _, _, hf, hgt, kt⟩ => ⟨hgt, ?_, ?_, ?_, ?_⟩
  · rw [hx, hN₈]; exact Nat.mod_lt _ hN0
  · rw [hx, hX₈, hN₈, sub_mul_mod (Nat.le_of_lt hNR), Nat.mod_mod]
  · have f₂ : Frm B (r2Ranges w) s.mem t₂.mem := by
      rw [← hm₁]; exact Frm.of_arrays (Arrays.of_outside (j := aR2) (List.mem_singleton_self _) ho₂
        (Nat.le_refl _) (by omega_arith)) (by simp [r2Ranges])
    have f₅ : Frm B (r2Ranges w) t₂.mem t₅.mem :=
      Frm.of_arrays1 (Arrays.of_outside (j := aAcc) (List.mem_singleton_self _) ho₅ (Nat.le_refl _) (by omega_arith))
        (by simp [r2Ranges])
    have f₇ : Frm B (r2Ranges w) t₆.mem t₇.mem :=
      Frm.of_arrays1 (Arrays.of_outside (j := aTmp) (List.mem_singleton_self _) o₇ (Nat.le_refl _) (by omega_arith))
        (by simp [r2Ranges])
    exact ((((f₂.trans f₅).trans (by rw [hm₆]; exact Frm.refl _ _ _)).trans f₇).trans
      (by rw [hm₈]; exact Frm.refl _ _ _)).trans hf
  · exact ((((((k₁₂.trans k₃₄).trans k₅).trans k₆).trans k₇).trans k₈).trans kt).mono (by decide)

/-- `choice`: `R² mod m` for the odd `m` of `w ≥ 2` words, its top word not
zero, by word steps when `m`'s top bit is set and `w` is a multiple of 4 and
by `vg_rsa_public`'s computation otherwise: `r2_ok`'s result. -/
theorem choice_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem B (slot w aN) w = N) (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h10 : s.gpr .r10 = off B (slot w aN)) (hodd : N % 2 = 1)
    (hlo : 2 ^ (64 * (w - 1)) ≤ N) :
    WP isa (R2Adx.choice M.mm) s fun t => Good t B Z w minv ∧
      wv t.mem B (slot w aR2) w < N ∧ wv t.mem B (slot w aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      Frm B (r2Ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := hg.scr
  have hnw := hs.nowrap
  have hsm := slot_le (w := w) (show aN < 8 by decide)
  have hd8 : slot w aN + 8 * (w - 1) + 8 ≤ Z := by omega_arith
  have hld : InRegions (s.rd ++ s.wr) (off B (slot w aN + 8 * (w - 1))) 8 := hs.ld hd8
  unfold R2Adx.choice
  refine WP.seq (WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.zf = some (decide (2 ^ 63 ≤
      (word s.mem B (slot w aN + 8 * (w - 1))).toNat ∧ w % 4 = 0)) ∧ t.mem = s.mem) (by
    unfold R2Words.fastTest
    xrun [State.ea, ix, addrm8 h10 h12 (by omega_arith), hld]
    rw [h12]
    exact fastFlag _ (by omega_arith)) rfl) fun t₁ ⟨⟨hz₁, hm₁⟩, k₁⟩ => ?_)
  have hg₁ : Good t₁ B Z w minv := ⟨hs.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, hm₁ ▸ hg.hdr⟩
  have hn₁ : wv t₁.mem B (slot w aN) w = N := by rw [hm₁, hn]
  have hinv₁ : ((word t₁.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by rw [hm₁]; exact hinv
  generalize hP : decide (2 ^ 63 ≤ (word s.mem B (slot w aN + 8 * (w - 1))).toNat ∧ w % 4 = 0) = P at hz₁
  refine WP.ite P (by simp only [eval, hz₁]) (fun hc => ?_) (fun hc => ?_)
  · obtain ⟨hT, h4⟩ := of_decide_eq_true (hP.trans hc)
    refine WP.mono (fast_ok hg₁ hZ (by omega_arith) hw30 hn₁ hodd (by rw [hm₁]; exact hT) h4)
      fun t ⟨h1, h2, h3, h4', h5⟩ => ⟨h1, h2, h3, by rw [← hm₁]; exact h4', (k₁.trans h5).mono (by decide)⟩
  · rw [old_eq]
    refine WP.mono (r2_ok M hg₁ hZ hw hw30 hn₁ hinv₁ ((k₁.gpr (by decide)).trans h12)
      ((k₁.gpr (by decide)).trans h10) hodd hlo)
      fun t ⟨h1, h2, h3, h4', h5⟩ => ⟨h1, h2, h3, by rw [← hm₁]; exact h4', (k₁.trans h5).mono (by decide)⟩

end VG.Proof.Bignum.X86_64.R2ax
