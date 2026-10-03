import VerifiedGarbage.Proof.Bignum.X86_64.CrtFront

/-!
# RSA with the CRT on x86-64: from the checks to the result

`q`'s phase, `p`'s, and `m = m_q + q h` written out masked (`back_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

theorem finish_out : finish = finishSum ++ outStepsArr Public.aAcc := rfl

/-- A factor of an odd `N`, its cofactor below `N`: odd and above 1. -/
theorem factor_facts {P Q N : Nat} (h : P * Q = N) (hP : P < N) (hN : N % 2 = 1) : 1 < Q ∧ Q % 2 = 1 := by
  have hodd := odd_of_mul_odd (by rw [Nat.mul_comm]; exact h) hN
  refine ⟨?_, hodd⟩
  rcases Nat.lt_or_ge 1 Q with h1 | h1
  · exact h1
  · rcases (show Q = 0 ∨ Q = 1 by omega) with rfl | rfl
    · rw [Nat.mul_zero] at h; omega
    · rw [Nat.mul_one] at h; omega

/-- The CRT's result for a valid key. -/
def crtResult (P Q dp dq QI C : Nat) : Nat :=
  C ^ dq % Q + Q * ((((C ^ dp % P : Nat) : Int) - (C ^ dq % Q : Nat)) * QI % (P : Int)).toNat

theorem decryptCrt_eq {N P Q dp dq QI C : Nat} :
    Spec.Rsa.decryptCrt N P Q dp dq QI C =
      if C < N ∧ P * Q = N ∧ QI < P then some (crtResult P Q dp dq QI C) else none := by
  simp only [Spec.Rsa.decryptCrt, crtResult, VG.Proof.Bignum.powMod_eq]

theorem keepsHdr_x {o wx : Nat} (ho : 8 * 32 ≤ o) : KeepsHdr (xRange o wx) := keepsHdr_ge (by simp only [xRange]; omega)

theorem keepsHdr_pRanges (w : Nat) : ∀ r ∈ pRanges w, KeepsHdr r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact keepsHdr_gRanges w r hr
  · rw [List.mem_singleton.mp hr]
    exact keepsHdr_ge (by have := hdr_lt_slot w Public.aX (show 31 < 32 by decide); simp only; omega)

/-- From the checks: both phases, and `m = m_q + q h` written out masked. -/
theorem back_ok (M : Mont) {s t₀ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs (qPhase M.mm ++ pPhase M.mm ++ finish)) t₀ fun t => MainPost s t B Z k op
      (if Mk then crtResult (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dpb) (Spec.Rsa.os2ip dqb)
        (Spec.Rsa.os2ip qib) (Spec.Rsa.os2ip xb) else 0) Mk := by
  obtain ⟨hodd, hN1, _⟩ := valid_facts hv h.k1
  have h256 : 256 ^ (k - 1) ≤ Spec.Rsa.os2ip nb := by
    simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, decide_eq_true_eq] at hv; exact hv.2
  have hNlt : Spec.Rsa.os2ip nb < 2 ^ (64 * ((k + 7) / 8)) := by
    have := os2ip_lt nb
    rw [h.nl, pow256_eq] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))
  have hPN : Spec.Rsa.os2ip pb < Spec.Rsa.os2ip nb := by
    have := os2ip_lt pb
    rw [h.pbl] at this
    exact Nat.lt_of_lt_of_le this ((Nat.pow_le_pow_right (by decide) (by have := h.pl2; omega)).trans h256)
  have hQN : Spec.Rsa.os2ip qb < Spec.Rsa.os2ip nb := by
    have := os2ip_lt qb
    rw [h.qbl] at this
    exact Nat.lt_of_lt_of_le this ((Nat.pow_le_pow_right (by decide) (by have := h.ql2; omega)).trans h256)
  have hk1 := h.k1
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  have hpl1 := h.pl1
  have hql1 := h.ql1
  have hZq := h.z
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize hQIe : Spec.Rsa.os2ip qib = QI at *
  -- What the mask gives.
  have hMk' : Mk = true → C < N ∧ P * Q = N ∧ QI < P := fun hm => by
    rw [hMk] at hm
    simp only [keyMask, Bool.and_eq_true, decide_eq_true_eq] at hm
    exact ⟨hm.1.1, hm.1.2, hm.2⟩
  have hP' : 1 < (if Mk then P else 3) ∧ (if Mk then P else 3) % 2 = 1 := by
    cases Mk
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨by decide, by decide⟩
    · obtain ⟨_, hpq, _⟩ := hMk' rfl
      simp only [↓reduceIte]
      exact factor_facts (by rw [Nat.mul_comm]; exact hpq) hQN hodd
  have hQ' : 1 < (if Mk then Q else 3) ∧ (if Mk then Q else 3) % 2 = 1 := by
    cases Mk
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨by decide, by decide⟩
    · obtain ⟨_, hpq, _⟩ := hMk' rfl
      simp only [↓reduceIte]
      exact factor_facts hpq hPN hodd
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hP8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega
  have hQ8 : 256 ≤ slot (wsWords ql) 8 := by unfold slot hdrBytes; omega
  have hwp2 : 2 ≤ wsWords pl := by unfold wsWords; omega
  have hwq2 : 2 ≤ wsWords ql := by unfold wsWords; omega
  have hwp := wsWords_le (len := pl) (w := (k + 7) / 8) (by omega) (by omega)
  have hwq := wsWords_le (len := ql) (w := (k + 7) / 8) (by omega) (by omega)
  have hZ : slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ at hZq; omega
  have hh₀ : ∀ i < 32, hFixed i = true → word t₀.mem B (8 * i) = word s.mem B (8 * i) := hr.hfix
  rw [List.append_assoc]
  -- `m_q`.
  refine wp_seqs_append (by simp [qPhase]) (by simp [pPhase]) ?_
  refine WP.mono (qPhase_ok M hr.good (by omega) (by omega) (by unfold offQ; omega) hZq hwq2 hwq hr.wsQ hr.qws
    hr.nv hodd hN1 hr.xm hr.qxv hQ'.1 hQ'.2 (by rw [hh₀ _ (by decide) (by decide)]; exact h.hDq)
    (by rw [hh₀ _ (by decide) (by decide), h.dql]; exact h.hQl) (by rw [h.dql]; omega)
    (by rw [h.dql]; omega) (h.dq.congrK hr.iscr hr.keep))
    fun t₁ ⟨hg₁, hwsq₁, hxq₁, hlt₁, hv₁, f₁, k₁⟩ => ?_
  have hz : B.toNat + slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega
  have hloq : slot ((k + 7) / 8) 8 ≤ offQ ((k + 7) / 8) pl := by unfold offQ; omega
  have f₁' : Frm B (pRanges ((k + 7) / 8) ++ [xRange (offQ ((k + 7) / 8) pl) (wsWords ql)]) t₀.mem t₁.mem :=
    f₁.mono fun r hr => (List.mem_append.mp hr).elim
      (fun h' => List.mem_append_left _ (List.mem_append_left _ h')) (fun h' => List.mem_append_right _ h')
  have hb₁ : ∀ i < 32, i ≠ Crt.sD → i ≠ Public.sCnt → word t₁.mem B (8 * i) = word t₀.mem B (8 * i) :=
    fun i hi h1 h2 => f₁'.px_hdr hloq hi h1 h2
  -- `p`'s workspace, below `q`'s, is kept.
  have hpk : ∀ d, slot ((k + 7) / 8) 8 ≤ d → d + 8 ≤ offQ ((k + 7) / 8) pl →
      word t₁.mem B d = word t₀.mem B d := fun d hd hd' => f₁.word_eq (fun r hr => by
    have := pxR_bound (wx := wsWords ql) hloq r (f₁'.mono (fun _ h => h) |> fun _ =>
      (List.mem_append.mp hr).elim (fun h' => List.mem_append_left _ (List.mem_append_left _ h'))
        (fun h' => List.mem_append_right _ h'))
    rcases List.mem_append.mp hr with hr | hr
    · exact Or.inr (by have := pRanges_le ((k + 7) / 8) r (List.mem_append_left _ hr); omega)
    · rw [List.mem_singleton.mp hr]; exact Or.inl (by simp only [xRange]; omega)) (by omega)
  have hpw₁ : ∀ i < 32, word t₁.mem (off B (offP ((k + 7) / 8))) (8 * i) =
      word t₀.mem (off B (offP ((k + 7) / 8))) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hpk _ (by unfold offP; omega) (by unfold offP offQ; omega)
  have hpv₁ : ∀ d m, d + 8 * m ≤ slot (wsWords pl) 8 → wv t₁.mem (off B (offP ((k + 7) / 8))) d m =
      wv t₀.mem (off B (offP ((k + 7) / 8))) d m := fun d m hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hpk _ (by unfold offP; omega) (by unfold offP offQ; omega)
  have hXp₁ : XVals t₁ B (offP ((k + 7) / 8)) (wsWords pl) mp (if Mk then P else 3) :=
    ⟨by rw [hpv₁ _ _ (by have := slot_le (w := wsWords pl) (show Public.aN < 8 by decide); omega)]; exact hr.pxv.n,
     by rw [word_off, hpk _ (by unfold offP; omega) (by
          have := slot_le (w := wsWords pl) (show Public.aN < 8 by decide); unfold offP offQ; omega), ← word_off]
        exact hr.pxv.inv,
     by rw [hpv₁ _ _ (by have := slot_le (w := wsWords pl) (show Public.aOne < 8 by decide); omega)]
        exact hr.pxv.one⟩
  have i01 : InScr B Z t₀.mem t₁.mem := InScr.of_frm f₁' fun r hr => by
    have := pxR_bound (wx := wsWords ql) hloq r hr; omega
  have hN₁ := hr.nv.of_frm f₁ hloq hz (by omega)
  have hXm₁ : wv t₁.mem B (slot ((k + 7) / 8) Public.aXm) ((k + 7) / 8) % N = C * 2 ^ (64 * ((k + 7) / 8)) % N := by
    rw [f₁.gx_wv hloq hz (by decide) (by decide) (by decide) (by decide)]; exact hr.xm
  -- `h`.
  refine wp_seqs_append (by simp [pPhase]) (by simp [finish]) ?_
  refine WP.mono (pPhase_ok M (X := if Mk then P else 3) (c := Mk) (eb := dpb) (qib := qib) (oq := offQ ((k + 7) / 8) pl) (wq := wsWords ql) hg₁ (by omega) (by omega)
    (show slot ((k + 7) / 8) 8 ≤ offP ((k + 7) / 8) from le_refl _) (by unfold offQ offP; omega) hZq hwp2 hwp
    (by omega) hwq (by rw [hb₁ _ (by decide) (by decide) (by decide)]; exact hr.wsP)
    (hr.pws.of_words fun i hi => hpw₁ i (by omega)) (by rw [hb₁ _ (by decide) (by decide) (by decide)]; exact hr.wsQ)
    hwsq₁ hN₁ hodd hN1 hXm₁ hXp₁ hP'.1 hP'.2 (by rw [hpw₁ _ (by decide)]; exact hr.pmask)
    (fun hm => by obtain ⟨_, hpq, _⟩ := hMk' hm; simp only [hm, ↓reduceIte]; exact ⟨Q, hpq.symm⟩)
    (by rw [hb₁ _ (by decide) (by decide) (by decide), hh₀ _ (by decide) (by decide)]; exact h.hDp)
    (by rw [hb₁ _ (by decide) (by decide) (by decide), hh₀ _ (by decide) (by decide), h.dpl]; exact h.hPl)
    (by rw [h.dpl]; omega) (by rw [h.dpl]; omega) (h.dp.congrK (hr.iscr.trans i01) (hr.keep.trans k₁))
    (by rw [hb₁ _ (by decide) (by decide) (by decide), hh₀ _ (by decide) (by decide)]; exact h.hQi)
    (by rw [h.qil, h.dpl]) (h.qi.congrK (hr.iscr.trans i01) (hr.keep.trans k₁))
    (by rw [h.qil]; unfold wsWords; omega)
    (fun hm => by obtain ⟨_, _, hqi⟩ := hMk' hm; simp only [hm, ↓reduceIte, hQIe]; exact hqi))
    fun t₂ ⟨hg₂, hwsp₂, hxp₂, hlt₂, hh₂, f₂, k₂⟩ => ?_
  have hlop : slot ((k + 7) / 8) 8 ≤ offP ((k + 7) / 8) := le_refl _
  have hb₂ : ∀ i < 32, i ≠ Crt.sD → i ≠ Public.sCnt → word t₂.mem B (8 * i) = word t₁.mem B (8 * i) :=
    fun i hi h1 h2 => f₂.px_hdr hlop hi h1 h2
  have hqk : ∀ d, offQ ((k + 7) / 8) pl ≤ d → d + 8 ≤ 2 ^ 64 → word t₂.mem B d = word t₁.mem B d :=
    fun d hd hd' => f₂.px_above hlop (by unfold offQ offP at *; omega) hd'
  have hqw₂ : ∀ i < 32, word t₂.mem (off B (offQ ((k + 7) / 8) pl)) (8 * i) =
      word t₁.mem (off B (offQ ((k + 7) / 8) pl)) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hqk _ (by omega) (by omega)
  have hqv₂ : ∀ d m, d + 8 * m ≤ slot (wsWords ql) 8 → wv t₂.mem (off B (offQ ((k + 7) / 8) pl)) d m =
      wv t₁.mem (off B (offQ ((k + 7) / 8) pl)) d m := fun d m hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hqk _ (by omega) (by omega)
  have hwsq₂ : WsAt t₂.mem B (offQ ((k + 7) / 8) pl) (wsWords ql) mq := hwsq₁.of_words fun i hi => hqw₂ i (by omega)
  have hY8 := slot_le (w := wsWords ql) (show Public.aY < 8 by decide)
  have hN8 := slot_le (w := wsWords ql) (show Public.aN < 8 by decide)
  -- `m_q + q h`.
  rw [finish_out]
  refine wp_seqs_append (by simp [finishSum, zeroAccs]) (by simp [outStepsArr]) ?_
  refine WP.mono (finishSum_ok hg₂ (by omega) (by rw [hb₂ _ (by decide) (by decide) (by decide),
      hb₁ _ (by decide) (by decide) (by decide)]; exact hr.wsP)
    (by rw [hb₂ _ (by decide) (by decide) (by decide), hb₁ _ (by decide) (by decide) (by decide)]; exact hr.wsQ)
    hwsp₂.hdr.hw hwsq₂.hdr.hw (by rw [hwsp₂.hdr.harr _ (by decide), off_off])
    (by rw [hwsq₂.hdr.harr _ (by decide), off_off]) (by rw [hwsq₂.hdr.harr _ (by decide), off_off]) hlop
    (by unfold offQ offP; omega) hZq (by omega) hwp (by omega) hwq) fun t₃ ⟨hm₃, ho₃, k₃⟩ => ?_
  rw [← wv_off, ← wv_off, ← wv_off, hqv₂ _ _ (by omega), hqv₂ _ _ (by omega), hxq₁.n] at hm₃
  have hacc := accs_le ((k + 7) / 8)
  have hA0 := hdr_lt_slot ((k + 7) / 8) Public.aAcc (show 31 < 32 by decide)
  have hb₃ : ∀ i < 32, word t₃.mem B (8 * i) = word t₂.mem B (8 * i) := fun i hi =>
    ho₃.word (Or.inl (by have := hdr_lt_slot ((k + 7) / 8) Public.aAcc hi; omega)) (by omega)
  have hg₃ : Good t₃ B Z ((k + 7) / 8) minv := ⟨hg₂.scr.congr k₃.2.2, (k₃.gpr (by decide)).trans hg₂.rdi,
    ⟨(hb₃ _ (by decide)).trans hg₂.hdr.hw, (hb₃ _ (by decide)).trans hg₂.hdr.hminv,
      fun j hj => (hb₃ _ (by unfold sArr; omega)).trans (hg₂.hdr.harr j hj)⟩⟩
  have hfx : ∀ i < 32, hFixed i = true → word t₃.mem B (8 * i) = word s.mem B (8 * i) := fun i hi hf => by
    have h1 : i ≠ Crt.sD := by rintro rfl; revert hf; decide
    have h2 : i ≠ Public.sCnt := by rintro rfl; revert hf; decide
    rw [hb₃ i hi, hb₂ i hi h1 h2, hb₁ i hi h1 h2, hh₀ i hi hf]
  have hM₃ : word t₃.mem B (8 * Public.sMask) = mask Mk := by
    rw [hb₃ _ (by decide), hb₂ _ (by decide) (by decide) (by decide), hb₁ _ (by decide) (by decide) (by decide)]
    exact hr.msk
  have k03 := ((hr.keep.trans k₁).trans k₂).trans k₃
  have i23 : InScr B Z t₁.mem t₃.mem := (InScr.of_frm f₂ fun r hr' => by
    have := pxR_bound (wx := wsWords pl) hlop r hr'; unfold offQ offP at *; omega).trans
    (InScr.of_outside ho₃ (by omega))
  have i03 : InScr B Z s.mem t₃.mem := (hr.iscr.trans i01).trans i23
  -- The result.
  refine WP.mono (outPhaseArr_ok (j := Public.aAcc) (by decide) hg₃ hZ (by omega) (by omega) rfl
    (by rw [hfx _ (by decide) (by decide)]; exact h.hO) (by rw [hfx _ (by decide) (by decide)]; exact h.hK) hM₃
    (fun j hj => by rw [k03.2.2]; exact h.out j hj) h.outSep) fun t ⟨hbytes, hax, hsv, hfr, k₄⟩ => ?_
  refine ⟨?_, hax, fun i hi => by rw [hsv i hi]; exact hfx i (by omega) (by
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    fun x hx hx' => by rw [hfr x hx', i03 x hx], (k03.trans k₄).mono (by decide)⟩
  rw [hbytes]
  congr 1
  cases hMk2 : Mk
  · simp only [Bool.false_eq_true, ↓reduceIte]
  · simp only [↓reduceIte]
    obtain ⟨_, hpq, _⟩ := hMk' hMk2
    simp only [hMk2, ↓reduceIte] at hv₁ hlt₁ hh₂ hlt₂ hm₃ hP' hQ'
    have hmq : wv t₁.mem (off B (offQ ((k + 7) / 8) pl)) (slot (wsWords ql) Public.aY) (wsWords ql) =
        C ^ Spec.Rsa.os2ip dqb % Q := by
      rw [← Nat.mod_eq_of_lt hlt₁]; exact hv₁ ⟨P, by rw [← hpq, Nat.mul_comm]⟩
    obtain ⟨a, b, ha, hb, hbP, hh⟩ := hh₂ trivial
    have hR : Nat.Coprime (2 ^ (64 * wsWords pl)) P := VG.Proof.Bignum.coprime_pow2 hP'.2 _
    have hhv := VG.Proof.Bignum.crt_h (m₁ := C ^ Spec.Rsa.os2ip dpb % P) (by omega) hR
      (by rw [ha, Nat.mod_mul_mod]) hb hbP hh hlt₂
    rw [hQIe, hmq] at hhv
    -- The sum is below `N`, so below `2^(64 w)`.
    generalize wv t₂.mem (off B (offP ((k + 7) / 8))) (slot (wsWords pl) Public.aY) (wsWords pl) = hv at *
    rw [hmq] at hm₃
    have hQpos : 0 < Q := by omega
    have hlt : C ^ Spec.Rsa.os2ip dqb % Q + hv * Q < N := by
      have h1 := Nat.mod_lt (C ^ Spec.Rsa.os2ip dqb) hQpos
      have h2 : (hv + 1) * Q ≤ P * Q := Nat.mul_le_mul_right Q (by omega)
      rw [Nat.add_mul, Nat.one_mul] at h2
      omega
    have hsplit := wv_split t₃.mem B (slot ((k + 7) / 8) Public.aAcc)
      (show (k + 7) / 8 + ((k + 7) / 8 + 2) = 2 * ((k + 7) / 8) + 2 by omega)
    rw [hm₃] at hsplit
    have hrest : wv t₃.mem B (slot ((k + 7) / 8) Public.aAcc + 8 * ((k + 7) / 8)) ((k + 7) / 8 + 2) = 0 := by
      by_contra hne
      have := Nat.mul_le_mul_left (2 ^ (64 * ((k + 7) / 8))) (show 1 ≤ _ from Nat.pos_of_ne_zero hne)
      omega
    rw [hrest, Nat.mul_zero, Nat.add_zero] at hsplit
    rw [← hsplit, crtResult, hhv, Nat.mul_comm hv Q]

end VG.Proof.Bignum.X86_64
