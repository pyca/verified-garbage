import VerifiedGarbage.Proof.Bignum.X86_64.CrtFront
import VerifiedGarbage.Proof.Bignum.CrtResult

/-!
# RSA with the CRT on x86-64: from the checks to the result

`q`'s phase, `p`'s, and `m = m_q + q h` written out masked (`back_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

theorem finish_out : finish = finishSum ++ outStepsArr Public.aAcc := rfl

/-- What a valid modulus and the key's lengths give. -/
theorem crt_bounds {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) :
    Spec.Rsa.os2ip nb % 2 = 1 ∧ 1 < Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip pb < Spec.Rsa.os2ip nb ∧
      Spec.Rsa.os2ip qb < Spec.Rsa.os2ip nb :=
  crt_bounds_of hv h.k1 h.pbl h.pl2 h.qbl h.ql2

/-- After `q`'s phase: as after the checks, and `m_q` in `q`'s `aY`. -/
structure QReady (s t : State) (B : Addr) (Z w pl ql : Nat) (minv mp mq : BitVec 64) (N C P Q : Nat)
    (dqb : List Byte) (Mk : Bool) : Prop extends CrtReady s t B Z w pl ql minv mp mq N C P Q Mk where
  qlt : wv t.mem (off B (offQ w pl)) (slot (wsWords ql) Public.aY) (wsWords ql) < if Mk then Q else 3
  qval : Mk = true →
    wv t.mem (off B (offQ w pl)) (slot (wsWords ql) Public.aY) (wsWords ql) = C ^ Spec.Rsa.os2ip dqb % Q

/-- `q`'s phase, from the checks. -/
theorem qPart_ok (M : Mont) {s t₀ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs (qPhase M.mm)) t₀ fun t => QReady s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb)
      (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dqb Mk := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
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
  generalize Spec.Rsa.os2ip qib = QI at *
  obtain ⟨hMk', -, hQ'⟩ := mask_facts hMk hodd hPN hQN
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hP8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega_using []
  have hQ8 : 256 ≤ slot (wsWords ql) 8 := by unfold slot hdrBytes; omega_using []
  have hZ : slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ at hZq; omega_using [hZq]
  have hwq2 : 2 ≤ wsWords ql := by unfold wsWords; omega_using []
  have hwq := wsWords_le (len := ql) (w := (k + 7) / 8) (by omega_using [hql2]) (by omega_using [hk1])
  have hh₀ : ∀ i < 32, hFixed i = true → word t₀.mem B (8 * i) = word s.mem B (8 * i) := hr.hfix
  refine WP.mono (qPhase_ok M hr.good (by omega_using [hk1]) (by omega_using [hk2]) (by unfold offQ; omega_using [])
      hZq hwq2 hwq hr.wsQ hr.qws
    hr.nv hodd hN1 hr.xm hr.qxv hQ'.1 hQ'.2 (by rw [hh₀ _ (by decide) (by decide)]; exact h.hDq)
    (by rw [hh₀ _ (by decide) (by decide), h.dql]; exact h.hQl) (by rw [h.dql]; omega_using [hql1])
    (by rw [h.dql]; omega_using [hk2, hql2]) (h.dq.congrK hr.iscr hr.keep))
    fun t₁ ⟨hg₁, hwsq₁, hxq₁, hlt₁, hv₁, f₁, k₁⟩ => ?_
  have hz : B.toNat + slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega_using [hn, hZ]
  have hloq : slot ((k + 7) / 8) 8 ≤ offQ ((k + 7) / 8) pl := by unfold offQ; omega_using []
  have f₁' : Frm B (pRanges ((k + 7) / 8) ++ [xRange (offQ ((k + 7) / 8) pl) (wsWords ql)]) t₀.mem t₁.mem :=
    f₁.mono fun r hr => (List.mem_append.mp hr).elim
      (fun h' => List.mem_append_left _ (List.mem_append_left _ h')) (fun h' => List.mem_append_right _ h')
  have hb₁ : ∀ i < 32, i ≠ Crt.sD → i ≠ Public.sCnt → word t₁.mem B (8 * i) = word t₀.mem B (8 * i) :=
    fun i hi h1 h2 => f₁'.px_hdr hloq hi h1 h2
  -- `p`'s workspace, below `q`'s, is kept.
  have hpk : ∀ d, slot ((k + 7) / 8) 8 ≤ d → d + 8 ≤ offQ ((k + 7) / 8) pl →
      word t₁.mem B d = word t₀.mem B d := fun d hd hd' => f₁.word_eq (fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact Or.inr (by have := pRanges_le ((k + 7) / 8) r (List.mem_append_left _ hr); omega_using [hd, this])
    · rw [List.mem_singleton.mp hr]; exact Or.inl (by simp only [xRange]; omega_using [hd'])) (by omega_using [hZq, hn, hd'])
  have hpw₁ : ∀ i < 32, word t₁.mem (off B (offP ((k + 7) / 8))) (8 * i) =
      word t₀.mem (off B (offP ((k + 7) / 8))) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hpk _ (by unfold offP; omega_using []) (by unfold offP offQ; omega_using [hP8, hi])
  have hpv₁ : ∀ d m, d + 8 * m ≤ slot (wsWords pl) 8 → wv t₁.mem (off B (offP ((k + 7) / 8))) d m =
      wv t₀.mem (off B (offP ((k + 7) / 8))) d m := fun d m hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hpk _ (by unfold offP; omega_using []) (by unfold offP offQ; omega_using [hd, hi])
  have i01 : InScr B Z t₀.mem t₁.mem := InScr.of_frm f₁' fun r hr => by
    have := pxR_bound (wx := wsWords ql) hloq r hr; omega_using [hZq, this]
  refine ⟨⟨hg₁, hr.nv.of_frm f₁ hloq hz (by omega_using [hwq2, hwq]), ?_, ?_, ?_, ?_,
      hr.pws.of_words fun i hi => hpw₁ i (by omega_using [hi]),
    ⟨?_, ?_, ?_⟩, ?_, hwsq₁, hxq₁, ?_, hr.iscr.trans i01, (hr.keep.trans k₁).mono (by decide)⟩, hlt₁, ?_⟩
  · rw [f₁.gx_wv hloq hz (by decide) (by decide) (by decide) (by decide)]; exact hr.xm
  · rw [hb₁ _ (by decide) (by decide) (by decide)]; exact hr.msk
  · rw [hb₁ _ (by decide) (by decide) (by decide)]; exact hr.wsP
  · rw [hb₁ _ (by decide) (by decide) (by decide)]; exact hr.wsQ
  · rw [hpv₁ _ _ (by have := slot_le (w := wsWords pl) (show Public.aN < 8 by decide); omega_using [this])]; exact hr.pxv.n
  · rw [word_off, hpk _ (by unfold offP; omega_using []) (by
      have := slot_le (w := wsWords pl) (show Public.aN < 8 by decide); unfold offP offQ; omega_using [this]), ← word_off]
    exact hr.pxv.inv
  · rw [hpv₁ _ _ (by have := slot_le (w := wsWords pl) (show Public.aOne < 8 by decide); omega_using [this])]
    exact hr.pxv.one
  · rw [hpw₁ _ (by decide)]; exact hr.pmask
  · intro i hi hf
    have h1 : i ≠ Crt.sD := by rintro rfl; revert hf; decide
    have h2 : i ≠ Public.sCnt := by rintro rfl; revert hf; decide
    rw [hb₁ i hi h1 h2, hh₀ i hi hf]
  · intro hm
    obtain ⟨_, hpq, _⟩ := hMk' hm
    simp only [hm, ↓reduceIte] at hv₁ hlt₁
    rw [← Nat.mod_eq_of_lt hlt₁]; exact hv₁ ⟨P, by rw [← hpq, Nat.mul_comm]⟩

/-- After `p`'s phase: `h` in `p`'s `aY`, `m_q` in `q`'s. -/
structure PDone (s t : State) (B : Addr) (Z w pl ql : Nat) (minv mp mq : BitVec 64) (C P Q QI : Nat)
    (dpb dqb : List Byte) (Mk : Bool) : Prop where
  good : Good t B Z w minv
  msk : word t.mem B (8 * Public.sMask) = mask Mk
  wsP : word t.mem B (8 * sWsP) = off B (offP w)
  wsQ : word t.mem B (8 * sWsQ) = off B (offQ w pl)
  pws : WsAt t.mem B (offP w) (wsWords pl) mp
  qws : WsAt t.mem B (offQ w pl) (wsWords ql) mq
  qn : wv t.mem (off B (offQ w pl)) (slot (wsWords ql) Public.aN) (wsWords ql) = if Mk then Q else 3
  qlt : wv t.mem (off B (offQ w pl)) (slot (wsWords ql) Public.aY) (wsWords ql) < if Mk then Q else 3
  qval : Mk = true →
    wv t.mem (off B (offQ w pl)) (slot (wsWords ql) Public.aY) (wsWords ql) = C ^ Spec.Rsa.os2ip dqb % Q
  plt : wv t.mem (off B (offP w)) (slot (wsWords pl) Public.aY) (wsWords pl) < if Mk then P else 3
  pval : Mk = true → ∃ a b, a % P = C ^ Spec.Rsa.os2ip dpb * 2 ^ (64 * wsWords pl) % P ∧
    b % P = C ^ Spec.Rsa.os2ip dqb % Q * 2 ^ (64 * wsWords pl) % P ∧ b < P ∧
    wv t.mem (off B (offP w)) (slot (wsWords pl) Public.aY) (wsWords pl) * 2 ^ (64 * wsWords pl) % P =
      (a + P - b) % P * QI % P
  hfix : HFix B s.mem t.mem
  iscr : InScr B Z s.mem t.mem
  keep : Keep mmRegs s t

/-- `p`'s phase, from `q`'s. -/
theorem pPart_ok (M : Mont) {s t₁ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : QReady s t₁ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dqb Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs (pPhase M.mm)) t₁ fun t => PDone s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib) dpb dqb Mk := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
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
  obtain ⟨hMk', hP', -⟩ := mask_facts hMk hodd hPN hQN
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hP8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega_using []
  have hQ8 : 256 ≤ slot (wsWords ql) 8 := by unfold slot hdrBytes; omega_using []
  have hZ : slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ at hZq; omega_using [hZq]
  have hwp2 : 2 ≤ wsWords pl := by unfold wsWords; omega_using []
  have hwq2 : 2 ≤ wsWords ql := by unfold wsWords; omega_using []
  have hwp := wsWords_le (len := pl) (w := (k + 7) / 8) (by omega_using [hpl2]) (by omega_using [hk1])
  have hwq := wsWords_le (len := ql) (w := (k + 7) / 8) (by omega_using [hql2]) (by omega_using [hwp2, hwp])
  have hh₁ : ∀ i < 32, hFixed i = true → word t₁.mem B (8 * i) = word s.mem B (8 * i) := hr.hfix
  refine WP.mono (pPhase_ok M (X := if Mk then P else 3) (c := Mk) (eb := dpb) (qib := qib)
    (oq := offQ ((k + 7) / 8) pl) (wq := wsWords ql) hr.good (by omega_using [hk1]) (by omega_using [hk2])
    (show slot ((k + 7) / 8) 8 ≤ offP ((k + 7) / 8) from le_refl _) (by unfold offQ offP; omega_using []) hZq hwp2 hwp
    (by omega_using [hwq2]) hwq hr.wsP hr.pws hr.wsQ hr.qws hr.nv hodd hN1 hr.xm hr.pxv hP'.1 hP'.2 hr.pmask
    (fun hm => by obtain ⟨_, hpq, _⟩ := hMk' hm; simp only [hm, ↓reduceIte]; exact ⟨Q, hpq.symm⟩)
    (by rw [hh₁ _ (by decide) (by decide)]; exact h.hDp)
    (by rw [hh₁ _ (by decide) (by decide), h.dpl]; exact h.hPl)
    (by rw [h.dpl]; omega_using [hpl1]) (by rw [h.dpl]; omega_using [hk2, hpl2]) (h.dp.congrK hr.iscr hr.keep)
    (by rw [hh₁ _ (by decide) (by decide)]; exact h.hQi)
    (by rw [h.qil, h.dpl]) (h.qi.congrK hr.iscr hr.keep)
    (by rw [h.qil]; unfold wsWords; omega_using [])
    (fun hm => by obtain ⟨_, _, hqi⟩ := hMk' hm; simp only [hm, ↓reduceIte, hQIe]; exact hqi))
    fun t₂ ⟨hg₂, hwsp₂, hxp₂, hlt₂, hh₂, f₂, k₂⟩ => ?_
  have hlop : slot ((k + 7) / 8) 8 ≤ offP ((k + 7) / 8) := le_refl _
  have hb₂ : ∀ i < 32, i ≠ Crt.sD → i ≠ Public.sCnt → word t₂.mem B (8 * i) = word t₁.mem B (8 * i) :=
    fun i hi h1 h2 => f₂.px_hdr hlop hi h1 h2
  have hqk : ∀ d, offQ ((k + 7) / 8) pl ≤ d → d + 8 ≤ 2 ^ 64 → word t₂.mem B d = word t₁.mem B d :=
    fun d hd hd' => f₂.px_above hlop (by unfold offQ offP at *; omega_using [hd]) hd'
  have hqw₂ : ∀ i < 32, word t₂.mem (off B (offQ ((k + 7) / 8) pl)) (8 * i) =
      word t₁.mem (off B (offQ ((k + 7) / 8) pl)) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hqk _ (by omega_using []) (by omega_using [hZq, hn, hQ8, hi])
  have hqv₂ : ∀ d m, d + 8 * m ≤ slot (wsWords ql) 8 → wv t₂.mem (off B (offQ ((k + 7) / 8) pl)) d m =
      wv t₁.mem (off B (offQ ((k + 7) / 8) pl)) d m := fun d m hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hqk _ (by omega_using []) (by omega_using [hZq, hn, hd, hi])
  have hY8 := slot_le (w := wsWords ql) (show Public.aY < 8 by decide)
  have hN8 := slot_le (w := wsWords ql) (show Public.aN < 8 by decide)
  have i12 : InScr B Z t₁.mem t₂.mem := InScr.of_frm f₂ fun r hr' => by
    have := pxR_bound (wx := wsWords pl) hlop r hr'; unfold offQ offP at *; omega_using [hZq, this]
  refine ⟨hg₂, ?_, ?_, ?_, hwsp₂, hr.qws.of_words fun i hi => hqw₂ i (by omega_using [hi]), ?_, ?_, ?_, hlt₂, ?_, ?_,
    hr.iscr.trans i12, (hr.keep.trans k₂).mono (by decide)⟩
  · rw [hb₂ _ (by decide) (by decide) (by decide)]; exact hr.msk
  · rw [hb₂ _ (by decide) (by decide) (by decide)]; exact hr.wsP
  · rw [hb₂ _ (by decide) (by decide) (by decide)]; exact hr.wsQ
  · rw [hqv₂ _ _ (by omega_using [hN8])]; exact hr.qxv.n
  · rw [hqv₂ _ _ (by omega_using [hY8])]; exact hr.qlt
  · intro hm; rw [hqv₂ _ _ (by omega_using [hY8])]; exact hr.qval hm
  · intro hm
    have hq := hr.qval hm
    obtain ⟨a, b, ha, hb, hbP, hh⟩ := hh₂ hm
    simp only [hm, ↓reduceIte] at ha hb hbP hh
    exact ⟨a, b, ha, by rw [hb, hq], hbP, by rw [hh, hQIe]⟩
  · intro i hi hf
    have h1 : i ≠ Crt.sD := by rintro rfl; revert hf; decide
    have h2 : i ≠ Public.sCnt := by rintro rfl; revert hf; decide
    rw [hb₂ i hi h1 h2, hh₁ i hi hf]

/-- `m = m_q + q h` written out masked, from `p`'s phase. -/
theorem finPart_ok {s t₂ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : PDone s t₂ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib) dpb dqb Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs finish) t₂ fun t => MainPost s t B Z k op
      (if Mk then crtResult (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dpb) (Spec.Rsa.os2ip dqb)
        (Spec.Rsa.os2ip qib) (Spec.Rsa.os2ip xb) else 0) Mk := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  have hNlt : Spec.Rsa.os2ip nb < 2 ^ (64 * ((k + 7) / 8)) := by
    have := os2ip_lt nb
    rw [h.nl, pow256_eq] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega_using []))
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
  obtain ⟨hMk', hP', hQ'⟩ := mask_facts hMk hodd hPN hQN
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hP8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega_using []
  have hQ8 : 256 ≤ slot (wsWords ql) 8 := by unfold slot hdrBytes; omega_arith
  have hwp2 : 2 ≤ wsWords pl := by unfold wsWords; omega_using []
  have hwq2 : 2 ≤ wsWords ql := by unfold wsWords; omega_using []
  have hwp := wsWords_le (len := pl) (w := (k + 7) / 8) (by omega_using [hpl2]) (by omega_using [hk1])
  have hwq := wsWords_le (len := ql) (w := (k + 7) / 8) (by omega_using [hql2]) (by omega_using [hwp2, hwp])
  have hZ : slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ at hZq; omega_using [hZq]
  have hlop : slot ((k + 7) / 8) 8 ≤ offP ((k + 7) / 8) := le_refl _
  have hY8 := slot_le (w := wsWords ql) (show Public.aY < 8 by decide)
  have hN8 := slot_le (w := wsWords ql) (show Public.aN < 8 by decide)
  -- `m_q + q h`.
  rw [finish_out]
  refine wp_seqs_append (by simp [finishSum, zeroAccs]) (by simp [outStepsArr]) ?_
  refine WP.mono (finishSum_ok hr.good (by omega_using [hk2]) hr.wsP hr.wsQ hr.pws.hdr.hw hr.qws.hdr.hw
    (by rw [hr.pws.hdr.harr _ (by decide), off_off]) (by rw [hr.qws.hdr.harr _ (by decide), off_off])
    (by rw [hr.qws.hdr.harr _ (by decide), off_off]) hlop (by unfold offQ offP; omega_using []) hZq (by omega_using [hwp2]) hwp
    (by omega_using [hwq2]) hwq) fun t₃ ⟨hm₃, ho₃, k₃⟩ => ?_
  rw [← wv_off, ← wv_off, ← wv_off, hr.qn] at hm₃
  have hacc := accs_le ((k + 7) / 8)
  have hA0 := hdr_lt_slot ((k + 7) / 8) Public.aAcc (show 31 < 32 by decide)
  have hb₃ : ∀ i < 32, word t₃.mem B (8 * i) = word t₂.mem B (8 * i) := fun i hi =>
    ho₃.word (Or.inl (by have := hdr_lt_slot ((k + 7) / 8) Public.aAcc hi; omega_using [this])) (by omega_using [hi])
  have hg₃ : Good t₃ B Z ((k + 7) / 8) minv := ⟨hr.good.scr.congr k₃.2.2, (k₃.gpr (by decide)).trans hr.good.rdi,
    ⟨(hb₃ _ (by decide)).trans hr.good.hdr.hw, (hb₃ _ (by decide)).trans hr.good.hdr.hminv,
      fun j hj => (hb₃ _ (by unfold sArr; omega_using [hj])).trans (hr.good.hdr.harr j hj)⟩⟩
  have hfx : ∀ i < 32, hFixed i = true → word t₃.mem B (8 * i) = word s.mem B (8 * i) := fun i hi hf => by
    rw [hb₃ i hi]; exact hr.hfix i hi hf
  have hM₃ : word t₃.mem B (8 * Public.sMask) = mask Mk := by rw [hb₃ _ (by decide)]; exact hr.msk
  have k03 := hr.keep.trans k₃
  have i03 : InScr B Z s.mem t₃.mem := hr.iscr.trans (InScr.of_outside ho₃ (by omega_using [hZ, hacc]))
  -- The result.
  refine WP.mono (outPhaseArr_ok (j := Public.aAcc) (by decide) hg₃ hZ (by omega_using [hwq2, hwq]) (by omega_using [hk2]) rfl
    (by rw [hfx _ (by decide) (by decide)]; exact h.hO) (by rw [hfx _ (by decide) (by decide)]; exact h.hK) hM₃
    (fun j hj => by rw [k03.2.2]; exact h.out j hj) h.outSep) fun t ⟨hbytes, hax, hsv, hfr, k₄⟩ => ?_
  refine ⟨?_, hax, fun i hi => by rw [hsv i hi]; exact hfx i (by omega_using [hi]) (by
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    fun x hx hx' => by rw [hfr x hx', i03 x hx], (k03.trans k₄).mono (by decide)⟩
  rw [hbytes]
  congr 1
  cases hMk2 : Mk
  · simp only [Bool.false_eq_true, ↓reduceIte]
  · simp only [↓reduceIte]
    obtain ⟨_, hpq, _⟩ := hMk' hMk2
    have hmq := hr.qval hMk2
    have hlt₂ := hr.plt
    simp only [hMk2, ↓reduceIte] at hlt₂ hm₃ hP' hQ'
    obtain ⟨a, b, ha, hb, hbP, hh⟩ := hr.pval hMk2
    have hR : Nat.Coprime (2 ^ (64 * wsWords pl)) P := VG.Proof.Bignum.coprime_pow2 hP'.2 _
    have hhv := VG.Proof.Bignum.crt_h (m₁ := C ^ Spec.Rsa.os2ip dpb % P) (by omega_using [hbP]) hR
      (by rw [ha, Nat.mod_mul_mod]) hb hbP hh hlt₂
    -- The sum is below `N`, so below `2^(64 w)`.
    generalize wv t₂.mem (off B (offP ((k + 7) / 8))) (slot (wsWords pl) Public.aY) (wsWords pl) = hv at *
    rw [hmq] at hm₃
    have hQpos : 0 < Q := by omega_using [hQ']
    have hlt : C ^ Spec.Rsa.os2ip dqb % Q + hv * Q < N := by
      have h1 := Nat.mod_lt (C ^ Spec.Rsa.os2ip dqb) hQpos
      have h2 : (hv + 1) * Q ≤ P * Q := Nat.mul_le_mul_right Q (by omega_using [hlt₂])
      rw [Nat.add_mul, Nat.one_mul] at h2
      omega_using [hpq, h1, h2]
    have hsplit := wv_split t₃.mem B (slot ((k + 7) / 8) Public.aAcc)
      (show (k + 7) / 8 + ((k + 7) / 8 + 2) = 2 * ((k + 7) / 8) + 2 by omega_using [])
    rw [hm₃] at hsplit
    have hrest : wv t₃.mem B (slot ((k + 7) / 8) Public.aAcc + 8 * ((k + 7) / 8)) ((k + 7) / 8 + 2) = 0 := by
      by_contra hne
      have := Nat.mul_le_mul_left (2 ^ (64 * ((k + 7) / 8))) (show 1 ≤ _ from Nat.pos_of_ne_zero hne)
      omega_using [hNlt, hlt, hsplit, this]
    rw [hrest, Nat.mul_zero, Nat.add_zero] at hsplit
    rw [← hsplit, crtResult, hhv, Nat.mul_comm hv Q]

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
  rw [List.append_assoc]
  exact wp_seqs_append (by simp [qPhase]) (by simp [pPhase]) (WP.mono (qPart_ok M h hv hr hMk) fun _ hq =>
    wp_seqs_append (by simp [pPhase]) (by simp [finish]) (WP.mono (pPart_ok M h hv hq hMk) fun _ hp =>
      finPart_ok h hv hp hMk))

end VG.Proof.Bignum.X86_64
