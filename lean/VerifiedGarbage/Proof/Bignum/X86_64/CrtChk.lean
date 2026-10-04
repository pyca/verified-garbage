import VerifiedGarbage.Proof.Bignum.X86_64.CrtP

/-!
# RSA with the CRT on x86-64: the checks

`checks`: the mask of `c < n`, `p q = n` and `qInv < p` into the modulus'
`sMask` and the primes' `sMaskX`, the primes replaced by 3 where it is
clear, and their `-X⁻¹` and the number 1 (`checks_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

theorem mask_and (a b : Bool) : mask a &&& mask b = mask (a && b) := by
  cases a <;> cases b <;> rfl

theorem odd_of_mul_odd {P Q N : Nat} (h : P * Q = N) (hN : N % 2 = 1) : P % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one P with hP | hP
  · rw [← h, Nat.mul_mod, hP, Nat.zero_mul] at hN; exact absurd hN (by decide)
  · exact hP

/-- The mask of the private key's checks. -/
def keyMask (m0 : Bool) (N P Q QI : Nat) : Bool := m0 && decide (P * Q = N) && decide (QI < P)

/-- The checks: the mask `M` of `c < n` (`m0`), `p q = n` and `qInv < p`;
`p := M ? p : 3`, `q := M ? q : 3`, their `-X⁻¹` and 1. -/
theorem checks_ok {s : State} {B : Addr} {Z w : Nat} {minv mp mq : BitVec 64} {op oq wp wq N P Q QI : Nat}
    {m0 : Bool} (hg : Good s B Z w minv) (hw : 8 ≤ w) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ op)
    (hop : op + slot wp 8 + tabBytes wp ≤ oq) (hoq : oq + slot wq 8 + tabBytes wq ≤ Z) (hwp : 2 ≤ wp) (hwp' : wp ≤ w) (hwq : 2 ≤ wq)
    (hwq' : wq ≤ w) (hsP : word s.mem B (8 * sWsP) = off B op) (hsQ : word s.mem B (8 * sWsQ) = off B oq)
    (hwsP : WsAt s.mem B op wp mp) (hwsQ : WsAt s.mem B oq wq mq)
    (hN : wv s.mem B (slot w Public.aN) w = N) (hM : word s.mem B (8 * Public.sMask) = mask m0)
    (hP : wv s.mem (off B op) (slot wp Public.aN) wp = P) (hQ : wv s.mem (off B oq) (slot wq Public.aN) wq = Q)
    (hQI : wv s.mem (off B op) (slot wp aChunk) wp = QI) (hodd : N % 2 = 1) :
    WP isa (seqs checks) s fun t => Good t B Z w minv ∧
      word t.mem B (8 * Public.sMask) = mask (keyMask m0 N P Q QI) ∧
      word t.mem B (8 * sWsP) = off B op ∧ word t.mem B (8 * sWsQ) = off B oq ∧
      (∃ mp', WsAt t.mem B op wp mp' ∧ XVals t B op wp mp' (if keyMask m0 N P Q QI then P else 3) ∧
        word t.mem (off B op) (8 * sMaskX) = mask (keyMask m0 N P Q QI)) ∧
      (∃ mq', WsAt t.mem B oq wq mq' ∧ XVals t B oq wq mq' (if keyMask m0 N P Q QI then Q else 3)) ∧
      Frm B [(slot w Public.aAcc, 8 * (2 * w + 2)), (8 * Public.sMask, 8), (op, slot wp 8), (oq, slot wq 8)]
        s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hP8 : 256 ≤ slot wp 8 := by unfold slot hdrBytes; omega
  have hQ8 : 256 ≤ slot wq 8 := by unfold slot hdrBytes; omega
  have hz : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  have hacc := accs_le w
  have hA0 := hdr_lt_slot w Public.aAcc (show 31 < 32 by decide)
  unfold checks
  simp only [List.append_assoc]
  -- `p q`.
  refine wp_seqs_append (by simp [pqProduct, zeroAccs]) (by simp) ?_
  refine WP.mono (pqProduct_ok hg (by omega) hsP hsQ hwsP.hdr.hw hwsQ.hdr.hw
    (by rw [hwsP.hdr.harr _ (by decide), off_off]) (by rw [hwsQ.hdr.harr _ (by decide), off_off]) hlo hop hoq
    (by omega) hwp' (by omega) hwq') fun s₁ ⟨hpq₁, ho₁, k₁⟩ => ?_
  have hb₁ : ∀ i < 32, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    ho₁.word (Or.inl (by have := hdr_lt_slot w Public.aAcc hi; omega)) (by omega)
  have hab₁ : ∀ d, slot w 8 ≤ d → d + 8 ≤ 2 ^ 64 → word s₁.mem B d = word s.mem B d := fun d hd hd' =>
    ho₁.word (Or.inr (by omega)) hd'
  have hg₁ : Good s₁ B Z w minv := ⟨hs.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi,
    ⟨(hb₁ _ (by decide)).trans hg.hdr.hw, (hb₁ _ (by decide)).trans hg.hdr.hminv,
      fun j hj => (hb₁ _ (by unfold sArr; omega)).trans (hg.hdr.harr j hj)⟩⟩
  have hN₁ : wv s₁.mem B (slot w Public.aN) w = N := by
    have := slot_le (w := w) (show Public.aN < 8 by decide)
    have : slot w Public.aN + 8 * w ≤ slot w Public.aAcc := by unfold slot Public.aN Public.aAcc; omega
    rw [ho₁.wv (Or.inl (by omega)) (by omega)]; exact hN
  rw [← wv_off, ← wv_off, hP, hQ] at hpq₁
  -- `p q = n`.
  refine wp_seqs_append (by simp [eqCheck]) (by simp) ?_
  refine WP.mono (eqCheck_ok hg₁ (by omega) (by omega) (by omega)) fun s₂ ⟨hM₂, ho₂, k₂⟩ => ?_
  rw [hpq₁, hN₁, hb₁ _ (by decide), hM, mask_and] at hM₂
  have hb₂ : ∀ d, d + 8 ≤ 8 * Public.sMask ∨ 8 * Public.sMask + 8 ≤ d → d + 8 ≤ 2 ^ 64 →
      word s₂.mem B d = word s₁.mem B d := fun d hd hd' => ho₂.word hd hd'
  have hab₂ : ∀ d, slot w 8 ≤ d → d + 8 ≤ 2 ^ 64 → word s₂.mem B d = word s.mem B d := fun d hd hd' => by
    rw [hb₂ d (Or.inr (by unfold Public.sMask sFn; omega)) hd', hab₁ d hd hd']
  have hpw₂ : ∀ i < 32, word s₂.mem (off B op) (8 * i) = word s.mem (off B op) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hab₂ _ (by omega) (by omega)
  have hqw₂ : ∀ i < 32, word s₂.mem (off B oq) (8 * i) = word s.mem (off B oq) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hab₂ _ (by omega) (by omega)
  have hpv₂ : ∀ d k, d + 8 * k ≤ slot wp 8 → wv s₂.mem (off B op) d k = wv s.mem (off B op) d k := fun d k hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hab₂ _ (by omega) (by omega)
  have hqv₂ : ∀ d k, d + 8 * k ≤ slot wq 8 → wv s₂.mem (off B oq) d k = wv s.mem (off B oq) d k := fun d k hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hab₂ _ (by omega) (by omega)
  have hsP₂ : word s₂.mem B (8 * sWsP) = off B op := by
    rw [hb₂ _ (Or.inr (by unfold sWsP Public.sMask sFn; omega)) (by unfold sWsP sFn; omega), hb₁ _ (by decide)]
    exact hsP
  have hsQ₂ : word s₂.mem B (8 * sWsQ) = off B oq := by
    rw [hb₂ _ (Or.inr (by unfold sWsQ Public.sMask sFn; omega)) (by unfold sWsQ sFn; omega), hb₁ _ (by decide)]
    exact hsQ
  have hs₂ := hs.congr (k₁.trans k₂).2.2
  have hdi₂ : s₂.gpr .rdi = B := ((k₁.trans k₂).gpr (by decide)).trans hg.rdi
  -- Into `p`'s workspace: `qInv < p`.
  refine wp_seqs_append (by simp) (by simp [qinvCheck]) ?_
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off B op ∧ t.mem = s₂.mem)
    (by xrun [enterP, State.ea, hdr, hdi₂, hdrOff, hs₂.ld (d := 8 * sWsP) (by unfold sWsP sFn; omega), hsP₂]) rfl)
    fun s₃ ⟨⟨hdi₃, hm₃⟩, k₃⟩ => ?_
  have hs₃ := hs₂.congr k₃.2.2
  have hwsP₃ : WsAt s₃.mem B op wp mp := by rw [hm₃]; exact hwsP.of_words fun i hi => hpw₂ i (by omega)
  refine wp_seqs_append (by simp [qinvCheck]) (by simp [primeFix]) ?_
  refine WP.mono (qinvCheck_ok hs₃ hdi₃ hwsP₃.hdr (by omega) (by unfold Public.sMask sFn; omega) (by omega)
    (by omega) hwsP₃.link) fun s₄ ⟨hM₄, ho₄, k₄⟩ => ?_
  rw [hm₃, hpv₂ _ _ (by have := slot_le (w := wp) (show aChunk < 8 by decide); omega),
    hpv₂ _ _ (by have := slot_le (w := wp) (show Public.aN < 8 by decide); omega), hP, hQI, hM₂, mask_and] at hM₄
  have hb₄ : ∀ d, d + 8 ≤ 8 * Public.sMask ∨ 8 * Public.sMask + 8 ≤ d → d + 8 ≤ 2 ^ 64 →
      word s₄.mem B d = word s₂.mem B d := fun d hd hd' => by rw [ho₄.word hd hd', hm₃]
  have hab₄ : ∀ d, slot w 8 ≤ d → d + 8 ≤ 2 ^ 64 → word s₄.mem B d = word s.mem B d := fun d hd hd' => by
    rw [hb₄ d (Or.inr (by unfold Public.sMask sFn; omega)) hd', hab₂ d hd hd']
  have hH₄ : Hdr s₄.mem B w minv := by
    have : ∀ i < 16, word s₄.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
      rw [hb₄ _ (Or.inl (by unfold Public.sMask sFn; omega)) (by omega),
        hb₂ _ (Or.inl (by unfold Public.sMask sFn; omega)) (by omega), hb₁ _ (by omega)]
    exact ⟨(this _ (by decide)).trans hg.hdr.hw, (this _ (by decide)).trans hg.hdr.hminv,
      fun j hj => (this _ (by unfold sArr; omega)).trans (hg.hdr.harr j hj)⟩
  have hwsP₄ : WsAt s₄.mem B op wp mp := hwsP.of_words fun i hi => by
    rw [word_off, word_off]; exact hab₄ _ (by omega) (by omega)
  have kk4 := ((k₁.trans k₂).trans k₃).trans k₄
  have hcP₄ := SubCtx.mk' (hs.congr kk4.2.2) hH₄ hwsP₄ ((k₄.gpr (by decide)).trans hdi₃) hlo (by omega)
  have hoddP : keyMask m0 N P Q QI = true → P % 2 = 1 := fun h => by
    simp only [keyMask, Bool.and_eq_true, decide_eq_true_eq] at h
    exact odd_of_mul_odd h.1.2 hodd
  have hoddQ : keyMask m0 N P Q QI = true → Q % 2 = 1 := fun h => by
    simp only [keyMask, Bool.and_eq_true, decide_eq_true_eq] at h
    exact odd_of_mul_odd (by rw [Nat.mul_comm]; exact h.1.2) hodd
  -- `p := M ? p : 3`.
  refine wp_seqs_append (by simp [primeFix]) (by simp) ?_
  refine WP.mono (primeFix_ok hcP₄ hwp hwp' (by omega) hM₄
    (by rw [wv_off, (show wv s₄.mem B (op + slot wp Public.aN) wp = wv s.mem B (op + slot wp Public.aN) wp from
      wv_congr fun i hi => hab₄ _ (by omega) (by
        have := slot_le (w := wp) (show Public.aN < 8 by decide); omega)), ← wv_off]; exact hP) hoddP)
    fun s₅ ⟨mp', hcP₅, hP₅, hiP₅, hoP₅, hmP₅, f₅, k₅⟩ => ?_
  have hpr : ∀ r ∈ [(slot wp Public.aN, 8 * (wp + 2)), (slot wp Public.aOne, 8 * (wp + 2)), (8 * sMaskX, 8),
      (8 * sMinv, 8)], r.1 + r.2 ≤ slot wp 8 := by
    have := slot_le (w := wp) (show Public.aN < 8 by decide)
    have := slot_le (w := wp) (show Public.aOne < 8 by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [sMaskX, sMinv, sFn] <;> omega
  have ho64 : op < 2 ^ 64 := by omega
  have hb₅ : ∀ d, d + 8 ≤ op → word s₅.mem B d = word s₄.mem B d := fun d hd =>
    f₅.word_below hpr (by omega) ho64 hd
  have hq₅ : ∀ d, oq ≤ d → d + 8 ≤ 2 ^ 64 → word s₅.mem B d = word s₄.mem B d := fun d hd hd' =>
    (f₅.rebase ho64 fun r hr => by have := hpr r hr; omega).word_eq (fun r hr => Or.inr (by
      obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
      have := hpr r₀ hr₀; simp only; omega)) hd'
  have hl₅ : InRegions (s₅.rd ++ s₅.wr) (off (off B op) (8 * sLink)) 8 :=
    hcP₅.good.scr.ld (by unfold sLink sFn; omega)
  have hsQ₅ : word s₅.mem B (8 * sWsQ) = off B oq := by
    rw [hb₅ _ (by unfold sWsQ sFn; omega), hb₄ _ (Or.inr (by unfold sWsQ Public.sMask sFn; omega))
      (by unfold sWsQ sFn; omega)]; exact hsQ₂
  -- Into `q`'s workspace.
  refine wp_seqs_append (by simp) (by simp [primeFix]) ?_
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off B oq ∧ t.mem = s₅.mem)
    (by xrun [leave, enterQ, State.ea, hdr, hcP₅.rdi, hdrOff, hl₅, hcP₅.link,
      hcP₅.scr.ld (d := 8 * sWsQ) (by unfold sWsQ sFn; omega), hsQ₅]) rfl)
    fun s₆ ⟨⟨hdi₆, hm₆⟩, k₆⟩ => ?_
  have hH₆ : Hdr s₆.mem B w minv := by
    rw [hm₆]
    exact ⟨(hb₅ _ (by unfold sW; omega)).trans hH₄.hw, (hb₅ _ (by unfold sMinv; omega)).trans hH₄.hminv,
      fun j hj => (hb₅ _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega); omega)).trans
        (hH₄.harr j hj)⟩
  have hwsQ₆ : WsAt s₆.mem B oq wq mq := by
    rw [hm₆]
    exact hwsQ.of_words fun i hi => by
      rw [word_off, word_off, hq₅ _ (by omega) (by omega), hab₄ _ (by omega) (by omega)]
  have kk6 := (kk4.trans k₅).trans k₆
  have hcQ₆ := SubCtx.mk' (hs.congr kk6.2.2) hH₆ hwsQ₆ hdi₆ (by omega) hoq
  have hM₆ : word s₆.mem B (8 * Public.sMask) = mask (keyMask m0 N P Q QI) := by
    rw [hm₆, hb₅ _ (by unfold Public.sMask sFn; omega)]; exact hM₄
  refine wp_seqs_append (by simp [primeFix]) (by simp) ?_
  refine WP.mono (primeFix_ok hcQ₆ hwq hwq' (by omega) hM₆
    (by rw [hm₆, wv_off, wv_congr fun i hi => hq₅ _ (by omega) (by
        have := slot_le (w := wq) (show Public.aN < 8 by decide); omega),
      wv_congr fun i hi => hab₄ _ (by omega) (by have := slot_le (w := wq) (show Public.aN < 8 by decide); omega),
      ← wv_off]; exact hQ) hoddQ)
    fun s₇ ⟨mq', hcQ₇, hQ₇, hiQ₇, hoQ₇, _, f₇, k₇⟩ => ?_
  have hqr : ∀ r ∈ [(slot wq Public.aN, 8 * (wq + 2)), (slot wq Public.aOne, 8 * (wq + 2)), (8 * sMaskX, 8),
      (8 * sMinv, 8)], r.1 + r.2 ≤ slot wq 8 := by
    have := slot_le (w := wq) (show Public.aN < 8 by decide)
    have := slot_le (w := wq) (show Public.aOne < 8 by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [sMaskX, sMinv, sFn] <;> omega
  have hoq64 : oq < 2 ^ 64 := by omega
  have hb₇ : ∀ d, d + 8 ≤ oq → word s₇.mem B d = word s₆.mem B d := fun d hd =>
    f₇.word_below hqr (by omega) hoq64 hd
  have hl₇ : InRegions (s₇.rd ++ s₇.wr) (off (off B oq) (8 * sLink)) 8 :=
    hcQ₇.good.scr.ld (by unfold sLink sFn; omega)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = s₇.mem)
    (by xrun [leave, State.ea, hdr, hcQ₇.rdi, hdrOff, hl₇, hcQ₇.link]) rfl) fun t ⟨⟨hdi, hm⟩, k'⟩ => ?_
  have kall := (kk6.trans k₇).trans k'
  have hbt : ∀ d, d + 8 ≤ op → word t.mem B d = word s₄.mem B d := fun d hd => by
    rw [hm, hb₇ d (by omega), hm₆, hb₅ d hd]
  have hpt : ∀ d, op ≤ d → d + 8 ≤ oq → word t.mem B d = word s₅.mem B d := fun d hd hd' => by
    rw [hm, hb₇ d hd', hm₆]
  have hpt' : ∀ i < 32, word t.mem (off B op) (8 * i) = word s₅.mem (off B op) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hpt _ (by omega) (by omega)
  have hptv : ∀ d k, d + 8 * k ≤ slot wp 8 → wv t.mem (off B op) d k = wv s₅.mem (off B op) d k := fun d k hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hpt _ (by omega) (by omega)
  refine ⟨⟨hs.congr kall.2.2, hdi, ⟨(hbt _ (by unfold sW; omega)).trans hH₄.hw,
      (hbt _ (by unfold sMinv; omega)).trans hH₄.hminv,
      fun j hj => (hbt _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega); omega)).trans
        (hH₄.harr j hj)⟩⟩,
    by rw [hbt _ (by unfold Public.sMask sFn; omega)]; exact hM₄,
    by rw [hbt _ (by unfold sWsP sFn; omega), hb₄ _ (Or.inr (by unfold sWsP Public.sMask sFn; omega))
      (by unfold sWsP sFn; omega)]; exact hsP₂,
    by rw [hbt _ (by unfold sWsQ sFn; omega), hb₄ _ (Or.inr (by unfold sWsQ Public.sMask sFn; omega))
      (by unfold sWsQ sFn; omega)]; exact hsQ₂,
    ⟨mp', hcP₅.ws.of_words fun i hi => hpt' i (by omega), ⟨?_, ?_, ?_⟩,
      by rw [hpt' _ (by decide)]; exact hmP₅⟩,
    ⟨mq', by rw [hm]; exact hcQ₇.ws, ⟨by rw [hm]; exact hQ₇, by rw [hm]; exact hiQ₇, by rw [hm]; exact hoQ₇⟩⟩,
    ?_, ⟨fun r hr => ?_, kall.2⟩⟩
  · rw [hptv _ _ (by have := slot_le (w := wp) (show Public.aN < 8 by decide); omega)]; exact hP₅
  · rw [word_off, hpt _ (by omega) (by have := slot_le (w := wp) (show Public.aN < 8 by decide); omega), ← word_off]
    exact hiP₅
  · rw [hptv _ _ (by have := slot_le (w := wp) (show Public.aOne < 8 by decide); omega)]; exact hoP₅
  · have mem1 : (slot w Public.aAcc, 8 * (2 * w + 2)) ∈ [(slot w Public.aAcc, 8 * (2 * w + 2)),
        (8 * Public.sMask, 8), (op, slot wp 8), (oq, slot wq 8)] := by simp
    have mem2 : (8 * Public.sMask, 8) ∈ [(slot w Public.aAcc, 8 * (2 * w + 2)),
        (8 * Public.sMask, 8), (op, slot wp 8), (oq, slot wq 8)] := by simp
    have g1 := Frm.of_outside ho₁ mem1
    have g2 := Frm.of_outside ho₂ mem2
    have g4 := Frm.of_outside ho₄ mem2
    have g5 := (f₅.rebase ho64 fun r hr => by have := hpr r hr; omega).widen (rs' := [(slot w Public.aAcc,
        8 * (2 * w + 2)), (8 * Public.sMask, 8), (op, slot wp 8), (oq, slot wq 8)]) fun r hr => by
      obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
      have := hpr r₀ hr₀
      exact ⟨(op, slot wp 8), by simp, by simp only; omega, by simp only; omega⟩
    have g7 := (f₇.rebase hoq64 fun r hr => by have := hqr r hr; omega).widen (rs' := [(slot w Public.aAcc,
        8 * (2 * w + 2)), (8 * Public.sMask, 8), (op, slot wp 8), (oq, slot wq 8)]) fun r hr => by
      obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
      have := hqr r₀ hr₀
      exact ⟨(oq, slot wq 8), by simp, by simp only; omega, by simp only; omega⟩
    rw [hm₃] at g4
    rw [hm₆] at g7
    rw [hm]
    exact (((g1.trans g2).trans g4).trans g5).trans g7
  · by_cases h : r = .rdi
    · subst h; rw [hdi, hg.rdi]
    · exact kall.1 r (by simp only [mmRegs, List.mem_cons, List.mem_append] at hr ⊢; simp_all)

end VG.Proof.Bignum.X86_64
